/-
  MachineChecked.X86.BinOp

  The two definitions the x86 model takes from catcrypt-compiler's VIR layer, at `69ffea9f`
  (MIT, Copyright (c) 2026 CatCrypt Contributors; see `MachineChecked/Ascent/LICENSE-catcrypt`):
  `shiftMask` (`VIR/Core.lean`) and `JasminBinOp` with its `apply` (`VIR/JasminDialect.lean`).
  Copied here so that the model does not pull in the VIR layer, its SIMD file and Mathlib.
-/

namespace MachineChecked.X86

/-- The count an x86 scalar `SHL`/`SHR` of a width-`w` register applies for the
    requested count `k`: `k % 64` at width 64 and `k % 32` at widths up to 32 (the
    count register is masked to six, respectively five, bits), `k % 128` and
    `k % 256` at widths 128 and 256 (Jasmin's `sem_shift` mask), and `k` at every
    other width. -/
def shiftMask (w k : Nat) : Nat :=
  if w = 64 then k % 64 else if w ≤ 32 then k % 32
  else if w = 128 then k % 128 else if w = 256 then k % 256 else k

/-- A count below the width is not changed by the mask. -/
theorem shiftMask_of_lt {w k : Nat} (h : k < w) : shiftMask w k = k := by
  unfold shiftMask
  split <;> (try split) <;> (try split) <;> (try split) <;>
    first | rfl | (apply Nat.mod_eq_of_lt; omega)

/-- The two-address binary operators on registers `regArith` supports.

    `shl`/`shr` are the **logical** left / right shifts:
    they let the dialect express the ARX rotate `(x <<< n) ||| (x >>> (w-n))`
    needed by ChaCha20 and other shift-using ciphers. The shift *amount* is the
    x86 scalar mask `shiftMask w` of the `.toNat` of the second register operand
    in the register operation `JasminBinOp.apply`, and the unmasked `.toNat` in
    the lane operation `JasminBinOp.applyLane` of the packed SIMD denotations.
    Width truncation is handled by `BitVec`'s `<<<` / `>>>` (logical, keeps the
    operand width). -/
inductive JasminBinOp where
  | add
  | sub
  | mul
  | and
  | or
  | xor
  /-- Logical left shift by the masked count `shiftMask w b.toNat`. -/
  | shl
  /-- Logical right shift by the masked count `shiftMask w b.toNat`. -/
  | shr
  /-- BMI1 `andn`: `(¬a) ∧ b` in ONE op (no separate `NOT`). This is the
      first source complemented and AND-ed with the second, matching the
      x86 `ANDN dst, a, b` ⇒ `dst := (~a) & b`. It collapses the Keccak χ
      idiom `B[x] ^ ((¬B[x+1]) ∧ B[x+2])` from a `NOT;AND` pair to a single
      instruction. Denotation: `(~~~a) &&& b`. -/
  | andn
  deriving DecidableEq, Repr

/-- Apply a `JasminBinOp` to two registers of width `w`. The `shl`/`shr` arms are
    the logical shifts by the count `shiftMask w b.toNat` of x86 scalar shifts. -/
def JasminBinOp.apply : JasminBinOp → {w : Nat} → BitVec w → BitVec w → BitVec w
  | .add, _, a, b => a + b
  | .sub, _, a, b => a - b
  | .mul, _, a, b => a * b
  | .and, _, a, b => a &&& b
  | .or,  _, a, b => a ||| b
  | .xor, _, a, b => a ^^^ b
  | .shl, w, a, b => a <<< shiftMask w b.toNat
  | .shr, w, a, b => a >>> shiftMask w b.toNat
  | .andn, _, a, b => (~~~a) &&& b

end MachineChecked.X86
