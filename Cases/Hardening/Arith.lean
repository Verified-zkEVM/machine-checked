import Cases.Hardening.Gen.Arith
import LprogRiscV.Lsym

/-!
  # Arithmetic at its edges

  Each function against what C says it computes, by `bv_decide` once `lsym` has stepped it:
  division and remainder by zero and at the one overflow, the high half of products, signed
  and not, a rotation, an absolute value without a branch. What is checked is the lift's
  meaning of `div`, `rem`, `divu`, `mulh`, `mulhu`, `sll`, `srl` and `sra`, against C's.
-/

namespace Cases.Hardening.Arith

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift
open Cases.Hardening.Gen.Arith

/-- A function at index `i` returns `f a0 a1` in `a0`. -/
def Returns (i : Nat) (f : Word → Word → Word) : Prop :=
  ∀ {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    (regs : Reg → BitVec 64) (m : MachineState), regs .x1 = ret → regs .x2 = top →
    (∀ r' m', r' .x10 = f (regs .x10) (regs .x11) → LSafeN fns G N Q ⟨rest, r', m'⟩) →
    LSafeN fns G N Q ⟨⟨i, 0, ret, top⟩ :: rest, regs, m⟩

/-- `sdiv(a, b)`: `b == 0 ? 0 : a / b`, C's division, which rounds toward zero; the overflow
    `INT64_MIN / -1` (undefined in C) gives `INT64_MIN`, as RISC-V's `div` does. -/
theorem sdiv_spec : Returns 0 fun a b => if b = 0 then 0 else a.sdiv b := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f0_eq with [hra, hsp]
  all_goals (apply hpost; simp only [lsym_simp] at *; bv_decide)

/-- `srem(a, b)`: `b == 0 ? a : a % b`, the remainder with the sign of the dividend. -/
theorem srem_spec : Returns 1 fun a b => if b = 0 then a else a.srem b := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f1_eq with [hra, hsp]
  all_goals (apply hpost; simp only [lsym_simp] at *; bv_decide)

/-- `udiv(a, b)`: `b == 0 ? 0 : a / b`, unsigned. -/
theorem udiv_spec : Returns 2 fun a b => if b = 0 then 0 else a / b := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f2_eq with [hra, hsp]
  all_goals (apply hpost; simp only [lsym_simp] at *; bv_decide)

/-- `mulhi(a, b)`: the high half of the unsigned 128-bit product. -/
theorem mulhi_spec : Returns 3 fun a b =>
    ((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).truncate 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f3_eq with [hra, hsp]
  -- the product is too wide for `bv_decide`: it is the same product, its factors swapped
  apply hpost; simp only [lsym_simp]; rw [BitVec.mul_comm]

/-- `smulhi(a, b)`: the high half of the signed 128-bit product. -/
theorem smulhi_spec : Returns 4 fun a b =>
    ((a.signExtend 128 * b.signExtend 128).sshiftRight 64).truncate 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f4_eq with [hra, hsp]
  -- the lift shifts the product logically, C arithmetically: the low 64 bits after a shift
  -- by 64 are the same
  apply hpost; simp only [lsym_simp]; rw [BitVec.mul_comm]
  generalize BitVec.signExtend 128 (regs .x10) * BitVec.signExtend 128 (regs .x11) = p
  bv_decide

/-- `rotl(x, s)`: `(x << (s & 63)) | (x >> (-s & 63))`, as C states it, with the shift amounts
    as words. -/
theorem rotl_spec : Returns 5 fun x s => x <<< (s &&& 63#64) ||| x >>> ((0 - s) &&& 63#64) := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f5_eq with [hra, hsp]
  apply hpost; simp only [lsym_simp]
  simp [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_and, BitVec.toNat_neg]

/-- `abs_branchless(x)`: `|x|`, with `|INT64_MIN| = INT64_MIN`. -/
theorem abs_spec : Returns 7 fun x _ => if x.slt 0 then -x else x := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f7_eq with [hra, hsp]
  all_goals (apply hpost; simp only [lsym_simp] at *; bv_decide)

end Cases.Hardening.Arith
