/-
  Cases.Zip2005.Precompile.Sp1 -- the three precompiles as the machine model dispatches them.

  The framework cuts the three arms the guest uses out of riscv-zkvm's
  `sp1AccelWrite` / `sp1AccelValid`, with each arm's **trap condition** exactly
  (`MachineChecked/RiscV/Accel.lean`). This file composes them with the mathematics:

  * `UINT256_MUL`: the four limbs written at `a0` decode to `(X * Y) % M`;
  * `PALLAS_ADD`:  the eight limbs written at `a0` are the point `P + Q`;
  * `PALLAS_DOUBLE`: the eight limbs written at `a0` are the point `2 • P`.

  The curve theorems carry an on-curve hypothesis the model does not check --
  the *guest* must establish it (it holds for canonical encodings of group
  elements, which is what `pasta_curves`' `sp1_pallas.rs` passes).
-/

import Cases.Zip2005.Precompile.Pallas
import MachineChecked.RiscV.Accel

namespace Cases.Zip2005.Precompile

open RiscvZkvm.Rv64 Pallas MachineChecked.RiscV MachineChecked.RiscV.Wire

/-! ### `UINT256_MUL` -/

/-- **`UINT256_MUL` computes `(X * Y) % M`.** For limb lists `x`, `y` and a
    modulus `m` of at most four limbs, `M ≠ 0` -- exactly the model's trap
    condition -- the four limbs the model writes decode to `(X * Y) % M`, which
    is below `M`. `X` and `Y` need not be reduced. -/
theorem uint256Mul_spec (x y m : List Word) (hm4 : m.length ≤ 4)
    (hm : Accel.leLimbsToNat m ≠ 0) :
    let out := Accel.natToLeLimbs 4
      (Accel.arith256Mod (Accel.leLimbsToNat x) (Accel.leLimbsToNat y) 0 (Accel.leLimbsToNat m))
    out.length = 4 ∧
      Accel.leLimbsToNat out = Accel.leLimbsToNat x * Accel.leLimbsToNat y % Accel.leLimbsToNat m ∧
      Accel.leLimbsToNat out < Accel.leLimbsToNat m := by
  have hM : Accel.leLimbsToNat m < 2 ^ 256 :=
    Nat.lt_of_lt_of_le (leLimbsToNat_lt m) (Nat.pow_le_pow_right (by omega) (by omega))
  have hlt : Accel.leLimbsToNat x * Accel.leLimbsToNat y % Accel.leLimbsToNat m <
      Accel.leLimbsToNat m := Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
  simp only [Accel.arith256Mod, Nat.add_zero]
  rw [leLimbsToNat_natToLeLimbs_four (by omega)]
  exact ⟨length_natToLeLimbs _ _, rfl, hlt⟩

/-- **`UINT256_MUL` at machine level.** Whenever the model does not trap, it
    writes at `a0` four limbs decoding to `(X * Y) % M`, where `X` is read from
    `a0`, `Y` from `a1` and `M` from `a1 + 32`. -/
theorem uint256Mul_machine (s : MachineState) (hv : s.sp1AccelValid Sp1.UINT256_MUL = true) :
    let X := Accel.leLimbsToNat (s.readWords (s.getReg .x10) 4)
    let Y := Accel.leLimbsToNat (s.readWords (s.getReg .x11) 4)
    let M := Accel.leLimbsToNat (s.readWords (s.getReg .x11 + 32) 4)
    (s.sp1AccelWrite Sp1.UINT256_MUL).1 = s.getReg .x10 ∧
      (s.sp1AccelWrite Sp1.UINT256_MUL).2.length = 4 ∧
      Accel.leLimbsToNat (s.sp1AccelWrite Sp1.UINT256_MUL).2 = X * Y % M ∧
      M ≠ 0 := by
  obtain ⟨-, -, hm⟩ := (sp1AccelValid_uint256Mul s).mp hv
  obtain ⟨hlen, hval, -⟩ := uint256Mul_spec (s.readWords (s.getReg .x10) 4)
    (s.readWords (s.getReg .x11) 4) (s.readWords (s.getReg .x11 + 32) 4) (by simp) hm
  rw [sp1AccelWrite_uint256Mul]
  exact ⟨rfl, hlen, hval, hm⟩

/-! ### `PALLAS_ADD` -/

/-- **`PALLAS_ADD` at machine level.** Whenever the model does not trap and both
    operands are on the curve, it writes at `a0` eight limbs encoding a reduced,
    on-curve point equal to `P + Q` in the group law. -/
theorem pallasAdd_machine (s : MachineState) (hv : s.sp1AccelValid Sp1.PALLAS_ADD = true)
    (h1 : OnCurve (xOf (s.readWords (s.getReg .x10) 8)) (yOf (s.readWords (s.getReg .x10) 8)))
    (h2 : OnCurve (xOf (s.readWords (s.getReg .x11) 8)) (yOf (s.readWords (s.getReg .x11) 8))) :
    let P := s.readWords (s.getReg .x10) 8
    let Q := s.readWords (s.getReg .x11) 8
    let out := (s.sp1AccelWrite Sp1.PALLAS_ADD).2
    (s.sp1AccelWrite Sp1.PALLAS_ADD).1 = s.getReg .x10 ∧
      out.length = 8 ∧ Accel.ptValid Sp1.pallasP 4 out = true ∧ OnCurve (xOf out) (yOf out) ∧
      pointOf (xOf out) (yOf out) = pointOf (xOf P) (yOf P) + pointOf (xOf Q) (yOf Q) := by
  obtain ⟨-, -, hv1, hv2, hne⟩ := (sp1AccelValid_pallasAdd s).mp hv
  rw [sp1AccelWrite_pallasAdd]
  exact ⟨rfl, curveAddL_spec _ _ hv1 hv2 hne h1 h2⟩

/-! ### `PALLAS_DOUBLE` -/

/-- **`PALLAS_DOUBLE` at machine level.** Whenever the model does not trap and
    the operand is on the curve, it writes at `a0` eight limbs encoding a
    reduced, on-curve point equal to `2 • P` in the group law. -/
theorem pallasDouble_machine (s : MachineState) (hv : s.sp1AccelValid Sp1.PALLAS_DOUBLE = true)
    (h1 : OnCurve (xOf (s.readWords (s.getReg .x10) 8)) (yOf (s.readWords (s.getReg .x10) 8))) :
    let P := s.readWords (s.getReg .x10) 8
    let out := (s.sp1AccelWrite Sp1.PALLAS_DOUBLE).2
    (s.sp1AccelWrite Sp1.PALLAS_DOUBLE).1 = s.getReg .x10 ∧
      out.length = 8 ∧ Accel.ptValid Sp1.pallasP 4 out = true ∧ OnCurve (xOf out) (yOf out) ∧
      pointOf (xOf out) (yOf out) = 2 • pointOf (xOf P) (yOf P) := by
  obtain ⟨-, hv1, hy0⟩ := (sp1AccelValid_pallasDouble s).mp hv
  rw [sp1AccelWrite_pallasDouble]
  exact ⟨rfl, curveDblL_spec _ hv1 hy0 h1⟩

end Cases.Zip2005.Precompile
