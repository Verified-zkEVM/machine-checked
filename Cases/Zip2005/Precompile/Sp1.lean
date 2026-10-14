/-
  Cases.Zip2005.Precompile.Sp1 -- the three precompiles as the machine model dispatches them.

  `MachineState.sp1AccelWrite` / `sp1AccelValid` (`riscv-zkvm`,
  `Rv64/Sp1Accel.lean`) are sixteen-way `if` chains. This file cuts out the three
  arms the guest uses, states each arm's **trap condition** exactly (as an `↔`,
  so nothing is lost), and composes them with the mathematics:

  * `UINT256_MUL`: the four limbs written at `a0` decode to `(X * Y) % M`;
  * `PALLAS_ADD`:  the eight limbs written at `a0` are the point `P + Q`;
  * `PALLAS_DOUBLE`: the eight limbs written at `a0` are the point `2 • P`.

  The curve theorems carry an on-curve hypothesis the model does not check --
  the *guest* must establish it (it holds for canonical encodings of group
  elements, which is what `pasta_curves`' `sp1_pallas.rs` passes).
-/

import Cases.Zip2005.Precompile.Pallas

namespace Cases.Zip2005.Precompile

open RiscvZkvm.Rv64 Pallas

/-- `readWords` reads exactly `n` doublewords. -/
@[simp] theorem length_readWords (s : MachineState) (base : Word) (n : Nat) :
    (s.readWords base n).length = n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp [MachineState.readWords, ih]

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

/-- The model's `UINT256_MUL` arm: result block at `a0`, operands `x` at `a0`,
    `y` at `a1`, modulus at `a1 + 32`. -/
theorem sp1AccelWrite_uint256Mul (s : MachineState) :
    s.sp1AccelWrite Sp1.UINT256_MUL =
      (s.getReg .x10, Accel.natToLeLimbs 4 (Accel.arith256Mod
        (Accel.leLimbsToNat (s.readWords (s.getReg .x10) 4))
        (Accel.leLimbsToNat (s.readWords (s.getReg .x11) 4)) 0
        (Accel.leLimbsToNat (s.readWords (s.getReg .x11 + 32) 4)))) := by
  simp (config := { decide := true }) only [MachineState.sp1AccelWrite, if_true, if_false]

/-- **The `UINT256_MUL` trap condition, exactly.** The model continues iff both
    operand blocks are valid dword ranges (four at `a0`; eight at `a1`, covering
    `y` *and* the modulus) and the modulus is nonzero. Nothing else: `x` and `y`
    may be unreduced. -/
theorem sp1AccelValid_uint256Mul (s : MachineState) :
    s.sp1AccelValid Sp1.UINT256_MUL = true ↔
      MachineState.validDwordRange (s.getReg .x10) 4 = true ∧
      MachineState.validDwordRange (s.getReg .x11) 8 = true ∧
      Accel.leLimbsToNat (s.readWords (s.getReg .x11 + 32) 4) ≠ 0 := by
  simp (config := { decide := true }) only [MachineState.sp1AccelValid, if_true, if_false]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, and_assoc, ne_eq]

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

theorem sp1AccelWrite_pallasAdd (s : MachineState) :
    s.sp1AccelWrite Sp1.PALLAS_ADD =
      (s.getReg .x10, Accel.curveAddL Sp1.pallasP 4 (s.readWords (s.getReg .x10) 8)
        (s.readWords (s.getReg .x11) 8)) := by
  simp (config := { decide := true }) only [MachineState.sp1AccelWrite, if_true, if_false]

/-- **The `PALLAS_ADD` trap condition, exactly.** Valid dword ranges at `a0` and
    `a1`, all four coordinates reduced, and `x₁ ≠ x₂` as integers. On-curve is
    *not* part of it. -/
theorem sp1AccelValid_pallasAdd (s : MachineState) :
    s.sp1AccelValid Sp1.PALLAS_ADD = true ↔
      MachineState.validDwordRange (s.getReg .x10) 8 = true ∧
      MachineState.validDwordRange (s.getReg .x11) 8 = true ∧
      Accel.ptValid Sp1.pallasP 4 (s.readWords (s.getReg .x10) 8) = true ∧
      Accel.ptValid Sp1.pallasP 4 (s.readWords (s.getReg .x11) 8) = true ∧
      xOf (s.readWords (s.getReg .x10) 8) ≠ xOf (s.readWords (s.getReg .x11) 8) := by
  simp (config := { decide := true }) only [MachineState.sp1AccelValid, if_true, if_false]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, and_assoc, xOf, ne_eq]

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

theorem sp1AccelWrite_pallasDouble (s : MachineState) :
    s.sp1AccelWrite Sp1.PALLAS_DOUBLE =
      (s.getReg .x10, Accel.curveDblL Sp1.pallasP 4 (s.readWords (s.getReg .x10) 8)) := by
  simp (config := { decide := true }) only [MachineState.sp1AccelWrite, if_true, if_false]

/-- **The `PALLAS_DOUBLE` trap condition, exactly.** A valid dword range at `a0`,
    both coordinates reduced, and `y ≠ 0`. `a1` is ignored. -/
theorem sp1AccelValid_pallasDouble (s : MachineState) :
    s.sp1AccelValid Sp1.PALLAS_DOUBLE = true ↔
      MachineState.validDwordRange (s.getReg .x10) 8 = true ∧
      Accel.ptValid Sp1.pallasP 4 (s.readWords (s.getReg .x10) 8) = true ∧
      yOf (s.readWords (s.getReg .x10) 8) ≠ 0 := by
  simp (config := { decide := true }) only [MachineState.sp1AccelValid, if_true, if_false]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, and_assoc, yOf, ne_eq]

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
