/-
  MachineChecked.RiscV.Accel

  The three SP1 accelerator arms ZIP 2005's guest uses, as riscv-zkvm dispatches them.

  `MachineState.sp1AccelWrite` / `sp1AccelValid` (`riscv-zkvm`, `Rv64/Sp1Accel.lean`) are
  sixteen-way `if` chains. This file cuts out the `UINT256_MUL`, `PALLAS_ADD` and
  `PALLAS_DOUBLE` arms and states each arm's write and its trap condition exactly (as an
  `↔`, so nothing is lost). What the arms compute (the residue, the Pallas group law) is a
  case's mathematics, not the machine's: ZIP 2005 proves it in `Cases/Zip2005/Precompile`.

  ## Main definitions

  * `Wire.xOf`, `Wire.yOf`: the coordinates of a four-limb-per-coordinate `x || y` point

  ## Main results

  * `sp1AccelWrite_uint256Mul`, `sp1AccelWrite_pallasAdd`, `sp1AccelWrite_pallasDouble`
  * `sp1AccelValid_uint256Mul`, `sp1AccelValid_pallasAdd`, `sp1AccelValid_pallasDouble`
-/

import RiscvZkvm.Rv64

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64

namespace Wire

/-- The `x` coordinate of a four-limb-per-coordinate `x || y` point. -/
def xOf (pt : List Word) : Nat := Accel.leLimbsToNat (pt.take 4)
/-- The `y` coordinate of a four-limb-per-coordinate `x || y` point. -/
def yOf (pt : List Word) : Nat := Accel.leLimbsToNat (pt.drop 4)

end Wire

open Wire

/-- `readWords` reads exactly `n` doublewords. -/
@[simp] theorem length_readWords (s : MachineState) (base : Word) (n : Nat) :
    (s.readWords base n).length = n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp [MachineState.readWords, ih]

/-! ### `UINT256_MUL` -/

/-- The model's `UINT256_MUL` arm: result block at `a0`, operands `x` at `a0`,
    `y` at `a1`, modulus at `a1 + 32`. -/
theorem sp1AccelWrite_uint256Mul (s : MachineState) :
    s.sp1AccelWrite Sp1.UINT256_MUL =
      (s.getReg .x10, Accel.natToLeLimbs 4 (Accel.arith256Mod
        (Accel.leLimbsToNat (s.readWords (s.getReg .x10) 4))
        (Accel.leLimbsToNat (s.readWords (s.getReg .x11) 4)) 0
        (Accel.leLimbsToNat (s.readWords (s.getReg .x11 + 32) 4)))) := by
  simp (config := { decide := true }) only [MachineState.sp1AccelWrite, ite_true, ite_false]

/-- **The `UINT256_MUL` trap condition, exactly.** The model continues iff both
    operand blocks are valid dword ranges (four at `a0`; eight at `a1`, covering
    `y` *and* the modulus) and the modulus is nonzero. Nothing else: `x` and `y`
    may be unreduced. -/
theorem sp1AccelValid_uint256Mul (s : MachineState) :
    s.sp1AccelValid Sp1.UINT256_MUL = true ↔
      MachineState.validDwordRange (s.getReg .x10) 4 = true ∧
      MachineState.validDwordRange (s.getReg .x11) 8 = true ∧
      Accel.leLimbsToNat (s.readWords (s.getReg .x11 + 32) 4) ≠ 0 := by
  simp (config := { decide := true }) only [MachineState.sp1AccelValid, ite_true, ite_false]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, and_assoc, ne_eq]

/-! ### `PALLAS_ADD` -/

theorem sp1AccelWrite_pallasAdd (s : MachineState) :
    s.sp1AccelWrite Sp1.PALLAS_ADD =
      (s.getReg .x10, Accel.curveAddL Sp1.pallasP 4 (s.readWords (s.getReg .x10) 8)
        (s.readWords (s.getReg .x11) 8)) := by
  simp (config := { decide := true }) only [MachineState.sp1AccelWrite, ite_true, ite_false]

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
  simp (config := { decide := true }) only [MachineState.sp1AccelValid, ite_true, ite_false]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, and_assoc, xOf, ne_eq]

/-! ### `PALLAS_DOUBLE` -/

theorem sp1AccelWrite_pallasDouble (s : MachineState) :
    s.sp1AccelWrite Sp1.PALLAS_DOUBLE =
      (s.getReg .x10, Accel.curveDblL Sp1.pallasP 4 (s.readWords (s.getReg .x10) 8)) := by
  simp (config := { decide := true }) only [MachineState.sp1AccelWrite, ite_true, ite_false]

/-- **The `PALLAS_DOUBLE` trap condition, exactly.** A valid dword range at `a0`,
    both coordinates reduced, and `y ≠ 0`. `a1` is ignored. -/
theorem sp1AccelValid_pallasDouble (s : MachineState) :
    s.sp1AccelValid Sp1.PALLAS_DOUBLE = true ↔
      MachineState.validDwordRange (s.getReg .x10) 8 = true ∧
      Accel.ptValid Sp1.pallasP 4 (s.readWords (s.getReg .x10) 8) = true ∧
      yOf (s.readWords (s.getReg .x10) 8) ≠ 0 := by
  simp (config := { decide := true }) only [MachineState.sp1AccelValid, ite_true, ite_false]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, and_assoc, yOf, ne_eq]

end MachineChecked.RiscV
