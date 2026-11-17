/-
  LprogRiscV.Lsym

  RISC-V's definitions in the simp set of `lsym` (`Lprog/Tactic.lean`): the instance, how an
  operand and an immediate are read, the memory, and the translation of an instruction to an
  operation, so that `lsym` computes RISC-V's operations and their side conditions.
-/

import LprogRiscV.Instance
import Lprog.Tactic

namespace Lprog.RiscV

open RiscvZkvm.Rv64 Lprog.RiscV.Machine

attribute [lsym_simp] rvIsa rv opnd se12 sh addr opOf rvMem signExtend12

/-! A memory access's check, in the form the lemmas about regions give it (`dwordOk`): a
  doubleword's as `isValidDwordAccessSp1`, a byte's as validity alone. -/

@[lsym_simp] theorem dword_check (a : Word) :
    (isValidMemAddrSp1 a && alignedFor 8 a) = isValidDwordAccessSp1 a := rfl

@[lsym_simp] theorem dword_check' (a : Word) :
    (isValidMemAddrSp1 a = true ∧ alignedFor 8 a = true) ↔ isValidDwordAccessSp1 a = true := by
  simp [isValidDwordAccessSp1, alignedFor]

/-- A store does not change the code, so not where the code is. -/
@[lsym_simp] theorem noCodeAt_setMem (m : MachineState) (a v b : Word) (w : Nat) :
    noCodeAt (m.setMem a v) b w = noCodeAt m b w := rfl

@[lsym_simp] theorem alignedFor_1 (a : Word) : alignedFor 1 a = true := rfl

/-- **The frame of a postcondition.** Every register outside `S` reads in the machine state
    built from `r'` as in `u0`, if `regs` agrees with `u0` outside `S` and `r'` with `regs`
    (`x0` reads zero in both). The second is what `lframe` proves of the register file `lsym`
    leaves. -/
theorem frame_ofParts {S : List Reg} {regs r' : Reg → BitVec 64} {u0 : MachineState}
    (hkept : ∀ r, r ∉ S → r ≠ .x0 → regs r = u0.getReg r)
    (hw : ∀ r, r ∉ S → r ≠ .x0 → r' r = regs r) (m : MachineState) :
    ∀ r, r ∉ S → (ofParts r' m).getReg r = u0.getReg r := by
  intro r hr
  by_cases h0 : r = .x0
  · subst h0; simp [getReg_x0]
  · rw [getReg_ofParts]; simp [h0, hw r hr h0, hkept r hr h0]

end Lprog.RiscV
