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

attribute [lsym_simp] rvIsa rv opnd se12 sh addr opOf rvMem alignedFor signExtend12

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
