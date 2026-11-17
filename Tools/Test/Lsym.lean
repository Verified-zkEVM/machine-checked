/-
  Tools.Test.Lsym

  A check of `lsym` (`Lprog/Tactic.lean`), run when the module is built: a small RISC-V function
  (a branch, two paths that set `a0`, a return) proved at Lprog with `lsym` and the postcondition
  alone. `Cases/Zip2005/Runtime/MemcmpLsym.lean` is a larger use, with loads and a loop.
-/

import MachineChecked.RiscV.Lift.Lift
import LprogRiscV.Lsym

namespace Tools.Test.Lsym

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift

/-- `if a1 == 0 { a0 = 7 } else { a0 = 8 }; ret`, at `0x1000`:
    `beq a1, zero, +12; addi a0, zero, 8; jal zero, +8; addi a0, zero, 7; ret`. -/
def F : Fn :=
  ⟨"f", 0x1000, [.BEQ .x11 .x0 12, .ADDI .x10 .x0 8, .JAL .x0 8, .ADDI .x10 .x0 7, .JALR .x0 .x1 0], 0⟩

def fs : List Fn := [F]

theorem hf : (liftProg fs)[0]? = some (liftFn fs F) := rfl

/-- `f` returns with `a0` 7 if `a1` was 0, and 8 otherwise. -/
theorem f_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = (if regs .x11 = 0 then 7 else 8) → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym hf with [hra, hsp]
  all_goals (apply hpost; simp_all [lsym_simp])

end Tools.Test.Lsym
