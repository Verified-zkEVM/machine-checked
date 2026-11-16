/-
  LprogRiscV.Sp1Ctx

  SP1's execution context at Lprog.

  `sp1Ctx` lets an `Lext` take any outcome riscv-zkvm's `ecall` (`sp1Ecall`) gives from a
  machine state the Lprog state stands for, and accepts at `HALT` with exit code `0`. A proof
  about a decompiled SP1 guest at Lprog needs it and RISC-V's registers (`Instance.lean`), not
  the lift, so it is here, in the package `lprog-riscv`, and not in the root's `RiscV/Lift/Lift.lean`.

  ## Main definitions

  * `sp1Ctx`
-/

import LprogRiscV.Instance
namespace Lprog.RiscV

open RiscvZkvm.Rv64 Lprog Lprog.RiscV.Machine
open Lprog.Ascent (Outcome)

/-- **SP1's execution context.** An external call may end in any outcome riscv-zkvm's
    `ecall` gives from a machine state at an `ecall` that agrees with the Lprog state; it
    accepts at `HALT` (`t0 = 0`) with exit code `0`. It makes no events yet. -/
def sp1Ctx : Context rvIsa Unit where
  ext _ regs m o := ∃ u, Agree (ofParts regs m) u ∧ u.code u.pc = some .ECALL ∧
    match sp1Ecall u with
    | some t => o = .ok ((regsOf t, t), [])
    | none => o = .trap
  accept _ regs m := (ofParts regs m).getReg .x5 = 0 ∧ (ofParts regs m).getReg .x10 = 0

theorem sp1Ctx_ext_ne_wrong {n : Nat} {regs : Reg → BitVec 64} {m : MachineState} :
    ¬ sp1Ctx.ext n regs m .wrong := by
  rintro ⟨u, -, -, h⟩
  split at h <;> cases h

end Lprog.RiscV
