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

/-! ## A call through a specification -/

/-- `g`: `a0 = 5`, at `0x2000`. -/
def G' : Fn := ⟨"g", 0x2000, [.ADDI .x10 .x0 5, .JALR .x0 .x1 0], 0⟩

/-- `f`: saves `ra` in `s1`, calls `g`, adds one to its result and returns, at `0x1000`:
    `addi s1, ra, 0; jal ra, g; addi a0, a0, 1; addi ra, s1, 0; ret`. -/
def F' : Fn :=
  ⟨"f", 0x1000, [.ADDI .x9 .x1 0, .JAL .x1 0xffc, .ADDI .x10 .x10 1, .ADDI .x1 .x9 0, .JALR .x0 .x1 0], 0⟩

def fs' : List Fn := [F', G']

theorem hf0 : (liftProg fs')[0]? = some (liftFn fs' F') := rfl
theorem hf1 : (liftProg fs')[1]? = some (liftFn fs' G') := rfl

/-- `g`'s contract: `a0` is 5, and every other register is kept. -/
theorem g_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = 5 → (∀ r, r ≠ .x10 → r' r = regs r) → LSafeN fs' G N Q ⟨rest, r', m'⟩) :
    LSafeN fs' G N Q ⟨⟨1, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym hf1 with [hra, hsp]
  apply hpost
  · simp [lsym_simp]
  · intro r h; simp [lsym_simp, h]

/-- `f`'s contract, through `g`'s: `a0` is 6. -/
theorem f_spec' {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = 6 → LSafeN fs' G N Q ⟨rest, r', m'⟩) :
    LSafeN fs' G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym hf0 with [hra, hsp] using [g_spec]
  apply hpost; simp [lsym_simp, hret]

/-! ## A call through a contract over the register file (`Isa.Contract`) -/

/-- `g`'s contract as an `Isa.Contract`: from `ra = ret` and `sp = top`, it returns with `a0`
    5 and every other register kept. -/
theorem g_contract : rvIsa.Contract (liftProg fs') sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = 5 ∧ ∀ r, r ≠ .x10 → r' r = regs r) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym hf1 with [hra, hsp]
  apply hk
  exact ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h]⟩

/-- `f`'s contract, through `g`'s contract: the call is stepped with no rule by hand. -/
theorem f_contract : rvIsa.Contract (liftProg fs') sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ _ _ r' _ => r' .x10 = 6) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym hf0 with [hra, hsp] using [g_contract]
  apply hk; simp [lsym_simp, hret.1]

end Tools.Test.Lsym
