/-
  MachineChecked.RiscV.Accept

  The observation every judgement in this framework is stated against: SP1's accepting halt.
  `Accepted s` says the machine is at an `ECALL` with `t0 = 0` (`HALT`) and exit code
  `a0 = 0`, which is what the verifier of an SP1 proof checks. An accepting state is stuck
  (`Accepted.stuck`), so a state that steps is never accepting.
-/

import RiscvZkvm.Rv64
import RiscvZkvm.Rv64.StepOn
import RiscvZkvm.Interpreter

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64

/-- SP1's accepting halt: `ecall` with `t0 = 0` (HALT) and exit code `a0 = 0`. -/
def Accepted (s : MachineState) : Prop :=
  s.code s.pc = some .ECALL ∧ s.getReg .x5 = 0 ∧ s.getReg .x10 = 0

theorem stepSp1_halt {s : MachineState} (h : s.code s.pc = some .ECALL) (h5 : s.getReg .x5 = 0) :
    stepSp1 s = none := by
  have hacc : Sp1.isAccelId 0#64 = false := by decide
  have hhost : Sp1.isHostId 0#64 = true := by decide
  simp [stepSp1, h, sp1Ecall, h5, hacc, hhost, step, Sp1.HINT_LEN, Sp1.HINT_READ,
    Sp1.COMMIT, Sp1.COMMIT_DEFERRED_PROOFS]

theorem Accepted.stuck {s : MachineState} (h : Accepted s) : stepSp1 s = none :=
  stepSp1_halt h.1 h.2.1

theorem not_accepted_of_code {s : MachineState} {i : Instr} (h : s.code s.pc = some i)
    (hi : i ≠ .ECALL) : ¬ Accepted s := by
  intro ha; have h1 := ha.1; rw [h] at h1; exact hi (Option.some.inj h1)

end MachineChecked.RiscV
