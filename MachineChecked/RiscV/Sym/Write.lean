import MachineChecked.RiscV.Sym.Core

/-!
# The `WRITE` syscall to a file descriptor other than 13

`t0 = 2` at an `ECALL` with `a0 ≠ 13` (the public-values descriptor) only advances the pc. A
leaf module: `MachineChecked.RiscV.Sym.Sym` does not know this syscall yet (it stops at `ECALL 2`), so the step is
applied as a spec at the `ecall`'s pc (`Proof/Runtime/SyscallWrite.lean`).
-/

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

/-- `WRITE` (`2`) to a descriptor other than 13: the pc advances, nothing else changes. -/
theorem stepSp1_write_other {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = 2#64) (hfd : s.getReg .x10 ≠ 13#64) :
    stepSp1 s = some (s.setPC (s.pc + 4)) := by
  have hhost : Sp1.isHostId (s.getReg .x5) = true := by rw [ht0]; decide
  rw [stepSp1_ecall_host hfetch hhost]
  exact step_ecall_write_other hfetch ht0 hfd

end MachineChecked.RiscV.Sym
