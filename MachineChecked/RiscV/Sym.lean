import MachineChecked.RiscV.Sym.Core
import MachineChecked.RiscV.Sym.Exec
import MachineChecked.RiscV.Sym.Syscall
import MachineChecked.RiscV.Sym.Region
import MachineChecked.RiscV.Sym.Mem
import MachineChecked.RiscV.Sym.Frame
import MachineChecked.RiscV.Sym.Regs
import MachineChecked.RiscV.Sym.Layout
import MachineChecked.RiscV.Sym.Ro
import MachineChecked.RiscV.Sym.ByteFold
import MachineChecked.RiscV.Sym.Write
import MachineChecked.RiscV.Sym.Resume
import MachineChecked.RiscV.Sym.Tactic
import MachineChecked.RiscV.Sym.Close
import MachineChecked.RiscV.Sym.Load

/-!
# The symbolic executor

The whole of `MachineChecked.RiscV.Sym`: the `Safe` continuation-form specifications, the executor
(`sym_exec`, `sym_close`), and the region, frame, register, layout and image vocabulary a
function-level proof is stated in.
-/
