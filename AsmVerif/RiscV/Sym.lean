import AsmVerif.RiscV.Sym.Core
import AsmVerif.RiscV.Sym.Exec
import AsmVerif.RiscV.Sym.Syscall
import AsmVerif.RiscV.Sym.Region
import AsmVerif.RiscV.Sym.Mem
import AsmVerif.RiscV.Sym.Frame
import AsmVerif.RiscV.Sym.Regs
import AsmVerif.RiscV.Sym.Layout
import AsmVerif.RiscV.Sym.Ro
import AsmVerif.RiscV.Sym.ByteFold
import AsmVerif.RiscV.Sym.Write
import AsmVerif.RiscV.Sym.Resume
import AsmVerif.RiscV.Sym.Tactic
import AsmVerif.RiscV.Sym.Close
import AsmVerif.RiscV.Sym.Load

/-!
# The symbolic executor

The whole of `AsmVerif.RiscV.Sym`: the `Safe` continuation-form specifications, the executor
(`sym_exec`, `sym_close`), and the region, frame, register, layout and image vocabulary a
function-level proof is stated in.
-/
