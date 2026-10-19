/-
  Cases.Zip2005.Frame.Fns

  The case functions as `Fn`s: code from the image modules, plus the outlined fragment
  `default_hook` calls, and the indirect-jump targets `core::fmt::write` is checked against.
-/

import MachineChecked.RiscV.Frame.Domain
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.F_78021720
import Cases.Zip2005.Image.F_7803b6ac
import Cases.Zip2005.Image.F_7803c304
import Cases.Zip2005.Image.F_7803e6b4

namespace Cases.Zip2005.Frame.Fns

open MachineChecked.RiscV.Frame Cases.Zip2005.Image

/-- `memcpy`: a leaf with a jump table. -/
def memcpy : Fn := { base := F_7801b4d8.base, prog := F_7801b4d8.prog }

/-- sinsemilla `Pad::next`: spills `ra`, uses it as a scratch register, stores through `self`. -/
def padNext : Fn := { base := F_78021720.base, prog := F_78021720.prog }

/-- `std::panicking::default_hook`: outlined prologue (`OUTLINED_FUNCTION_0` at `0x7803c304`). -/
def defaultHook : Fn :=
  { base := F_7803b6ac.base, prog := F_7803b6ac.prog,
    frags := [(F_7803c304.base, F_7803c304.prog)] }

/-- `core::fmt::write`: ends in a tail call through a vtable (`jalr zero, 0(t1)` at
    `0x7803e914`), checked on the premise that it leaves the function (`jumps := some []`). -/
def fmtWrite : Fn := { base := F_7803e6b4.base, prog := F_7803e6b4.prog, jumps := some [] }

end Cases.Zip2005.Frame.Fns
