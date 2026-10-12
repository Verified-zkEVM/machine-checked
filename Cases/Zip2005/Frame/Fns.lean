/-
  Cases.Zip2005.Frame.Fns

  The three spike functions as `Fn`s: code from the image modules, plus the outlined
  fragment `default_hook` calls.
-/

import AsmVerif.RiscV.Frame.Domain
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.F_78021720
import Cases.Zip2005.Image.F_7803b6ac
import Cases.Zip2005.Image.F_7803c304

namespace Cases.Zip2005.Frame.Fns

open AsmVerif.RiscV.Frame Cases.Zip2005.Image

/-- `memcpy`: a leaf with a jump table. -/
def memcpy : Fn := { base := F_7801b4d8.base, prog := F_7801b4d8.prog }

/-- sinsemilla `Pad::next`: spills `ra`, uses it as a scratch register, stores through `self`. -/
def padNext : Fn := { base := F_78021720.base, prog := F_78021720.prog }

/-- `std::panicking::default_hook`: outlined prologue (`OUTLINED_FUNCTION_0` at `0x7803c304`). -/
def defaultHook : Fn :=
  { base := F_7803b6ac.base, prog := F_7803b6ac.prog,
    frags := [(F_7803c304.base, F_7803c304.prog)] }

end Cases.Zip2005.Frame.Fns
