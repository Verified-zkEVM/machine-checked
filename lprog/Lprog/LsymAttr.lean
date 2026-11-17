/-
  Lprog.LsymAttr

  The simp set `lsym_simp` (`Lprog/Tactic.lean`) normalises states and side conditions with: Lprog's
  evaluation (tagged in `Lprog.Tactic`), and each instruction set's own definitions, which it
  tags in its package (`LprogRiscV.Lsym` for RISC-V). A simp attribute is used only after the
  module that declares it, so it is declared here.
-/

import Lean

/-- The lemmas `lsym` simplifies with (named apart from the tactic, whose name is a keyword). -/
register_simp_attr lsym_simp
