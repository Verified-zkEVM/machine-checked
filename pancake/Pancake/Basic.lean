/-
  Pancake.Basic

  Pancake as the decompiler writes it: a program is a list of Flapjack's declarations over
  64-bit words (Flapjack's syntax, `Flapjack.Pancake.PanLang`).

  Running a program is Flapjack's interpreter (`Flapjack.evalPanValueProgram`, from the
  function `main` with no arguments), but Flapjack's semantics does not build on this
  repository's Lean version (v4.36) at the commit it pins: that commit ports the syntax only.
  Until Flapjack's semantics builds here, this package has the syntax and the conventions
  (`Pancake.Env`), and no semantics; `docs/design/Packages.md` step 4.

  ## Main definitions

  * `W`, `Program`
-/

import Flapjack.Pancake.PanLang

namespace Pancake

/-- The word of the programs the decompiler writes. -/
abbrev W := BitVec 64

/-- **A Pancake program**: its declarations, as `decompile --to pancake` writes them (and
    `decompile --to lean --pancake` as terms). -/
abbrev Program := List (Flapjack.Decl W)

end Pancake
