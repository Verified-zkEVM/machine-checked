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

/-- **The normal form of an address**: a base plus one constant (`sp + 0xffffffffffffffd0#64`,
    not `sp - 48#64` or `sp + 0xffffffffffffffe0#64 + 16#64`). In `lsym_simp` too, so that what
    `lsym` computes and a fact about a cell stated otherwise (a region lemma's
    `base + BitVec.ofNat 64 (8 * i)`, normalised by `simp only [lsym_addr] at h`) meet. -/
register_simp_attr lsym_addr
