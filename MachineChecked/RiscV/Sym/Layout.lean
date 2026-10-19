/-
  MachineChecked.RiscV.Sym.Layout

  What the symbolic executor needs to know about where a guest's image sits: the code
  window `[textLo, textHi)` the code map is confined to, the read-only segment
  `[roBase, roBase + roBytes)` as chunks of at most 64 doublewords, and the top of the
  stack. A case defines one `Layout` (generated from its image) and every specification
  names it; the executor reads the constants off that one definition, so nothing about a
  particular guest is built into the framework.

  The numeric side conditions the executor's lemmas need are fields, proved once per case
  (by `decide`), so a lemma takes `L.ro_fits` rather than re-deciding a literal fact.
-/

import RiscvZkvm.Rv64

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

/-- The doublewords per read-only chunk. -/
def roChunkCells : Nat := 64

structure Layout where
  /-- The code window: every loaded instruction lies in `[textLo, textHi)`. -/
  textLo : Nat
  textHi : Nat
  /-- The read-only segment. -/
  roBase : Nat
  roBytes : Nat
  /-- Its contents, as chunks of `roChunkCells` doublewords (the last may be shorter). -/
  roChunks : Nat
  roChunk : Nat → List Word
  /-- The top of the stack: `sp` never exceeds it. -/
  stackTop : Nat
  /-- Every chunk lies inside the segment. -/
  ro_fits : ∀ k, k < roChunks → 8 * roChunkCells * k + 8 * (roChunk k).length ≤ roBytes
  ro_aligned : roBase % 8 = 0
  ro_inMem : roBase + roBytes ≤ SP1_MAX_MEMORY
  /-- The read-only segment lies below the code. -/
  ro_text : roBase + roBytes ≤ textLo
  text_le : textLo ≤ textHi
  text_inMem : textHi ≤ SP1_MAX_MEMORY
  /-- The stack lies below the code. -/
  stack_text : stackTop ≤ textLo

namespace Layout

variable (L : Layout)

theorem ro_nowrap : L.roBase + L.roBytes < 2 ^ 64 :=
  Nat.lt_of_le_of_lt L.ro_inMem (by decide)

theorem stack_inMem : L.stackTop ≤ SP1_MAX_MEMORY :=
  Nat.le_trans L.stack_text (Nat.le_trans L.text_le L.text_inMem)

theorem roChunk_fits (k : Nat) (hk : k < L.roChunks) :
    512 * k + 8 * (L.roChunk k).length ≤ L.roBytes := by
  have := L.ro_fits k hk
  simp only [roChunkCells] at this
  omega

end Layout

end MachineChecked.RiscV.Sym
