/-
  AsmVerif.RiscV.Sym.Load

  The executor's image facts from a loaded `Image`: what a case states about the state the
  guest starts in, as theorems about `AsmVerif.RiscV.Load`'s reading of the ELF rather than
  as hypotheses.

  * `codeAt_of_image`: a function's decoded program (`decodeWords ws = prog`, kernel-checked
    in the generated module) is `CodeAt` its base in every state with the image's code.
  * `codeWithin_of_image`: the code map is confined to the extent of the code chunks.
  * `roImage_of_image`: the read-only segment, as the chunks of a `Layout` generated from
    the same data chunk, holds in every state with the image's memory.
-/

import AsmVerif.RiscV.Load
import AsmVerif.RiscV.Sym.Ro

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64 AsmVerif.RiscV

/-! ## Code -/

theorem codeAt_of_image {img : Image} (hwf : img.codeWF = true) {k : Nat} {base : Word}
    {ws : List (BitVec 32)} (hk : img.code[k]? = some ⟨base, ws⟩) {prog : List (Option Instr)}
    (hdec : decodeWords ws = prog) {s : MachineState} (hs : s.code = img.codeAt) :
    CodeAt base prog s := by
  intro i hi
  rw [hs]
  subst hdec
  simp only [decodeWords, List.length_map] at hi
  rw [Image.codeAt_chunk (c := ⟨base, ws⟩) hwf hk hi]
  rw [getElem!_pos _ _ (by simpa [decodeWords] using hi)]
  simp [decodeWords]

/-- Outside every code chunk, a well-formed image has no code. -/
theorem Image.codeAt_outside {img : Image} (hwf : img.codeWF = true) {a : Word}
    (h : ∀ c ∈ img.code, a.toNat < c.lo ∨ c.hi ≤ a.toNat) : img.codeAt a = none := by
  simp only [Image.codeWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have : img.code.findSome? (·.word? a) = none := by
    rw [List.findSome?_eq_none_iff]
    intro c hc
    have hhi := hwf.2 c hc
    simp only [CodeChunk.hi] at hhi
    have hout := h c hc
    simp only [CodeChunk.lo, CodeChunk.hi] at hout
    simp only [CodeChunk.word?]
    split
    · apply List.getElem?_eq_none
      rw [BitVec.toNat_sub]
      have ha := a.isLt
      have hb := c.base.isLt
      rcases hout with h1 | h1
      · rw [show 2 ^ 64 - c.base.toNat + a.toNat = (2 ^ 64 - c.base.toNat + a.toNat) % 2 ^ 64 from
          (Nat.mod_eq_of_lt (by omega)).symm]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [show 2 ^ 64 - c.base.toNat + a.toNat = 2 ^ 64 + (a.toNat - c.base.toNat) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        omega
    · rfl
  simp [Image.codeAt, this]

/-- The code map is confined to `[lo, hi)` when every code chunk is. -/
theorem codeWithin_of_image {img : Image} (hwf : img.codeWF = true) {lo hi : Nat}
    (hlo : ∀ c ∈ img.code, lo ≤ c.lo) (hhi : ∀ c ∈ img.code, c.hi ≤ hi) {s : MachineState}
    (hs : s.code = img.codeAt) : CodeWithin lo hi s := by
  intro a ha
  rw [hs] at ha
  by_contra hn
  apply ha
  apply Image.codeAt_outside hwf
  intro c hc
  have h1 := hlo c hc
  have h2 := hhi c hc
  have := c.lo_le_hi
  omega

/-! ## The read-only segment -/

theorem DataChunk.wordAt_eq {c : DataChunk} {n : Nat} (hn : n < c.size) :
    c.wordAt n = (c.words ++ List.replicate c.zeros 0)[n]! := by
  simp only [DataChunk.size] at hn
  rw [getElem!_pos _ _ (by simp; omega), DataChunk.wordAt, List.getD_eq_getElem?_getD]
  by_cases h : n < c.words.length
  · rw [List.getElem_append_left h, List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem_append_right (by omega), List.getElem_replicate, List.getElem?_eq_none (by omega)]; rfl

/-- `RoImage L s` from the data chunk the layout's chunks were cut from. -/
theorem roImage_of_image {img : Image} (hwf : img.dataWF = true) (L : Layout) {k : Nat}
    {c : DataChunk} (hk : img.data[k]? = some c) (hbase : c.base.toNat = L.roBase)
    (hchunks : ∀ j, j < L.roChunks →
      L.roChunk j = ((c.words ++ List.replicate c.zeros 0).drop (64 * j)).take 64)
    {s : MachineState} (hs : ∀ a, s.getMem a = img.memAt a) : RoImage L s := by
  intro j hj i hi
  rw [hchunks j hj] at hi ⊢
  have hsz : (c.words ++ List.replicate c.zeros 0).length = c.size := by
    simp [DataChunk.size]
  simp only [List.length_take, List.length_drop, hsz] at hi
  have hn : 64 * j + i < c.size := by
    rcases Nat.lt_min.mp hi with ⟨_, h2⟩; omega
  have haddr : roChunkBase L j + BitVec.ofNat 64 (8 * i) = c.base + BitVec.ofNat 64 (8 * (64 * j + i)) := by
    have : c.base = BitVec.ofNat 64 L.roBase := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, hbase]
      exact (Nat.mod_eq_of_lt (hbase ▸ c.base.isLt)).symm
    rw [this, roChunkBase, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega
  rw [haddr, hs, Image.memAt_chunk hwf hk hn, DataChunk.wordAt_eq hn]
  have hn' : 64 * j + i < (c.words ++ List.replicate c.zeros 0).length := by rw [hsz]; exact hn
  have hi' : i < (((c.words ++ List.replicate c.zeros 0).drop (64 * j)).take 64).length := by
    simp only [List.length_take, List.length_drop]; omega
  rw [getElem!_pos (c.words ++ List.replicate c.zeros 0) (64 * j + i) hn']
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, if_pos (by omega),
    List.getElem?_eq_getElem hn']
  rfl

end AsmVerif.RiscV.Sym
