/-
  AsmVerif.RiscV.Sym.LoadRo

  The converse of `roImage_of_image`: a state whose memory holds a layout's read-only chunks
  (`RoImage`) holds the image's words at every aligned address of the segment. This is how a
  run that carries `RoImage` meets a precondition stated against the loaded image (the frame
  checker's protected regions, a table a runtime function reads).
-/

import AsmVerif.RiscV.Sym.Load

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64 AsmVerif.RiscV

/-- **The segment, word by word.** With the layout's chunks cut from data chunk `c`, which
    covers the segment, `RoImage` gives the image's word at each aligned address of it. -/
theorem memAt_of_roImage {img : Image} (hwf : img.dataWF = true) (L : Layout) {k : Nat}
    {c : DataChunk} (hk : img.data[k]? = some c) (hbase : c.base.toNat = L.roBase)
    (hchunks : ∀ j, j < L.roChunks →
      L.roChunk j = ((c.words ++ List.replicate c.zeros 0).drop (64 * j)).take 64)
    (hsize : L.roBytes ≤ 8 * c.size) (hcnt : c.size ≤ 64 * L.roChunks)
    {s : MachineState} (h : RoImage L s) {a : Word} (ha8 : a.toNat % 8 = 0)
    (h1 : L.roBase ≤ a.toNat) (h2 : a.toNat < L.roBase + L.roBytes) :
    s.getMem a = img.memAt a := by
  have hb := L.ro_inMem
  have hal := L.ro_aligned
  have hM : SP1_MAX_MEMORY < 2 ^ 64 := by decide
  obtain ⟨j, i, hi64, hja⟩ : ∃ j i, i < 64 ∧ a.toNat = L.roBase + 512 * j + 8 * i :=
    ⟨(a.toNat - L.roBase) / 512, ((a.toNat - L.roBase) % 512) / 8, by omega, by omega⟩
  have hsz : (c.words ++ List.replicate c.zeros 0).length = c.size := by simp [DataChunk.size]
  have hn : 64 * j + i < c.size := by omega
  have hj : j < L.roChunks := by omega
  have hi : i < (L.roChunk j).length := by
    rw [hchunks j hj]; simp only [List.length_take, List.length_drop, hsz]; omega
  have hreg := h j hj i hi
  have haddr : roChunkBase L j + BitVec.ofNat 64 (8 * i) = a := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_roCell hj hi, hja]
  have haddr' : c.base + BitVec.ofNat 64 (8 * (64 * j + i)) = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hbase, hja]
    rw [Nat.mod_eq_of_lt (a := 8 * (64 * j + i)) (by omega),
      Nat.mod_eq_of_lt (a := L.roBase + 8 * (64 * j + i)) (by omega)]
    omega
  rw [← haddr, hreg, haddr, ← haddr', Image.memAt_chunk hwf hk hn, DataChunk.wordAt_eq hn,
    hchunks j hj]
  have hn' : 64 * j + i < (c.words ++ List.replicate c.zeros 0).length := by rw [hsz]; exact hn
  have hi' : i < (((c.words ++ List.replicate c.zeros 0).drop (64 * j)).take 64).length := by
    simp only [List.length_take, List.length_drop]; omega
  rw [getElem!_pos (c.words ++ List.replicate c.zeros 0) (64 * j + i) hn',
    getElem!_pos _ i hi', List.getElem_take, List.getElem_drop]

end AsmVerif.RiscV.Sym
