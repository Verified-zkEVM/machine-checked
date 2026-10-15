import Cases.Zip2005.Runtime.Hint
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `sp1_zkvm::io::read_vec_raw` (0x7801beb0)

`HINT_LEN`; on `u64::MAX` (no vector left) an empty `Vec`. Otherwise the input bump pointer
`EMBEDDED_RESERVED_INPUT_PTR` (`0x78040618`) is advanced by the length rounded up to eight, with a
panic past `SP1_MAX_MEMORY` (`2^37`), and `HINT_READ` writes the vector at the old pointer. The
three words stored at `a0` are the pointer, the length and the rounded length.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem read_vec_raw_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} {sp0 : Word} (s : MachineState) (ra dst b : Word) (I : List (BitVec 8))
    (D J : List Word) (hDl : D.length = 3) (hJl : J.length = 175)
    (hpc : s.pc = 0x7801beb0#64) (hcode : CodeAt F_7801beb0.base F_7801beb0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp0 : s.getReg .x2 = sp0) (hstk0 : StackOk Ro.layout 0 sp0)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (hI : s.privateInput = I)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 3)
    (hB : Region 0x78040618#64 [b] s) (hb : 0x1c00000000 ≤ b.toNat)
    (hJ : Region b J s) (hokJ : RegionOk Ro.layout.textLo Ro.layout.textHi b 175)
    (hdD : dst.toNat + 24 ≤ 0x78040618)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hk0 : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 3), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000)] s t →
      t.privateInput = I → hlenW I = -1#64 → Region dst [0#64, 0#64, 0#64] t → Region b J t →
      Region 0x78040618#64 [b] t → SafeN G n P t)
    (hk1 : ∀ (t : MachineState) (L : Word) (B : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(dst, 3), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000)] s t →
      bytesToWordLE (I.take 8) = L → t.privateInput = I.drop (8 + L.toNat) →
      8 + L.toNat ≤ I.length → b.toNat + 8 * (L.toNat / 8 + 1) ≤ 0x2000000000 →
      hintWords ((I.drop 8).take L.toNat) = B → B.length = L.toNat / 8 + 1 → Region b (overlay B J) t →
      Region dst [b, L, L + 7#64 &&& 18446744073709551608#64] t →
      Region 0x78040618#64 [b + (L + 7#64 &&& 18446744073709551608#64)] t → SafeN G n P t) :
    SafeN G n P s := by
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040618#64 1 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hdB : Disjoint dst 3 0x78040618#64 1 := ⟨Or.inl (by simpa using hdD), by omega, by decide⟩
  have hJn := hokJ.inMem
  unfold SP1_MAX_MEMORY at hJn
  have hdJ : Disjoint dst 3 b 175 := ⟨Or.inl (by omega), by omega, by omega⟩
  have hdBJ : Disjoint 0x78040618#64 1 b 175 := ⟨Or.inl (by simp; omega), by decide, by omega⟩
  have hokI : RegionOk Ro.layout.textLo Ro.layout.textHi 0x1c00000000#64 0x80000000 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hu := Unchanged.refl [(dst, 3), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000)] s
  sym_exec [hint_len_spec, hint_read_spec, hpanic]
  · -- no vector left: an empty `Vec`
    have hs : hlenW I = -1#64 := by simpa using hbr4
    sym_close hk0
  · -- the vector at `b`, the pointer bumped by the rounded length
    have hlen6 : acc19_0.length = 175 := by rw [← acc19_0_def, overlay_length, hJl]
    have hRo : Region b (overlay post19_0 J) s_24 := by
      rw [acc19_0_def, AsmVerif.RiscV.Sym.List.eq_map_range acc19_0 hlen6]; exact hR2
    clear hR2
    subst v9_def v10_def
    sym_close (hk1 _ (hlenW I) post19_0)

end Cases.Zip2005
