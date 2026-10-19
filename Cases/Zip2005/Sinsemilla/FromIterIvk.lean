import Cases.Zip2005.Sinsemilla.PadNextIvkSpec
import Cases.Zip2005.Image.F_7801e110
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Vec<u8>::from_iter` of `commit_ivk`'s padded bit iterator (0x7801e110)

The loop (`0x7801e230`, one byte stored per `Pad::next`), one word at a time.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- From the loop head at byte `8m + 1` to the loop head at byte `8m + 8`: seven bytes of
    word `m` of the `Vec` (`q = p + 8m`), seven calls. -/
theorem from_iter_ivk_word {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} {K : Nat} (s : MachineState) (sp sp0 out p iw q cap w bit0 : Word)
    (J A B I : List Word) (j : Word) (hAl : A.length = 4) (hBl : B.length = 4)
    (m : Nat) (hm : m ≤ 62)
    (hIl : I.length = 12) (hIv : ivkState sp0 J j (8 * m + 2) = I)
    (hq1 : p + (iw + 1#64) = q + 1#64) (hq2 : p + (iw + 2#64) = q + 2#64)
    (hq3 : p + (iw + 3#64) = q + 3#64) (hq4 : p + (iw + 4#64) = q + 4#64)
    (hq5 : p + (iw + 5#64) = q + 5#64) (hq6 : p + (iw + 6#64) = q + 6#64)
    (hq7 : p + (iw + 7#64) = q + 7#64)
    (hc1 : (iw + 1#64 == cap) = false) (hc2 : (iw + 2#64 == cap) = false)
    (hc3 : (iw + 3#64 == cap) = false) (hc4 : (iw + 4#64 == cap) = false)
    (hc5 : (iw + 5#64 == cap) = false) (hc6 : (iw + 6#64 == cap) = false)
    (hc7 : (iw + 7#64 == cap) = false)
    (hpc : s.pc = 0x7801e230#64) (hcode : CodeAt F_7801e110.base F_7801e110.prog s)
    (hcodeN : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    -- the run's heap invariant, the `Vec`'s block `(p, K)` live and the word `q` in it
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt ((p, K) :: L) s)
    (hqlo : p.toNat ≤ q.toNat) (hqhi : q.toNat + 8 * 1 ≤ p.toNat + 8 * K)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = iw + 1#64)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (ivkBit A B (8 * m + 1)) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [cap, p, iw + 1#64] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 12)
    (hW : Region q [w] s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi q 1)
    (hAr : Region (ptrA sp0) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4)
    (hBr : Region (ptrB sp0) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjBA : Disjoint (sp + 0x18#64) 12 (ptrA sp0) 4) (hdjBB : Disjoint (sp + 0x18#64) 12 (ptrB sp0) 4)
    (hdjFA : Disjoint (sp - 0x10#64) 2 (ptrA sp0) 4) (hdjFB : Disjoint (sp - 0x10#64) 2 (ptrB sp0) 4)
    (hdjAB : Disjoint (ptrA sp0) 4 (ptrB sp0) 4)
    (hdjFW : Disjoint (sp - 0x10#64) 2 q 1) (hdjVW : Disjoint sp 3 q 1)
    (hdjBW : Disjoint (sp + 0x18#64) 12 q 1) (hdjFBlk : Disjoint (sp - 0x10#64) 2 (sp + 0x18#64) 12)
    (hdjWA : Disjoint q 1 (ptrA sp0) 4) (hdjWB : Disjoint q 1 (ptrB sp0) 4)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ (t : MachineState) (I' : List Word) (w' bit' : Word), t.pc = 0x7801e230#64 → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (q, 1)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = p → t.getReg .x18 = iw + 8#64 →
      t.getReg .x19 = 2#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      bw (ivkBit A B (8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1)) = bit' → t.getReg .x20 = bit' →
      Region sp [cap, p, iw + 8#64] t →
      I'.length = 12 → ivkState sp0 J j (8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = I' →
      Region (sp + 0x18#64) I' t →
      Region q [w'] t → extractByte w' 0 = extractByte w 0 →
      (∀ b, 1 ≤ b → b < 8 → extractByte w' b = BitVec.truncate 8 (bw (ivkBit A B (8 * m + b)))) →
      RoImage Ro.layout t → Run.HeapAt ((p, K) :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (q, 1)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hIv' : ivkState sp0 J j (8 * m + 2) = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!] := by
    rw [hIv]; exact list12_cells I hIl
  have hiterB : (sp + 0x18#64).toNat + 8 * 12 ≤ 0x78040620 := by
    have h := hstk.hi; rw [Ro.layout_stackTop] at h; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  -- `Pad::next` at this call site, the message fixed
  have hnext : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word) (k : Nat) (L' : List (Word × Nat)),
      ivkState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] → k < 510 →
      u.pc = 0x78021e7c#64 → CodeAt F_78021e7c.base F_78021e7c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e228#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] u → Region (ptrA sp0) A u → Region (ptrB sp0) B u →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' bit : Word), t.pc = 0x7801e228#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x10#64, 2), (sp + 0x18#64, 12)] u t →
        ivkState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
        bw (ivkBit A B k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → SafeN G n P t) → SafeN G n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 k L' hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hA hB hro' hheap' hk' =>
      pad_next_ivk_cells_spec (L := L') u 0x7801e228#64 sp sp0 (sp + 0x18#64) J A B i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 hAl hBl j k hIv hk hpc
        hcode hcw hro' hheap' hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokBlk hiterB hA hokA hB hokB hdjBA hdjBB
        hdjFBlk hdjFA hdjFB hdjAB (fun u' sp'' L'' h1 h2 => hunwrap_opt u' sp'' L'' h1 (h2.trans hcodeEq)) hk'
  sym_exec [hnext] 84
  sym_close hk _ _ _ post81_12
  · -- byte 0 of the word: untouched
    rw [← v75_def, ← v63_def, ← v51_def, ← v39_def, ← v27_def, ← v15_def, ← v3_def]
    simp (disch := decide) only [extractByte_replaceByte_ne]
  · -- bytes 1–7: the bits
    intro b hb1 hb8
    rw [← v75_def, ← v63_def, ← v51_def, ← v39_def, ← v27_def, ← v15_def, ← v3_def, ← hbit0,
      ← post9_19, ← post21_19, ← post33_19, ← post45_19, ← post57_19, ← post69_19]
    interval_cases b <;>
      simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
  · rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- From the loop head at byte `8m` to the loop head at byte `8(m + 1)`: the eight bytes of
    word `m` of the `Vec` (`q = p + 8m`), eight calls. -/
theorem from_iter_ivk_word8 {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} {K : Nat} (s : MachineState) (sp sp0 out p iw q cap w bit0 : Word)
    (J A B I : List Word) (j : Word) (hAl : A.length = 4) (hBl : B.length = 4)
    (m : Nat) (hm : m ≤ 62)
    (hIl : I.length = 12) (hIv : ivkState sp0 J j (8 * m + 1) = I)
    (hq : p + iw = q) (hq1 : p + (iw + 1#64) = q + 1#64) (hq2 : p + (iw + 2#64) = q + 2#64)
    (hq3 : p + (iw + 3#64) = q + 3#64) (hq4 : p + (iw + 4#64) = q + 4#64)
    (hq5 : p + (iw + 5#64) = q + 5#64) (hq6 : p + (iw + 6#64) = q + 6#64)
    (hq7 : p + (iw + 7#64) = q + 7#64)
    (hc0 : (iw == cap) = false) (hc1 : (iw + 1#64 == cap) = false) (hc2 : (iw + 2#64 == cap) = false)
    (hc3 : (iw + 3#64 == cap) = false) (hc4 : (iw + 4#64 == cap) = false)
    (hc5 : (iw + 5#64 == cap) = false) (hc6 : (iw + 6#64 == cap) = false)
    (hc7 : (iw + 7#64 == cap) = false)
    (hpc : s.pc = 0x7801e230#64) (hcode : CodeAt F_7801e110.base F_7801e110.prog s)
    (hcodeN : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    -- the run's heap invariant, the `Vec`'s block `(p, K)` live and the word `q` in it
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt ((p, K) :: L) s)
    (hqlo : p.toNat ≤ q.toNat) (hqhi : q.toNat + 8 * 1 ≤ p.toNat + 8 * K)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = iw)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (ivkBit A B (8 * m)) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [cap, p, iw] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 12)
    (hW : Region q [w] s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi q 1)
    (hAr : Region (ptrA sp0) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4)
    (hBr : Region (ptrB sp0) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjBA : Disjoint (sp + 0x18#64) 12 (ptrA sp0) 4) (hdjBB : Disjoint (sp + 0x18#64) 12 (ptrB sp0) 4)
    (hdjFA : Disjoint (sp - 0x10#64) 2 (ptrA sp0) 4) (hdjFB : Disjoint (sp - 0x10#64) 2 (ptrB sp0) 4)
    (hdjAB : Disjoint (ptrA sp0) 4 (ptrB sp0) 4)
    (hdjFW : Disjoint (sp - 0x10#64) 2 q 1) (hdjVW : Disjoint sp 3 q 1)
    (hdjBW : Disjoint (sp + 0x18#64) 12 q 1) (hdjFBlk : Disjoint (sp - 0x10#64) 2 (sp + 0x18#64) 12)
    (hdjWA : Disjoint q 1 (ptrA sp0) 4) (hdjWB : Disjoint q 1 (ptrB sp0) 4)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ (t : MachineState) (I' : List Word) (w' bit' : Word), t.pc = 0x7801e230#64 → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (q, 1)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = p → t.getReg .x18 = iw + 8#64 →
      t.getReg .x19 = 2#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      bw (ivkBit A B (8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = bit' → t.getReg .x20 = bit' →
      Region sp [cap, p, iw + 8#64] t →
      I'.length = 12 → ivkState sp0 J j (8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = I' →
      Region (sp + 0x18#64) I' t →
      Region q [w'] t →
      (∀ b, b < 8 → extractByte w' b = BitVec.truncate 8 (bw (ivkBit A B (8 * m + b)))) →
      RoImage Ro.layout t → Run.HeapAt ((p, K) :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (q, 1)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hIv' : ivkState sp0 J j (8 * m + 1) = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!] := by
    rw [hIv]; exact list12_cells I hIl
  have hiterB : (sp + 0x18#64).toNat + 8 * 12 ≤ 0x78040620 := by
    have h := hstk.hi; rw [Ro.layout_stackTop] at h; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  -- `Pad::next` at this call site, the message fixed
  have hnext : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word) (k : Nat) (L' : List (Word × Nat)),
      ivkState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] → k < 510 →
      u.pc = 0x78021e7c#64 → CodeAt F_78021e7c.base F_78021e7c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e228#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] u → Region (ptrA sp0) A u → Region (ptrB sp0) B u →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' bit : Word), t.pc = 0x7801e228#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x10#64, 2), (sp + 0x18#64, 12)] u t →
        ivkState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
        bw (ivkBit A B k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → SafeN G n P t) → SafeN G n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 k L' hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hA hB hro' hheap' hk' =>
      pad_next_ivk_cells_spec (L := L') u 0x7801e228#64 sp sp0 (sp + 0x18#64) J A B i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 hAl hBl j k hIv hk hpc
        hcode hcw hro' hheap' hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokBlk hiterB hA hokA hB hokB hdjBA hdjBB
        hdjFBlk hdjFA hdjFB hdjAB (fun u' sp'' L'' h1 h2 => hunwrap_opt u' sp'' L'' h1 (h2.trans hcodeEq)) hk'
  sym_exec [hnext] 96
  sym_close hk _ _ _ post93_12
  · -- the eight bytes: the bits
    intro b hb8
    rw [← v87_def, ← v75_def, ← v63_def, ← v51_def, ← v39_def, ← v27_def, ← v15_def, ← v3_def, ← hbit0,
      ← post9_19, ← post21_19, ← post33_19, ← post45_19, ← post57_19, ← post69_19, ← post81_19]
    interval_cases b <;>
      simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte, Nat.add_zero]
  · rfl

end Cases.Zip2005
