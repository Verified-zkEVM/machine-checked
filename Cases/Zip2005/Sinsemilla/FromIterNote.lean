import Cases.Zip2005.Sinsemilla.FromIterNoteKit
import Cases.Zip2005.Image.F_7801dfb4
import Cases.Zip2005.Image.Ro

/-!
# `Vec<u8>::from_iter` of `NoteCommitment::derive`'s padded bit iterator (0x7801dfb4)

The loop (`0x7801e0d4`, one byte stored per `Pad::next`), one word at a time.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- From the loop head at byte `8m + 1` to the loop head at byte `8m + 8`: seven bytes of
    word `m` of the `Vec` (`q = p + 8m`), seven calls. -/
theorem from_iter_note_word {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (sp sp0 out v p iw q cap w bit0 : Word)
    (J G K R Q I : List Word) (j : Word) (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4)
    (m : Nat) (hm : m ≤ 135)
    (hIl : I.length = 18) (hIv : noteState sp0 J j (8 * m + 2) = I)
    (hq1 : p + (iw + 1#64) = q + 1#64) (hq2 : p + (iw + 2#64) = q + 2#64)
    (hq3 : p + (iw + 3#64) = q + 3#64) (hq4 : p + (iw + 4#64) = q + 4#64)
    (hq5 : p + (iw + 5#64) = q + 5#64) (hq6 : p + (iw + 6#64) = q + 6#64)
    (hq7 : p + (iw + 7#64) = q + 7#64)
    (hc1 : (iw + 1#64 == cap) = false) (hc2 : (iw + 2#64 == cap) = false)
    (hc3 : (iw + 3#64 == cap) = false) (hc4 : (iw + 4#64 == cap) = false)
    (hc5 : (iw + 5#64 == cap) = false) (hc6 : (iw + 6#64 == cap) = false)
    (hc7 : (iw + 7#64 == cap) = false)
    (hpc : s.pc = 0x7801e0d4#64) (hcode : CodeAt F_7801dfb4.base F_7801dfb4.prog s)
    (hcodeN : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x180 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = iw + 1#64)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (noteBit G K v R Q (8 * m + 1)) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [cap, p, iw + 1#64] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 18)
    (hW : Region q [w] s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi q 1)
    (hGr : Region (sp0 + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551408#64) 4)
    (hKr : Region (sp0 + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551440#64) 4)
    (hVr : Region (sp0 + 18446744073709551472#64) [v] s) (hokVv : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551472#64) 1)
    (hRr : Region (sp0 + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551480#64) 4)
    (hQr : Region (sp0 + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551512#64) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjBG : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551408#64) 4)
    (hdjBK : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551440#64) 4)
    (hdjBV : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551472#64) 1)
    (hdjBR : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551480#64) 4)
    (hdjBQ : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551512#64) 4)
    (hdjFG : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551408#64) 4)
    (hdjFK : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551440#64) 4)
    (hdjFV : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551472#64) 1)
    (hdjFR : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551480#64) 4)
    (hdjFQ : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551512#64) 4)
    (hdjFW : Disjoint (sp - 0x180#64) 48 q 1) (hdjVW : Disjoint sp 3 q 1)
    (hdjBW : Disjoint (sp + 0x18#64) 18 q 1) (hdjFBlk : Disjoint (sp - 0x180#64) 48 (sp + 0x18#64) 18)
    (hdjWG : Disjoint q 1 (sp0 + 18446744073709551408#64) 4)
    (hdjWK : Disjoint q 1 (sp0 + 18446744073709551440#64) 4)
    (hdjWV : Disjoint q 1 (sp0 + 18446744073709551472#64) 1)
    (hdjWR : Disjoint q 1 (sp0 + 18446744073709551480#64) 4)
    (hdjWQ : Disjoint q 1 (sp0 + 18446744073709551512#64) 4)
    (hk : ∀ (t : MachineState) (I' : List Word) (w' bit' : Word), t.pc = 0x7801e0d4#64 → t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (q, 1)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = p → t.getReg .x18 = iw + 8#64 →
      t.getReg .x19 = 2#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      bw (noteBit G K v R Q (8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1)) = bit' → t.getReg .x20 = bit' →
      Region sp [cap, p, iw + 8#64] t →
      I'.length = 18 → noteState sp0 J j (8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = I' →
      Region (sp + 0x18#64) I' t →
      Region q [w'] t → extractByte w' 0 = extractByte w 0 →
      (∀ b, 1 ≤ b → b < 8 → extractByte w' b = BitVec.truncate 8 (bw (noteBit G K v R Q (8 * m + b)))) →
      SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hu := Unchanged.refl [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (q, 1)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x180#64) 48 s
  have hIv' : noteState sp0 J j (8 * m + 2) = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!, I[12]!, I[13]!, I[14]!, I[15]!, I[16]!, I[17]!] := by
    rw [hIv]; exact list18_cells I hIl
  -- `Pad::next` at this call site, the message fixed
  have hnext : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 : Word) (k : Nat),
      noteState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] → k < 1090 →
      u.pc = 0x78021720#64 → CodeAt F_78021720.base F_78021720.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e0cc#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] u → Region (sp0 + 18446744073709551408#64) G u → Region (sp0 + 18446744073709551440#64) K u → Region (sp0 + 18446744073709551472#64) [v] u → Region (sp0 + 18446744073709551480#64) R u → Region (sp0 + 18446744073709551512#64) Q u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' i12' i13' i14' i15' i16' i17' bit : Word), t.pc = 0x7801e0cc#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x180#64, 48), (sp + 0x18#64, 18)] u t →
        noteState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] t →
        bw (noteBit G K v R Q k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → SafeN Gd n P t) → SafeN Gd n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hG hK hV hR hQ hk' =>
      pad_next_note_cells_spec u 0x7801e0cc#64 sp sp0 (sp + 0x18#64) v J G K R Q i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 hGl hKl hRl hQl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokBlk hG hokG hK hokK hV hokVv hR hokR hQ hokQ hdjBG hdjBK hdjBV hdjBR hdjBQ
        hdjFBlk hdjFG hdjFK hdjFV hdjFR hdjFQ hk'
  sym_exec [hnext] 84
  sym_close hk _ _ _ post81_18
  · -- byte 0 of the word: untouched
    rw [← v75_def, ← v63_def, ← v51_def, ← v39_def, ← v27_def, ← v15_def, ← v3_def]
    simp (disch := decide) only [extractByte_replaceByte_ne]
  · -- bytes 1–7: the bits
    intro b hb1 hb8
    rw [← v75_def, ← v63_def, ← v51_def, ← v39_def, ← v27_def, ← v15_def, ← v3_def, ← hbit0,
      ← post9_25, ← post21_25, ← post33_25, ← post45_25, ← post57_25, ← post69_25]
    interval_cases b <;>
      simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
  · rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- From the loop head at byte `8m` to the loop head at byte `8(m + 1)`: the eight bytes of
    word `m` of the `Vec` (`q = p + 8m`), eight calls. -/
theorem from_iter_note_word8 {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (sp sp0 out v p iw q cap w bit0 : Word)
    (J G K R Q I : List Word) (j : Word) (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4)
    (m : Nat) (hm : m ≤ 135)
    (hIl : I.length = 18) (hIv : noteState sp0 J j (8 * m + 1) = I)
    (hq : p + iw = q) (hq1 : p + (iw + 1#64) = q + 1#64) (hq2 : p + (iw + 2#64) = q + 2#64)
    (hq3 : p + (iw + 3#64) = q + 3#64) (hq4 : p + (iw + 4#64) = q + 4#64)
    (hq5 : p + (iw + 5#64) = q + 5#64) (hq6 : p + (iw + 6#64) = q + 6#64)
    (hq7 : p + (iw + 7#64) = q + 7#64)
    (hc0 : (iw == cap) = false) (hc1 : (iw + 1#64 == cap) = false) (hc2 : (iw + 2#64 == cap) = false)
    (hc3 : (iw + 3#64 == cap) = false) (hc4 : (iw + 4#64 == cap) = false)
    (hc5 : (iw + 5#64 == cap) = false) (hc6 : (iw + 6#64 == cap) = false)
    (hc7 : (iw + 7#64 == cap) = false)
    (hpc : s.pc = 0x7801e0d4#64) (hcode : CodeAt F_7801dfb4.base F_7801dfb4.prog s)
    (hcodeN : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x180 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = iw)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (noteBit G K v R Q (8 * m)) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [cap, p, iw] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 18)
    (hW : Region q [w] s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi q 1)
    (hGr : Region (sp0 + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551408#64) 4)
    (hKr : Region (sp0 + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551440#64) 4)
    (hVr : Region (sp0 + 18446744073709551472#64) [v] s) (hokVv : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551472#64) 1)
    (hRr : Region (sp0 + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551480#64) 4)
    (hQr : Region (sp0 + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551512#64) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjBG : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551408#64) 4)
    (hdjBK : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551440#64) 4)
    (hdjBV : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551472#64) 1)
    (hdjBR : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551480#64) 4)
    (hdjBQ : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551512#64) 4)
    (hdjFG : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551408#64) 4)
    (hdjFK : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551440#64) 4)
    (hdjFV : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551472#64) 1)
    (hdjFR : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551480#64) 4)
    (hdjFQ : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551512#64) 4)
    (hdjFW : Disjoint (sp - 0x180#64) 48 q 1) (hdjVW : Disjoint sp 3 q 1)
    (hdjBW : Disjoint (sp + 0x18#64) 18 q 1) (hdjFBlk : Disjoint (sp - 0x180#64) 48 (sp + 0x18#64) 18)
    (hdjWG : Disjoint q 1 (sp0 + 18446744073709551408#64) 4)
    (hdjWK : Disjoint q 1 (sp0 + 18446744073709551440#64) 4)
    (hdjWV : Disjoint q 1 (sp0 + 18446744073709551472#64) 1)
    (hdjWR : Disjoint q 1 (sp0 + 18446744073709551480#64) 4)
    (hdjWQ : Disjoint q 1 (sp0 + 18446744073709551512#64) 4)
    (hk : ∀ (t : MachineState) (I' : List Word) (w' bit' : Word), t.pc = 0x7801e0d4#64 → t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (q, 1)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = p → t.getReg .x18 = iw + 8#64 →
      t.getReg .x19 = 2#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      bw (noteBit G K v R Q (8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = bit' → t.getReg .x20 = bit' →
      Region sp [cap, p, iw + 8#64] t →
      I'.length = 18 → noteState sp0 J j (8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = I' →
      Region (sp + 0x18#64) I' t →
      Region q [w'] t →
      (∀ b, b < 8 → extractByte w' b = BitVec.truncate 8 (bw (noteBit G K v R Q (8 * m + b)))) →
      SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hu := Unchanged.refl [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (q, 1)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x180#64) 48 s
  have hIv' : noteState sp0 J j (8 * m + 1) = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!, I[12]!, I[13]!, I[14]!, I[15]!, I[16]!, I[17]!] := by
    rw [hIv]; exact list18_cells I hIl
  -- `Pad::next` at this call site, the message fixed
  have hnext : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 : Word) (k : Nat),
      noteState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] → k < 1090 →
      u.pc = 0x78021720#64 → CodeAt F_78021720.base F_78021720.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e0cc#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] u → Region (sp0 + 18446744073709551408#64) G u → Region (sp0 + 18446744073709551440#64) K u → Region (sp0 + 18446744073709551472#64) [v] u → Region (sp0 + 18446744073709551480#64) R u → Region (sp0 + 18446744073709551512#64) Q u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' i12' i13' i14' i15' i16' i17' bit : Word), t.pc = 0x7801e0cc#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x180#64, 48), (sp + 0x18#64, 18)] u t →
        noteState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] t →
        bw (noteBit G K v R Q k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → SafeN Gd n P t) → SafeN Gd n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hG hK hV hR hQ hk' =>
      pad_next_note_cells_spec u 0x7801e0cc#64 sp sp0 (sp + 0x18#64) v J G K R Q i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 hGl hKl hRl hQl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokBlk hG hokG hK hokK hV hokVv hR hokR hQ hokQ hdjBG hdjBK hdjBV hdjBR hdjBQ
        hdjFBlk hdjFG hdjFK hdjFV hdjFR hdjFQ hk'
  sym_exec [hnext] 96
  sym_close hk _ _ _ post93_18
  · -- the eight bytes: the bits
    intro b hb8
    rw [← v87_def, ← v75_def, ← v63_def, ← v51_def, ← v39_def, ← v27_def, ← v15_def, ← v3_def, ← hbit0,
      ← post9_25, ← post21_25, ← post33_25, ← post45_25, ← post57_25, ← post69_25, ← post81_25]
    interval_cases b <;>
      simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte, Nat.add_zero]
  · rfl

end Cases.Zip2005
