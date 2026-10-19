import Cases.Zip2005.Sinsemilla.FromIterNoteKit
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_7801dfb4
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-!
# `from_iter`'s last word and exit (0x7801e0d4 at byte 1088)

Bytes 1088–1089 of the `Vec` (word 136), then call 1090 yields `None`: the `Vec` header is copied
to the output, the frame restored, and `from_iter` returns.
-/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_iter_note_tail {Gd : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp sp0 out v p bit0 w w64 : Word)
    (J G K R Q I O : List Word) (j : Word) (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (hOl : O.length = 3)
    (hIl : I.length = 18) (hIv : noteState sp0 J j 1089 = I)
    (rav s0v s1v s2v s3v s4v s5v : Word) (hra1 : rav &&& ~~~1#64 = rav)
    (hpc : s.pc = 0x7801e0d4#64) (hcode : CodeAt F_7801dfb4.base F_7801dfb4.prog s)
    (hcodeN : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    -- the run's heap invariant, the `Vec`'s block live; the output header below the heap
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt ((p, 256) :: L) s)
    (hplo : 0x78048980 ≤ p.toNat) (hphi : p.toNat + 8 * 256 ≤ 0x1c00000000)
    (hout : out.toNat + 8 * 3 ≤ 0x78040620)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x180 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = 1088#64)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (noteBit G K v R Q 1088) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [2048#64, p, 1088#64] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 18)
    (hF : Region (sp + 0xa8#64) [s5v, s4v, s3v, s2v, s1v, s0v, rav] s)
    (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa8#64) 7)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hW : Region (p + 1088#64) [w, w64] s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi (p + 1088#64) 2)
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
    (hdjFBlk : Disjoint (sp - 0x180#64) 48 (sp + 0x18#64) 18)
    (hdjFW : Disjoint (sp - 0x180#64) 48 (p + 1088#64) 2) (hdjSW : Disjoint sp 28 (p + 1088#64) 2)
    (hdjWG : Disjoint (p + 1088#64) 2 (sp0 + 18446744073709551408#64) 4)
    (hdjWK : Disjoint (p + 1088#64) 2 (sp0 + 18446744073709551440#64) 4)
    (hdjWV : Disjoint (p + 1088#64) 2 (sp0 + 18446744073709551472#64) 1)
    (hdjWR : Disjoint (p + 1088#64) 2 (sp0 + 18446744073709551480#64) 4)
    (hdjWQ : Disjoint (p + 1088#64) 2 (sp0 + 18446744073709551512#64) 4)
    (hdjOS : Disjoint out 3 sp 28) (hdjOW : Disjoint out 3 (p + 1088#64) 2)
    (hdjFO : Disjoint (sp - 0x180#64) 48 out 3)
    (hdjOG : Disjoint out 3 (sp0 + 18446744073709551408#64) 4)
    (hdjOK : Disjoint out 3 (sp0 + 18446744073709551440#64) 4)
    (hdjOV : Disjoint out 3 (sp0 + 18446744073709551472#64) 1)
    (hdjOR : Disjoint out 3 (sp0 + 18446744073709551480#64) 4)
    (hdjOQ : Disjoint out 3 (sp0 + 18446744073709551512#64) 4)
    (hk : ∀ (t : MachineState) (I' : List Word) (w' : Word), t.pc = rav → t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (p + 1088#64, 2), (out, 3)] s t →
      t.getReg .x2 = sp + 0xe0#64 → t.getReg .x8 = s0v → t.getReg .x9 = s1v → t.getReg .x18 = s2v →
      t.getReg .x19 = s3v → t.getReg .x20 = s4v → t.getReg .x21 = s5v →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      Region out [2048#64, p, 1090#64] t → Region sp [2048#64, p, 1090#64] t →
      I'.length = 18 → noteState sp0 J j 1091 = I' → Region (sp + 0x18#64) I' t →
      Region (p + 1088#64) [w', w64] t →
      (∀ b, b < 2 → extractByte w' b = BitVec.truncate 8 (bw (noteBit G K v R Q (1088 + b)))) →
      RoImage Ro.layout t → Run.HeapAt ((p, 256) :: L) t → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hu := Unchanged.refl [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (p + 1088#64, 2), (out, 3)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x180#64) 48 s
  have hIv' : noteState sp0 J j 1089 = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!, I[12]!, I[13]!, I[14]!, I[15]!, I[16]!, I[17]!] := by
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
  -- call 1090: `None`
  have hend : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 : Word),
      noteState sp0 J j 1090 = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] →
      u.pc = 0x78021720#64 → CodeAt F_78021720.base F_78021720.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e0cc#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] u → Region (sp0 + 18446744073709551408#64) G u → Region (sp0 + 18446744073709551440#64) K u → Region (sp0 + 18446744073709551472#64) [v] u → Region (sp0 + 18446744073709551480#64) R u → Region (sp0 + 18446744073709551512#64) Q u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' i12' i13' i14' i15' i16' i17' : Word), t.pc = 0x7801e0cc#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x180#64, 48), (sp + 0x18#64, 18)] u t →
        noteState sp0 J j 1091 = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] t →
        t.getReg .x10 = 2#64 → SafeN Gd n P t) → SafeN Gd n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 hIv hpc hcode hcw hcodeEq hra hsp' ha0 hI hG hK hV hR hQ hk' =>
      pad_next_note_end_cells_spec u 0x7801e0cc#64 sp sp0 (sp + 0x18#64) v J G K R Q i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 hGl hKl hRl hQl j hIv hpc
        hcode hcw hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokBlk hG hokG hK hokK hV hokVv hR hokR hQ hokQ hdjBG hdjBK hdjBV hdjBR hdjBQ
        hdjFBlk hdjFG hdjFK hdjFV hdjFR hdjFQ hk'
  sym_exec [hnext, hend]
  sym_close hk _ _ v15
  · -- bytes 1088–1089 of the `Vec`: the bits
    intro b hb2
    rw [← v15_def, ← v3_def, ← hbit0, ← post9_25]
    interval_cases b <;>
      simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte, Nat.add_zero]
  · rfl

end Cases.Zip2005
