import Cases.Zip2005.Sinsemilla.FromIterNoteKit
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Image.F_7801dfb4
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `from_iter`'s prologue (0x7801dfb4 to the loop head at byte 1)

The first `next` on the caller's block (bit 0), `__rust_alloc(8, 1)` (A4, this call's
instance) for the `Vec`'s first block, byte 0 stored, the `Vec` header `(8, ptr, 1)` in the
frame, the iterator block copied into the frame (`memcpy(_, _, 96)`), and the second `next`
(bit 1) on the copy.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_iter_note_pro {Gd : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp sp0 out a1 ra v : Word)
    (J G K R Q Cb O : List Word) (j : Word) (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4)
    (hCbl : Cb.length = 18) (hCb : noteState sp0 J j 0 = Cb) (hOl : O.length = 3)
    (hpc : s.pc = 0x7801dfb4#64) (hcode : CodeAt F_7801dfb4.base F_7801dfb4.prog s)
    (hcodeN : CodeAt F_78021720.base F_78021720.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra)
    (hsp : s.getReg .x2 = sp + 0xe0#64) (hstk : StackOk Ro.layout 0x180 sp) (hokFr : RegionOk Ro.layout.roBase Ro.layout.textHi sp 28)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hCbr : Region a1 Cb s) (hokCb : RegionOk Ro.layout.roBase Ro.layout.textHi a1 18)
    (ha1hi : a1.toNat + 8 * 18 ≤ 0x78040620)
    (hGr : Region (sp0 + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551408#64) 4)
    (hKr : Region (sp0 + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551440#64) 4)
    (hVr : Region (sp0 + 18446744073709551472#64) [v] s) (hokVv : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551472#64) 1)
    (hRr : Region (sp0 + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551480#64) 4)
    (hQr : Region (sp0 + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551512#64) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjSO : Disjoint sp 28 out 3) (hdjSC : Disjoint sp 28 a1 18)
    (hdjSG : Disjoint sp 28 (sp0 + 18446744073709551408#64) 4)
    (hdjSK : Disjoint sp 28 (sp0 + 18446744073709551440#64) 4)
    (hdjSV : Disjoint sp 28 (sp0 + 18446744073709551472#64) 1)
    (hdjSR : Disjoint sp 28 (sp0 + 18446744073709551480#64) 4)
    (hdjSQ : Disjoint sp 28 (sp0 + 18446744073709551512#64) 4)
    (hdjBG : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551408#64) 4)
    (hdjBK : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551440#64) 4)
    (hdjBV : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551472#64) 1)
    (hdjBR : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551480#64) 4)
    (hdjBQ : Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551512#64) 4)
    (hdjFBlk : Disjoint (sp - 0x180#64) 48 (sp + 0x18#64) 18)
    (hdjFC : Disjoint (sp - 0x180#64) 48 a1 18)
    (hdjFG : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551408#64) 4)
    (hdjFK : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551440#64) 4)
    (hdjFV : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551472#64) 1)
    (hdjFR : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551480#64) 4)
    (hdjFQ : Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551512#64) 4)
    (hdjFO : Disjoint (sp - 0x180#64) 48 out 3)
    (hdjBC : Disjoint (sp + 0x18#64) 18 a1 18)
    (hdjOC : Disjoint out 3 a1 18) (hdjOG : Disjoint out 3 (sp0 + 18446744073709551408#64) 4)
    (hdjOK : Disjoint out 3 (sp0 + 18446744073709551440#64) 4)
    (hdjOV : Disjoint out 3 (sp0 + 18446744073709551472#64) 1)
    (hdjOR : Disjoint out 3 (sp0 + 18446744073709551480#64) 4)
    (hdjOQ : Disjoint out 3 (sp0 + 18446744073709551512#64) 4)
    (hdjCG : Disjoint a1 18 (sp0 + 18446744073709551408#64) 4)
    (hdjCK : Disjoint a1 18 (sp0 + 18446744073709551440#64) 4)
    (hdjCV : Disjoint a1 18 (sp0 + 18446744073709551472#64) 1)
    (hdjCR : Disjoint a1 18 (sp0 + 18446744073709551480#64) 4)
    (hdjCQ : Disjoint a1 18 (sp0 + 18446744073709551512#64) 4)
    (hdjHG : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551408#64) 4)
    (hdjHK : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551440#64) 4)
    (hdjHV : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551472#64) 1)
    (hdjHR : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551480#64) 4)
    (hdjHQ : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551512#64) 4)
    (hdjHO : Disjoint 0x78040620#64 14780694332 out 3)
    (hdjHC : Disjoint 0x78040620#64 14780694332 a1 18)
    -- `__rust_alloc(8, 1)` (A4, this call's instance): a fresh word in the arena
    (halloc : ∀ (u : MachineState) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e028#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e028#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 1) :: L') t → SafeN Gd n P t) → SafeN Gd n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN Gd n P u)
    (hk : ∀ (t : MachineState) (ptr w bit0 bit1 : Word) (I1 I2 : List Word), t.pc = 0x7801e0d4#64 →
      t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 28), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = ptr → t.getReg .x18 = 1#64 →
      t.getReg .x19 = 2#64 → bw (noteBit G K v R Q 1) = bit1 → t.getReg .x20 = bit1 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      I2.length = 18 → noteState sp0 J j (0 + 1 + 1) = I2 →
      Region sp ([8#64, ptr, 1#64] ++ I2 ++ [s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
        s.getReg .x9, s.getReg .x8, ra]) t →
      I1.length = 18 → Region a1 I1 t →
      Region out O t →
      bw (noteBit G K v R Q 0) = bit0 → Region ptr [w] t → extractByte w 0 = BitVec.truncate 8 bit0 →
      RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 ≤ 0x1c00000000 →
      RoImage Ro.layout t → Run.HeapAt ((ptr, 1) :: L) t → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3 := hokFr.sub' 0 3 (by decide) (by simp)
  have hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 18 := hokFr.sub' 3 18 (by decide) rfl
  have hokSv : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa8#64) 7 := hokFr.sub' 21 7 (by decide) rfl
  have hokFr' : RegionOk Ro.layout.textLo Ro.layout.textHi sp 28 := hokFr.weaken (by decide) (by decide)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hstk30 : StackOk Ro.layout 0x30 sp := ⟨hstk.aligned, by have := hstk.lo; omega, hstk.hi⟩
  have hu := Unchanged.refl [(sp - 0x180#64, 48), (sp, 28), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x180#64) 48 s
  obtain ⟨Fr, hFr, hFrl⟩ := Region.exists_junk sp 28 s
  have hCb' : noteState sp0 J j 0 = [Cb[0]!, Cb[1]!, Cb[2]!, Cb[3]!, Cb[4]!, Cb[5]!, Cb[6]!, Cb[7]!, Cb[8]!, Cb[9]!, Cb[10]!, Cb[11]!, Cb[12]!, Cb[13]!, Cb[14]!, Cb[15]!, Cb[16]!, Cb[17]!] := by
    rw [hCb]; exact list18_cells Cb hCbl
  have hnext0 : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 : Word) (k : Nat),
      noteState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] → k < 1090 →
      u.pc = 0x78021720#64 → CodeAt F_78021720.base F_78021720.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801dfe8#64 → u.getReg .x2 = sp → u.getReg .x10 = a1 →
      Region (a1) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] u → Region (sp0 + 18446744073709551408#64) G u → Region (sp0 + 18446744073709551440#64) K u → Region (sp0 + 18446744073709551472#64) [v] u → Region (sp0 + 18446744073709551480#64) R u → Region (sp0 + 18446744073709551512#64) Q u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' i12' i13' i14' i15' i16' i17' bit : Word), t.pc = 0x7801dfe8#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x180#64, 48), (a1, 18)] u t →
        noteState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] → Region (a1) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] t →
        bw (noteBit G K v R Q k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → SafeN Gd n P t) → SafeN Gd n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hG hK hV hR hQ hk' =>
      pad_next_note_cells_spec u 0x7801dfe8#64 sp sp0 (a1) v J G K R Q i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 hGl hKl hRl hQl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokCb hG hokG hK hokK hV hokVv hR hokR hQ hokQ hdjCG hdjCK hdjCV hdjCR hdjCQ
        hdjFC hdjFG hdjFK hdjFV hdjFR hdjFQ hk'
  have hnext1 : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 : Word) (k : Nat),
      noteState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] → k < 1090 →
      u.pc = 0x78021720#64 → CodeAt F_78021720.base F_78021720.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e060#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] u → Region (sp0 + 18446744073709551408#64) G u → Region (sp0 + 18446744073709551440#64) K u → Region (sp0 + 18446744073709551472#64) [v] u → Region (sp0 + 18446744073709551480#64) R u → Region (sp0 + 18446744073709551512#64) Q u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' i12' i13' i14' i15' i16' i17' bit : Word), t.pc = 0x7801e060#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x180#64, 48), (sp + 0x18#64, 18)] u t →
        noteState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] t →
        bw (noteBit G K v R Q k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → SafeN Gd n P t) → SafeN Gd n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hG hK hV hR hQ hk' =>
      pad_next_note_cells_spec u 0x7801e060#64 sp sp0 (sp + 0x18#64) v J G K R Q i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 hGl hKl hRl hQl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokBlk hG hokG hK hokK hV hokVv hR hokR hQ hokQ
        hdjBG hdjBK hdjBV hdjBR hdjBQ hdjFBlk hdjFG hdjFK hdjFV hdjFR hdjFQ hk'
  have hO3 : O = [O[0]!, O[1]!, O[2]!] := by
    match O, hOl with
    | [_, _, _], _ => rfl
  -- the continuation over the frame's cells, as the executor states it
  have hk' : ∀ (t : MachineState) (ptr w bit0 bit1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 : Word),
      t.pc = 0x7801e0d4#64 → t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 28), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = ptr → t.getReg .x18 = 1#64 →
      t.getReg .x19 = 2#64 → bw (noteBit G K v R Q 1) = bit1 → t.getReg .x20 = bit1 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      noteState sp0 J j (0 + 1 + 1) = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17] →
      Region sp [8#64, ptr, 1#64, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
        s.getReg .x9, s.getReg .x8, ra] t →
      Region a1 [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17] t →
      Region out [O[0]!, O[1]!, O[2]!] t →
      bw (noteBit G K v R Q 0) = bit0 → Region ptr [w] t → extractByte w 0 = BitVec.truncate 8 bit0 →
      RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 ≤ 0x1c00000000 →
      RoImage Ro.layout t → Run.HeapAt ((ptr, 1) :: L) t → SafeN Gd n P t :=
    fun t ptr w bit0 bit1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 hpc' hcode' hun hsp' hs0 hs1 hs2 hs3 hb1 hs4
        h3 h4 h22 h23 h24 h25 h26 h27 hI2 hR hR1 hO' hb0 hW hw hok hlo hhi hro' hheap' =>
      hk t ptr w bit0 bit1 [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17] [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17] hpc' hcode' hun hsp' hs0 hs1 hs2 hs3 hb1 hs4
        h3 h4 h22 h23 h24 h25 h26 h27 rfl hI2 hR rfl hR1 (by rw [hO3]; exact hO') hb0 hW hw hok hlo hhi hro' hheap'
  sym_exec [hnext0, hnext1, halloc, hhandle_rv, memcpy144_spec] stop [0x7801e0d4]
  sym_close hk' _ post26_0 v29 post13_18 post42_18 post13_0 post13_1 post13_2 post13_3 post13_4 post13_5 post13_6 post13_7 post13_8 post13_9 post13_10 post13_11 post13_12 post13_13 post13_14 post13_15 post13_16 post13_17 post42_0 post42_1 post42_2 post42_3 post42_4 post42_5 post42_6 post42_7 post42_8 post42_9 post42_10 post42_11 post42_12 post42_13 post42_14 post42_15 post42_16 post42_17
  all_goals first
    | rfl
    | (rw [← v29_def, extractByte_replaceByte _ _ (by decide)])

end Cases.Zip2005
