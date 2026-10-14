import Cases.Zip2005.Sinsemilla.PadNextIvkSpec
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Image.F_7801e110
import Cases.Zip2005.Sinsemilla.HasherKept
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro

/-!
# `from_iter`'s prologue (0x7801e110 to the loop head at byte 1)

The first `next` on the caller's block (bit 0), `__rust_alloc(8, 1)` (A4, this call's
instance) for the `Vec`'s first block, byte 0 stored, the `Vec` header `(8, ptr, 1)` in the
frame, the iterator block copied into the frame (`memcpy(_, _, 96)`), and the second `next`
(bit 1) on the copy.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_iter_ivk_pro {P : Prop} (s : MachineState) (sp sp0 out a1 ra : Word)
    (J A B Cb O : List Word) (j : Word) (hAl : A.length = 4) (hBl : B.length = 4)
    (hCbl : Cb.length = 12) (hCb : ivkState sp0 J j 0 = Cb) (hOl : O.length = 3)
    (hpc : s.pc = 0x7801e110#64) (hcode : CodeAt F_7801e110.base F_7801e110.prog s)
    (hcodeN : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra)
    (hsp : s.getReg .x2 = sp + 0xb0#64) (hstk : StackOk Ro.layout 0x1b0 sp) (hokFr : RegionOk Ro.layout.roBase Ro.layout.textHi sp 22)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hCbr : Region a1 Cb s) (hokCb : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hAr : Region (ptrA sp0) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4)
    (hBr : Region (ptrB sp0) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjSO : Disjoint sp 22 out 3) (hdjSC : Disjoint sp 22 a1 12)
    (hdjSA : Disjoint sp 22 (ptrA sp0) 4) (hdjSB : Disjoint sp 22 (ptrB sp0) 4)
    (hdjBA : Disjoint (sp + 0x18#64) 12 (ptrA sp0) 4) (hdjBB : Disjoint (sp + 0x18#64) 12 (ptrB sp0) 4)
    (hdjFBlk : Disjoint (sp - 0x10#64) 2 (sp + 0x18#64) 12)
    (hdjFC : Disjoint (sp - 0x10#64) 2 a1 12)
    (hdjFA : Disjoint (sp - 0x10#64) 2 (ptrA sp0) 4) (hdjFB : Disjoint (sp - 0x10#64) 2 (ptrB sp0) 4)
    (hdjF6A : Disjoint (sp - 0x30#64) 6 (ptrA sp0) 4) (hdjF6B : Disjoint (sp - 0x30#64) 6 (ptrB sp0) 4)
    (hdjF6C : Disjoint (sp - 0x30#64) 6 a1 12) (hdjF6O : Disjoint (sp - 0x30#64) 6 out 3)
    (hdjBC : Disjoint (sp + 0x18#64) 12 a1 12)
    (hdjOC : Disjoint out 3 a1 12) (hdjOA : Disjoint out 3 (ptrA sp0) 4) (hdjOB : Disjoint out 3 (ptrB sp0) 4)
    (hdjCA : Disjoint a1 12 (ptrA sp0) 4) (hdjCB : Disjoint a1 12 (ptrB sp0) 4)
    (hdjAB : Disjoint (ptrA sp0) 4 (ptrB sp0) 4)
    (hdjHA : Disjoint 0x78040620#64 14780694332 (ptrA sp0) 4)
    (hdjHB : Disjoint 0x78040620#64 14780694332 (ptrB sp0) 4)
    (hdjHO : Disjoint 0x78040620#64 14780694332 out 3)
    (hdjHC : Disjoint 0x78040620#64 14780694332 a1 12)
    -- the hasher's six regions (`T`): in the arena, held, kept by the allocator
    (T : HasherT) (hT : Kept6 T s) (hTA : Arena6 T) (hTO : Ok6 T)
    -- `__rust_alloc(8, 1)` (A4, this call's instance): a fresh word in the arena
    (halloc : ∀ (u : MachineState), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e184#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u → Region T.b6 T.L6 u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e184#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b2 138 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b6 516 ptr 1 → Safe P t) → Safe P u)
    (hunwrap_opt : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = s.code → Safe P u)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → Safe P u)
    (hk : ∀ (t : MachineState) (ptr w bit0 bit1 : Word) (I1 I2 : List Word), t.pc = 0x7801e230#64 →
      t.code = s.code →
      Unchanged [(sp - 0x30#64, 6), (sp, 22), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = ptr → t.getReg .x18 = 1#64 →
      t.getReg .x19 = 2#64 → bw (ivkBit A B 1) = bit1 → t.getReg .x20 = bit1 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      I2.length = 12 → ivkState sp0 J j (0 + 1 + 1) = I2 →
      Region sp ([8#64, ptr, 1#64] ++ I2 ++ [s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
        s.getReg .x9, s.getReg .x8, ra]) t →
      I1.length = 12 → Region a1 I1 t →
      Region out O t →
      bw (ivkBit A B 0) = bit0 → Region ptr [w] t → extractByte w 0 = BitVec.truncate 8 bit0 →
      RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 ≤ 0x1c00000000 →
      Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
      AsmVerif.RiscV.Sym.Disjoint T.b1 10 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b2 138 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b6 516 ptr 1 →
      Safe P t) :
    Safe P s := by
  have hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3 := hokFr.sub' 0 3 (by decide) (by simp)
  have hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 12 := hokFr.sub' 3 12 (by decide) rfl
  have hokSv : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x78#64) 7 := hokFr.sub' 15 7 (by decide) rfl
  have hokFr' : RegionOk Ro.layout.textLo Ro.layout.textHi sp 22 := hokFr.weaken (by decide) (by decide)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hstk10 : StackOk Ro.layout 0x10 sp := ⟨hstk.aligned, by have := hstk.lo; omega, hstk.hi⟩
  have hstk30 : StackOk Ro.layout 0x30 sp := ⟨hstk.aligned, by have := hstk.lo; omega, hstk.hi⟩
  have hu := Unchanged.refl [(sp - 0x30#64, 6), (sp, 22), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x30#64) 6 s
  obtain ⟨Fr, hFr, hFrl⟩ := Region.exists_junk sp 22 s
  have hK1 := hT.r1
  have hK2 := hT.r2
  have hK3 := hT.r3
  have hK4 := hT.r4
  have hK5 := hT.r5
  have hK6 := hT.r6
  have hlo1 := hTA.lo1
  have hhi1 := hTA.hi1
  have hlo2 := hTA.lo2
  have hhi2 := hTA.hi2
  have hlo3 := hTA.lo3
  have hhi3 := hTA.hi3
  have hlo4 := hTA.lo4
  have hhi4 := hTA.hi4
  have hlo5 := hTA.lo5
  have hhi5 := hTA.hi5
  have hlo6 := hTA.lo6
  have hhi6 := hTA.hi6
  have hO1 := hTO.ok1
  have hO2 := hTO.ok2
  have hO3 := hTO.ok3
  have hO4 := hTO.ok4
  have hO5 := hTO.ok5
  have hO6 := hTO.ok6
  have hl1 := T.l1
  have hl2 := T.l2
  have hl3 := T.l3
  have hl4 := T.l4
  have hl5 := T.l5
  have hl6 := T.l6
  have hCb' : ivkState sp0 J j 0 = [Cb[0]!, Cb[1]!, Cb[2]!, Cb[3]!, Cb[4]!, Cb[5]!, Cb[6]!, Cb[7]!, Cb[8]!, Cb[9]!, Cb[10]!, Cb[11]!] := by
    rw [hCb]; exact list12_cells Cb hCbl
  have hnext0 : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word) (k : Nat),
      ivkState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] → k < 510 →
      u.pc = 0x78021e7c#64 → CodeAt F_78021e7c.base F_78021e7c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e144#64 → u.getReg .x2 = sp → u.getReg .x10 = a1 →
      Region (a1) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] u → Region (ptrA sp0) A u → Region (ptrB sp0) B u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' bit : Word), t.pc = 0x7801e144#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x10#64, 2), (a1, 12)] u t →
        ivkState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region (a1) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
        bw (ivkBit A B k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → Safe P t) → Safe P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hA hB hk' =>
      pad_next_ivk_cells_spec u 0x7801e144#64 sp sp0 (a1) J A B i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 hAl hBl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk10 hsp0_lo hsp0_hi ha0 hI hokCb hA hokA hB hokB
        hdjCA hdjCB hdjFC hdjFA hdjFB hdjAB
        (fun u' h1 h2 => hunwrap_opt u' h1 (h2.trans hcodeEq)) hk'
  have hnext1 : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word) (k : Nat),
      ivkState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] → k < 510 →
      u.pc = 0x78021e7c#64 → CodeAt F_78021e7c.base F_78021e7c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e1bc#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] u → Region (ptrA sp0) A u → Region (ptrB sp0) B u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' bit : Word), t.pc = 0x7801e1bc#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x10#64, 2), (sp + 0x18#64, 12)] u t →
        ivkState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
        bw (ivkBit A B k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → Safe P t) → Safe P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hA hB hk' =>
      pad_next_ivk_cells_spec u 0x7801e1bc#64 sp sp0 (sp + 0x18#64) J A B i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 hAl hBl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk10 hsp0_lo hsp0_hi ha0 hI hokBlk hA hokA hB hokB
        hdjBA hdjBB hdjFBlk hdjFA hdjFB hdjAB
        (fun u' h1 h2 => hunwrap_opt u' h1 (h2.trans hcodeEq)) hk'
  have hO3 : O = [O[0]!, O[1]!, O[2]!] := by
    match O, hOl with
    | [_, _, _], _ => rfl
  -- the continuation over the frame's cells, as the executor states it
  have hk' : ∀ (t : MachineState) (ptr w bit0 bit1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : Word),
      t.pc = 0x7801e230#64 → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6), (sp, 22), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = ptr → t.getReg .x18 = 1#64 →
      t.getReg .x19 = 2#64 → bw (ivkBit A B 1) = bit1 → t.getReg .x20 = bit1 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      ivkState sp0 J j (0 + 1 + 1) = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] →
      Region sp [8#64, ptr, 1#64, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
        s.getReg .x9, s.getReg .x8, ra] t →
      Region a1 [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] t →
      Region out [O[0]!, O[1]!, O[2]!] t →
      bw (ivkBit A B 0) = bit0 → Region ptr [w] t → extractByte w 0 = BitVec.truncate 8 bit0 →
      RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 ≤ 0x1c00000000 →
      Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
      AsmVerif.RiscV.Sym.Disjoint T.b1 10 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b2 138 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b6 516 ptr 1 →
      Safe P t :=
    fun t ptr w bit0 bit1 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 hpc' hcode' hun hsp' hs0 hs1 hs2 hs3 hb1 hs4
        h3 h4 h22 h23 h24 h25 h26 h27 hI2 hR hR1 hO' hb0 hW hw hok hlo hhi hk1 hk2 hk3 hk4 hk5 hk6 hf1 hf2 hf3 hf4 hf5 hf6 =>
      hk t ptr w bit0 bit1 [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] hpc' hcode' hun hsp' hs0 hs1 hs2 hs3 hb1 hs4
        h3 h4 h22 h23 h24 h25 h26 h27 rfl hI2 hR rfl hR1 (by rw [hO3]; exact hO') hb0 hW hw hok hlo hhi hk1 hk2 hk3 hk4 hk5 hk6 hf1 hf2 hf3 hf4 hf5 hf6
  sym_exec [hnext0, hnext1, halloc, hhandle_rv, memcpy96_spec] stop [0x7801e230]
  sym_close hk' _ post26_0 v29 post13_12 post42_12 post13_0 post13_1 post13_2 post13_3 post13_4 post13_5 post13_6 post13_7 post13_8 post13_9 post13_10 post13_11 post42_0 post42_1 post42_2 post42_3 post42_4 post42_5 post42_6 post42_7 post42_8 post42_9 post42_10 post42_11
  all_goals first
    | rfl
    | assumption
    | (rw [← v29_def, extractByte_replaceByte _ _ (by decide)])

end Cases.Zip2005
