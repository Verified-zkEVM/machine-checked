import Cases.Zip2005.Sinsemilla.PadNextIvkSpec
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_7801e110
import Cases.Zip2005.Sinsemilla.HasherKept
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-!
# `from_iter`'s `Vec` growth (0x7801e230, `len == cap`)

At the loop head with the `Vec` full (`cap = C`), `RawVecInner::reserve::do_reserve_and_handle`
doubles it (the A5 contract `hreserve`, this call's instance), the byte `C` goes into the new
block's word `C / 8`, and one more `next` yields bit `C + 1`.
-/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_iter_ivk_grow {P : Prop} (s : MachineState) (sp sp0 out p bit0 : Word)
    (J A B I W : List Word) (j : Word) (hAl : A.length = 4) (hBl : B.length = 4)
    (C : Nat) (hC : C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256)
    (hIl : I.length = 12) (hIv : ivkState sp0 J j (C + 1) = I) (hWl : W.length = C / 8)
    (hpc : s.pc = 0x7801e230#64) (hcode : CodeAt F_7801e110.base F_7801e110.prog s)
    (hcodeN : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x100 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = BitVec.ofNat 64 C)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (ivkBit A B C) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 12)
    (hW : Region p W s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi p (C / 8))
    (hp_lo : 0x78048980 ≤ p.toNat) (hp_hi : p.toNat + C ≤ 0x1c00000000)
    (hAr : Region (ptrA sp0) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4)
    (hBr : Region (ptrB sp0) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjBA : Disjoint (sp + 0x18#64) 12 (ptrA sp0) 4) (hdjBB : Disjoint (sp + 0x18#64) 12 (ptrB sp0) 4)
    (hdjFA : Disjoint (sp - 0x10#64) 2 (ptrA sp0) 4) (hdjFB : Disjoint (sp - 0x10#64) 2 (ptrB sp0) 4)
    (hdjF32A : Disjoint (sp - 0x100#64) 32 (ptrA sp0) 4) (hdjF32B : Disjoint (sp - 0x100#64) 32 (ptrB sp0) 4)
    (hdjAB : Disjoint (ptrA sp0) 4 (ptrB sp0) 4)
    (hdjFBlk : Disjoint (sp - 0x10#64) 2 (sp + 0x18#64) 12)
    (hdjHA : Disjoint 0x78040620#64 14780694332 (ptrA sp0) 4)
    (hdjHB : Disjoint 0x78040620#64 14780694332 (ptrB sp0) 4)
    (hdjHS : Disjoint 0x78040620#64 14780694332 (sp - 0x100#64) 54)
    -- the hasher's six regions (`T`): in the arena, held, kept by the allocator
    (T : HasherT) (hT : Kept6 T s) (hTA : Arena6 T) (hTO : Ok6 T)
    -- `do_reserve_and_handle(&vec, C, 1, 1, 1)` (A5, this call's instance): the block doubled,
    -- its contents copied, one word past the block readable
    (hreserve : ∀ (u : MachineState) (W : List Word), W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = s.code → u.getReg .x1 = 0x7801e254#64 → u.getReg .x2 = sp →
      StackOk Ro.layout 0x100 sp → u.getReg .x10 = sp → u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u → Region T.b6 T.L6 u →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x7801e254#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → Safe P t) → Safe P u)
    (hunwrap_opt : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = s.code → Safe P u)
    (hk : ∀ (t : MachineState) (p' : Word) (V I' : List Word) (bit' : Word), t.pc = 0x7801e230#64 →
      t.code = s.code →
      Unchanged [(sp - 0x100#64, 32), (sp, 3), (sp + 0x18#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = p' → t.getReg .x18 = BitVec.ofNat 64 (C + 1) →
      t.getReg .x19 = 2#64 → bw (ivkBit A B (C + 1)) = bit' → t.getReg .x20 = bit' →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 (C + 1)] t →
      I'.length = 12 → ivkState sp0 J j (C + 1 + 1) = I' → Region (sp + 0x18#64) I' t →
      V.length = C / 4 + 1 → Region p' V t → (∀ i, i < C / 8 → V[i]! = W[i]!) →
      extractByte V[C / 8]! 0 = BitVec.truncate 8 bit0 →
      RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) → 0x78048980 ≤ p'.toNat →
      p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
      Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
      AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → Safe P t) :
    Safe P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x100#64) 32 := hstk.frame 32 (by decide)
  have hu := Unchanged.refl [(sp - 0x100#64, 32), (sp, 3), (sp + 0x18#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hstk10 : StackOk Ro.layout 0x10 sp := ⟨hstk.aligned, by have := hstk.lo; omega, hstk.hi⟩
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x100#64) 32 s
  have hK1 := hT.r1
  have hK2 := hT.r2
  have hK3 := hT.r3
  have hK4 := hT.r4
  have hK5 := hT.r5
  have hK6 := hT.r6
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
  have hdF : Away6 (sp - 0x100#64) 32 T := Away6.of_heap hTA (hdjHS.sub_right (self_add_zero _) (by omega))
  have hdV : Away6 sp 3 T := Away6.of_heap hTA (hdjHS.sub_right (fl_0 sp) (by omega))
  have hdB : Away6 (sp + 0x18#64) 12 T := Away6.of_heap hTA (hdjHS.sub_right (fl_18 sp) (by omega))
  have hdF1 := hdF.d1
  have hdF2 := hdF.d2
  have hdF3 := hdF.d3
  have hdF4 := hdF.d4
  have hdF5 := hdF.d5
  have hdF6 := hdF.d6
  have hdV1 := hdV.d1
  have hdV2 := hdV.d2
  have hdV3 := hdV.d3
  have hdV4 := hdV.d4
  have hdV5 := hdV.d5
  have hdV6 := hdV.d6
  have hdB1 := hdB.d1
  have hdB2 := hdB.d2
  have hdB3 := hdB.d3
  have hdB4 := hdB.d4
  have hdB5 := hdB.d5
  have hdB6 := hdB.d6
  have hIv' : ivkState sp0 J j (C + 1) = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!] := by
    rw [hIv]; exact list12_cells I hIl
  -- `Pad::next` at this call site, the message fixed
  have hnext : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word) (k : Nat),
      ivkState sp0 J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] → k < 510 →
      u.pc = 0x78021e7c#64 → CodeAt F_78021e7c.base F_78021e7c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e228#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] u → Region (ptrA sp0) A u → Region (ptrB sp0) B u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' bit : Word), t.pc = 0x7801e228#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x10#64, 2), (sp + 0x18#64, 12)] u t →
        ivkState sp0 J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
        bw (ivkBit A B k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
        t.getReg .x10 = bit → Safe P t) → Safe P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hA hB hk' =>
      pad_next_ivk_cells_spec u 0x7801e228#64 sp sp0 (sp + 0x18#64) J A B i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 hAl hBl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk10 hsp0_lo hsp0_hi ha0 hI hokBlk hA hokA hB hokB hdjBA hdjBB
        hdjFBlk hdjFA hdjFB hdjAB (fun u' h1 h2 => hunwrap_opt u' h1 (h2.trans hcodeEq)) hk'
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · sym_exec [hreserve, hnext] stop [0x7801e230]
    sym_close hk _ post9_0 _ _ post19_12
    all_goals first
      | rfl
      | assumption
      | (intro i hi; interval_cases i <;>
          (simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
           simp only [← acc9_1_def, List.cons_append, List.nil_append, List.getElem!_cons_succ,
             List.getElem!_cons_zero]))
      | (simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.reduceDiv, ← v13_def]
         rw [extractByte_replaceByte _ _ (by decide)])

end Cases.Zip2005
