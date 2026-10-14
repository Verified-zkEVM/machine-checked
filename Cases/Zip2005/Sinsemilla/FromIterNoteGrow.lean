import Cases.Zip2005.Sinsemilla.FromIterNoteKit
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_7801dfb4
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-!
# `from_iter`'s `Vec` growth (0x7801e0d4, `len == cap`)

At the loop head with the `Vec` full (`cap = C`), `RawVecInner::reserve::do_reserve_and_handle`
doubles it (the A5 contract `hreserve`, this call's instance), the byte `C` goes into the new
block's word `C / 8`, and one more `next` yields bit `C + 1`.
-/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_iter_note_grow {P : Prop} (s : MachineState) (sp sp0 out v p bit0 : Word)
    (J G K R Q I W : List Word) (j : Word) (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4)
    (C : Nat) (hC : C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024)
    (hIl : I.length = 18) (hIv : noteState sp0 J j (C + 1) = I) (hWl : W.length = C / 8)
    (hpc : s.pc = 0x7801e0d4#64) (hcode : CodeAt F_7801dfb4.base F_7801dfb4.prog s)
    (hcodeN : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x180 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = BitVec.ofNat 64 C)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (noteBit G K v R Q C) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 18)
    (hW : Region p W s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi p (C / 8))
    (hp_lo : 0x78048980 ≤ p.toNat) (hp_hi : p.toNat + C ≤ 0x1c00000000)
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
    (hdjHG : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551408#64) 4)
    (hdjHK : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551440#64) 4)
    (hdjHV : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551472#64) 1)
    (hdjHR : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551480#64) 4)
    (hdjHQ : Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551512#64) 4)
    (hdjHS : Disjoint 0x78040620#64 14780694332 (sp - 0x180#64) 76)
    -- `do_reserve_and_handle(&vec, C, 1, 1, 1)` (A5, this call's instance): the block doubled,
    -- its contents copied, one word past the block readable
    (hreserve : ∀ (u : MachineState) (W : List Word), W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = s.code → u.getReg .x1 = 0x7801e0f8#64 → u.getReg .x2 = sp →
      StackOk Ro.layout 0x100 sp → u.getReg .x10 = sp → u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x7801e0f8#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 → Safe P t) → Safe P u)
    (hk : ∀ (t : MachineState) (p' : Word) (V I' : List Word) (bit' : Word), t.pc = 0x7801e0d4#64 →
      t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = out → t.getReg .x9 = p' → t.getReg .x18 = BitVec.ofNat 64 (C + 1) →
      t.getReg .x19 = 2#64 → bw (noteBit G K v R Q (C + 1)) = bit' → t.getReg .x20 = bit' →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 (C + 1)] t →
      I'.length = 18 → noteState sp0 J j (C + 1 + 1) = I' → Region (sp + 0x18#64) I' t →
      V.length = C / 4 + 1 → Region p' V t → (∀ i, i < C / 8 → V[i]! = W[i]!) →
      extractByte V[C / 8]! 0 = BitVec.truncate 8 bit0 →
      RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) → 0x78048980 ≤ p'.toNat →
      p'.toNat + 2 * C + 8 ≤ 0x1c00000000 → Safe P t) :
    Safe P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hu := Unchanged.refl [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x180#64) 48 s
  have hIv' : noteState sp0 J j (C + 1) = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!, I[12]!, I[13]!, I[14]!, I[15]!, I[16]!, I[17]!] := by
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
        t.getReg .x10 = bit → Safe P t) → Safe P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 k hIv hk hpc hcode hcw hcodeEq hra hsp' ha0 hI hG hK hV hR hQ hk' =>
      pad_next_note_cells_spec u 0x7801e0cc#64 sp sp0 (sp + 0x18#64) v J G K R Q i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 hGl hKl hRl hQl j k hIv hk hpc
        hcode hcw hra (by decide) hsp' hstk hsp0_lo hsp0_hi ha0 hI hokBlk hG hokG hK hokK hV hokVv hR hokR hQ hokQ hdjBG hdjBK hdjBV hdjBR hdjBQ
        hdjFBlk hdjFG hdjFK hdjFV hdjFR hdjFQ hk'
  have hleft : ∀ (W W' : List Word) (i : Nat), i < W.length → (W ++ W')[i]! = W[i]! := by
    intro W W' i h
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · sym_exec [hreserve, hnext] stop [0x7801e0d4]
    sym_close hk _ post9_0 _ _ post19_18
    all_goals first
      | rfl
      | (intro i hi; interval_cases i <;>
          (simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
           simp only [← acc9_1_def, List.cons_append, List.nil_append, List.getElem!_cons_succ,
             List.getElem!_cons_zero]
           -- the 1024 case: the old block stays symbolic
           try exact hleft _ _ _ (by omega)))
      | (simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.reduceDiv, ← v13_def]
         rw [extractByte_replaceByte _ _ (by decide)])

end Cases.Zip2005
