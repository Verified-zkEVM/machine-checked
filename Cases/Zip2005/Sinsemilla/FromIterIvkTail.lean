import Cases.Zip2005.Sinsemilla.PadNextIvkSpec
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_7801e110
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-!
# `from_iter`'s last word and exit (0x7801e230 at byte 504)

Bytes 504–509 of the `Vec` (word 63), then call 510 yields `None`: the `Vec` header is copied
to the output, the frame restored, and `from_iter` returns.
-/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_iter_ivk_tail {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp sp0 out p bit0 w w64 : Word)
    (J A B I O : List Word) (j : Word) (hAl : A.length = 4) (hBl : B.length = 4) (hOl : O.length = 3)
    (hIl : I.length = 12) (hIv : ivkState sp0 J j 505 = I)
    (rav s0v s1v s2v s3v s4v s5v : Word) (hra1 : rav &&& ~~~1#64 = rav)
    (hpc : s.pc = 0x7801e230#64) (hcode : CodeAt F_7801e110.base F_7801e110.prog s)
    (hcodeN : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    -- the run's heap invariant, the `Vec`'s block live; the output header below the heap
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt ((p, 64) :: L) s)
    (hplo : 0x78048980 ≤ p.toNat) (hphi : p.toNat + 8 * 65 ≤ 0x1c00000000)
    (hout : out.toNat + 8 * 3 ≤ 0x78040620)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x100 sp)
    (hs0 : s.getReg .x8 = out) (hs1 : s.getReg .x9 = p) (hs2 : s.getReg .x18 = 504#64)
    (hs3 : s.getReg .x19 = 2#64) (hbit0 : bw (ivkBit A B 504) = bit0) (hs4 : s.getReg .x20 = bit0)
    (hV : Region sp [512#64, p, 504#64] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3)
    (hBlk : Region (sp + 0x18#64) I s)
    (hokBlk : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 12)
    (hF : Region (sp + 0x78#64) [s5v, s4v, s3v, s2v, s1v, s0v, rav] s)
    (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x78#64) 7)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hW : Region (p + 504#64) [w, w64] s) (hokW : RegionOk Ro.layout.roBase Ro.layout.textHi (p + 504#64) 2)
    (hAr : Region (ptrA sp0) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4)
    (hBr : Region (ptrB sp0) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjBA : Disjoint (sp + 0x18#64) 12 (ptrA sp0) 4) (hdjBB : Disjoint (sp + 0x18#64) 12 (ptrB sp0) 4)
    (hdjFA : Disjoint (sp - 0x10#64) 2 (ptrA sp0) 4) (hdjFB : Disjoint (sp - 0x10#64) 2 (ptrB sp0) 4)
    (hdjAB : Disjoint (ptrA sp0) 4 (ptrB sp0) 4)
    (hdjFBlk : Disjoint (sp - 0x10#64) 2 (sp + 0x18#64) 12)
    (hdjFW : Disjoint (sp - 0x10#64) 2 (p + 504#64) 2) (hdjSW : Disjoint sp 22 (p + 504#64) 2)
    (hdjWA : Disjoint (p + 504#64) 2 (ptrA sp0) 4) (hdjWB : Disjoint (p + 504#64) 2 (ptrB sp0) 4)
    (hdjOS : Disjoint out 3 sp 22) (hdjOW : Disjoint out 3 (p + 504#64) 2)
    (hdjFO : Disjoint (sp - 0x10#64) 2 out 3)
    (hdjOA : Disjoint out 3 (ptrA sp0) 4) (hdjOB : Disjoint out 3 (ptrB sp0) 4)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ (t : MachineState) (I' : List Word) (w' : Word), t.pc = rav → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + 504#64, 2), (out, 3)] s t →
      t.getReg .x2 = sp + 0xb0#64 → t.getReg .x8 = s0v → t.getReg .x9 = s1v → t.getReg .x18 = s2v →
      t.getReg .x19 = s3v → t.getReg .x20 = s4v → t.getReg .x21 = s5v →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x22 = s.getReg .x22 → t.getReg .x23 = s.getReg .x23 → t.getReg .x24 = s.getReg .x24 →
      t.getReg .x25 = s.getReg .x25 → t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = s.getReg .x27 →
      Region out [512#64, p, 510#64] t → Region sp [512#64, p, 510#64] t →
      I'.length = 12 → ivkState sp0 J j 511 = I' → Region (sp + 0x18#64) I' t →
      Region (p + 504#64) [w', w64] t →
      (∀ b, b < 6 → extractByte w' b = BitVec.truncate 8 (bw (ivkBit A B (504 + b)))) →
      RoImage Ro.layout t → Run.HeapAt ((p, 64) :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + 504#64, 2), (out, 3)] s
  have hlo := hstk.lo
  have hstk10 : StackOk Ro.layout 0x10 sp := ⟨hstk.aligned, by have := hstk.lo; omega, hstk.hi⟩
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hIv' : ivkState sp0 J j 505 = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!] := by
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
        hcode hcw hro' hheap' hra (by decide) hsp' hstk10 hsp0_lo hsp0_hi ha0 hI hokBlk hiterB hA hokA hB hokB hdjBA hdjBB
        hdjFBlk hdjFA hdjFB hdjAB (fun u' sp'' L'' h1 h2 => hunwrap_opt u' sp'' L'' h1 (h2.trans hcodeEq)) hk'
  -- call 510: `None`
  have hend : ∀ (u : MachineState) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word) (L' : List (Word × Nat)),
      ivkState sp0 J j 510 = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] →
      u.pc = 0x78021e7c#64 → CodeAt F_78021e7c.base F_78021e7c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.code = s.code →
      u.getReg .x1 = 0x7801e228#64 → u.getReg .x2 = sp → u.getReg .x10 = sp + 0x18#64 →
      Region (sp + 0x18#64) [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] u → Region (ptrA sp0) A u → Region (ptrB sp0) B u →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' : Word), t.pc = 0x7801e228#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x10#64, 2), (sp + 0x18#64, 12)] u t →
        ivkState sp0 J j 511 = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region (sp + 0x18#64) [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
        t.getReg .x10 = 2#64 → SafeN G n P t) → SafeN G n P u :=
    fun u i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 L' hIv hpc hcode hcw hcodeEq hra hsp' ha0 hI hA hB hro' hheap' hk' =>
      pad_next_ivk_end_cells_spec (L := L') u 0x7801e228#64 sp sp0 (sp + 0x18#64) J A B i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 hAl hBl j hIv hpc
        hcode hcw hro' hheap' hra (by decide) hsp' hstk10 hsp0_lo hsp0_hi ha0 hI hokBlk hiterB hA hokA hB hokB hdjBA hdjBB
        hdjFBlk hdjFA hdjFB hdjAB (fun u' sp'' L'' h1 h2 => hunwrap_opt u' sp'' L'' h1 (h2.trans hcodeEq)) hk'
  sym_exec [hnext, hend]
  sym_close hk _ _ v63
  · -- bytes 504–509 of the `Vec`: the bits
    intro b hb6
    rw [← v63_def, ← v51_def, ← v39_def, ← v27_def, ← v15_def, ← v3_def, ← hbit0,
      ← post9_19, ← post21_19, ← post33_19, ← post45_19, ← post57_19]
    interval_cases b <;>
      simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte, Nat.add_zero]
  · rfl

end Cases.Zip2005
