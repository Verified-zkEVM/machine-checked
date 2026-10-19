import Cases.Zip2005.Sinsemilla.PadIvkDefs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Image.F_78021e7c
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Pad<…>::next` (0x78021e7c), the first call

Position 0: the `Option<Empty>` tag is `1` (`Some(Empty)`, yielded and cleared on this call),
the inner cursor at bit 0 of `ak`'s words with 255 left. The call yields bit 0 and advances.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option machineChecked.sym.foldBytes true in
theorem pad_next_ivk_0_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (padIvkA sp J j 255#64 (ptrA sp) 0#8 1#64 0#64) s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 12)
    (hiter : iter.toNat + 8 * 12 ≤ 0x78040620)
    (hAr : Region (ptrA sp) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp) 4)
    (hBr : Region (ptrB sp) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp) 4)
    (hdjI : Disjoint iter 12 (ptrA sp) 4) (hdjI' : Disjoint iter 12 (ptrB sp) 4)
    (hdjS : Disjoint (spn - 0x10#64) 2 iter 12) (hdjSA : Disjoint (spn - 0x10#64) 2 (ptrA sp) 4)
    (hdjSB : Disjoint (spn - 0x10#64) 2 (ptrB sp) 4) (hdjAB : Disjoint (ptrA sp) 4 (ptrB sp) 4)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter (padIvkA sp J j 254#64 (ptrA sp) 1#8 0#64 1#64) t →
      t.getReg .x10 = bw (wordsBit A 0) → SafeN G n P t) :
    SafeN G n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(spn - 0x10#64, 2), (iter, 12)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x10#64) 2 s
  have hTag := ivkTag_byte1 J
  have hHd := ivkEndA_head sp J 0#8
  have hEA1 := ivkEndA_byte sp J 0#8 1 (by decide)
  have hEA2 := ivkEndA_byte sp J 0#8 2 (by decide)
  have hEA3 := ivkEndA_byte sp J 0#8 3 (by decide)
  have hEA4 := ivkEndA_byte sp J 0#8 4 (by decide)
  have hEA5 := ivkEndA_byte sp J 0#8 5 (by decide)
  have hEA6 := ivkEndA_byte sp J 0#8 6 (by decide)
  have hEA7 := ivkEndA_byte sp J 0#8 7 (by decide)
  have hEA2_0 := ivkEndA2_byte0 sp J
  have hEA2_1 := ivkEndA2_byte1 sp J
  have hpB0 : (ptrB sp == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpA0 : (ptrA sp == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, ptrA]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpe : ptrA sp ≠ ptrB sp := by
    simp only [ptrA, ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hA4 : [A[0]!, A[1]!, A[2]!, A[3]!] = A := by
    match A, hAl with
    | [_, _, _, _], _ => rfl
  sym_exec [hunwrap_opt]
  all_goals (first
    -- the inner range is not exhausted
    | (exfalso; sym_subst; rw [bytes_word, seqz_or_xor _ _ _ hpe] at hbr86; exact hbr86 (by decide))
    | skip)
  -- the live path: the tag cleared, the head bit 1, bit 0 of `ak`
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter [0#64, j, 255#64, ptrB sp, ivkEndB sp J, ivkEndB2 sp J, 254#64, ptrA sp, v103,
        ivkEndA2 sp J, v91, 1#64] t →
      t.getReg .x10 = v112 → SafeN G n P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 (Region.of_eq h5 ?_) ?_
    · simp only [padIvkA, List.cons.injEq, and_true, true_and, eq_self]
      refine ⟨?_, ?_⟩
      · rw [← v103_def, replaceByte_replaceByte _ _ (by decide)]; rfl
      · rw [← v91_def, replaceByte_replaceByte _ _ (by decide)]
    · rw [h6, ← v112_def, ← v111_def, ← v105_def, BitVec.ushiftRight_zero, wordsBit, Nat.zero_div,
        Nat.zero_mod, BitVec.ushiftRight_zero]
      exact bitVal _
  sym_close hk'

end Cases.Zip2005
