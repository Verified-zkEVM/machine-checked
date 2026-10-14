import Cases.Zip2005.Sinsemilla.PadIvkDefs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Image.F_78021e7c
import Cases.Zip2005.Image.Ro

/-!
# `Pad<…>::next` (0x78021e7c), the phase changes

Position 255: the inner `Take` is spent (count 0); the chain marks it exhausted (tag 2) and the
outer cursor yields bit 0 of `nk`. Position 510: the outer `Take` is spent too; `Pad` computes
its padding (`510 % 10 = 0`, none) and the call yields `None` (2), leaving `padding_left`
as `(Some, 0)`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option asmverif.sym.foldBytes true in
theorem pad_next_ivk_255_spec {P : Prop} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (padIvkA sp J j 0#64 (ptrA sp + 24#64) 63#8 0#64 255#64) s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 12)
    (hAr : Region (ptrA sp) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp) 4)
    (hBr : Region (ptrB sp) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp) 4)
    (hdjI : Disjoint iter 12 (ptrA sp) 4) (hdjI' : Disjoint iter 12 (ptrB sp) 4)
    (hdjS : Disjoint (spn - 0x10#64) 2 iter 12) (hdjSA : Disjoint (spn - 0x10#64) 2 (ptrA sp) 4)
    (hdjSB : Disjoint (spn - 0x10#64) 2 (ptrB sp) 4) (hdjAB : Disjoint (ptrA sp) 4 (ptrB sp) 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter (padIvkB sp J j 254#64 (ptrB sp) 1#8 256#64) t →
      t.getReg .x10 = bw (wordsBit B 0) → Safe P t) :
    Safe P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(spn - 0x10#64, 2), (iter, 12)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x10#64) 2 s
  have hTag := ivkTag_byte0 J
  have hHdA := ivkEndA_head sp J 63#8
  have hEA1 := ivkEndA_byte sp J 63#8 1 (by decide)
  have hEA2 := ivkEndA_byte sp J 63#8 2 (by decide)
  have hEA3 := ivkEndA_byte sp J 63#8 3 (by decide)
  have hEA4 := ivkEndA_byte sp J 63#8 4 (by decide)
  have hEA5 := ivkEndA_byte sp J 63#8 5 (by decide)
  have hEA6 := ivkEndA_byte sp J 63#8 6 (by decide)
  have hEA7 := ivkEndA_byte sp J 63#8 7 (by decide)
  have hEA2_0 := ivkEndA2_byte0 sp J
  have hEA2_1 := ivkEndA2_byte1 sp J
  have hHdB := ivkEndB_head0 sp J
  have hEB1 := ivkEndB_byte0 sp J 1 (by decide)
  have hEB2 := ivkEndB_byte0 sp J 2 (by decide)
  have hEB3 := ivkEndB_byte0 sp J 3 (by decide)
  have hEB4 := ivkEndB_byte0 sp J 4 (by decide)
  have hEB5 := ivkEndB_byte0 sp J 5 (by decide)
  have hEB6 := ivkEndB_byte0 sp J 6 (by decide)
  have hEB7 := ivkEndB_byte0 sp J 7 (by decide)
  have hEB2_0 := ivkEndB2_byte0 sp J
  have hEB2_1 := ivkEndB2_byte1 sp J
  have hpA24 : sp + 18446744073709551424#64 ≠ 0#64 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpA24' : (sp + 18446744073709551424#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, hpA24, not_false_eq_true]
  have hpB0 : (ptrB sp == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpeA : sp + 18446744073709551424#64 ≠ ptrB sp := by
    simp only [ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpeB : sp + 18446744073709551432#64 ≠ endB sp := by
    simp only [endB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hB4 : [B[0]!, B[1]!, B[2]!, B[3]!] = B := by
    match B, hBl with
    | [_, _, _, _], _ => rfl
  sym_exec
  all_goals (first
    -- the inner range is not exhausted
    | (exfalso; sym_subst; rw [bytes_word, seqz_or_xor _ _ _ hpeA] at hbr86; exact hbr86 (by decide))
    -- the outer range is not exhausted
    | (exfalso; sym_subst; rw [bytes_word, seqz_or_xor _ _ _ hpeB] at hbr97; exact hbr97 (by decide))
    | skip)
  -- the live path: the tag set to 2, the outer cursor stepped, bit 0 of `nk`
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter [0#64, j, 254#64, ptrB sp, v106, ivkEndB2 sp J, 0#64, ptrA sp + 24#64,
        replaceByte (ivkEndA sp J) 0 63#8, ivkEndA2 sp J, v93, 256#64] t →
      t.getReg .x10 = v115 → Safe P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 (Region.of_eq h5 ?_) ?_
    · simp only [padIvkB, List.cons.injEq, and_true, true_and, eq_self]
      refine ⟨?_, ?_⟩
      · rw [← v106_def]; rfl
      · rw [← v93_def, replaceByte_replaceByte _ _ (by decide)]
    · rw [h6, ← v115_def, ← v114_def, ← v108_def, BitVec.ushiftRight_zero, wordsBit, Nat.zero_div,
        Nat.zero_mod, BitVec.ushiftRight_zero]
      exact bitVal _
  sym_close hk'

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option asmverif.sym.foldBytes true in
theorem pad_next_ivk_510_spec {P : Prop} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (padIvkB sp J j 0#64 (ptrB sp + 24#64) 63#8 510#64) s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 12)
    (hAr : Region (ptrA sp) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp) 4)
    (hBr : Region (ptrB sp) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp) 4)
    (hdjI : Disjoint iter 12 (ptrA sp) 4) (hdjI' : Disjoint iter 12 (ptrB sp) 4)
    (hdjS : Disjoint (spn - 0x10#64) 2 iter 12) (hdjSA : Disjoint (spn - 0x10#64) 2 (ptrA sp) 4)
    (hdjSB : Disjoint (spn - 0x10#64) 2 (ptrB sp) 4) (hdjAB : Disjoint (ptrA sp) 4 (ptrB sp) 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter [1#64, 0#64, 0#64, ptrB sp + 24#64, replaceByte (ivkEndB sp J) 0 63#8, ivkEndB2 sp J,
        0#64, ptrA sp + 24#64, replaceByte (ivkEndA sp J) 0 63#8, ivkEndA2 sp J,
        replaceByte J[8]! 0 (BitVec.truncate 8 2#64), 510#64] t →
      t.getReg .x10 = 2#64 → Safe P t) :
    Safe P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(spn - 0x10#64, 2), (iter, 12)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x10#64) 2 s
  have hTag := ivkTag_byte2 J
  have hHdA := ivkEndA_head sp J 63#8
  have hEA1 := ivkEndA_byte sp J 63#8 1 (by decide)
  have hEA2 := ivkEndA_byte sp J 63#8 2 (by decide)
  have hEA3 := ivkEndA_byte sp J 63#8 3 (by decide)
  have hEA4 := ivkEndA_byte sp J 63#8 4 (by decide)
  have hEA5 := ivkEndA_byte sp J 63#8 5 (by decide)
  have hEA6 := ivkEndA_byte sp J 63#8 6 (by decide)
  have hEA7 := ivkEndA_byte sp J 63#8 7 (by decide)
  have hEA2_0 := ivkEndA2_byte0 sp J
  have hEA2_1 := ivkEndA2_byte1 sp J
  have hHdB := ivkEndB_head sp J 63#8
  have hEB1 := ivkEndB_byte sp J 63#8 1 (by decide)
  have hEB2 := ivkEndB_byte sp J 63#8 2 (by decide)
  have hEB3 := ivkEndB_byte sp J 63#8 3 (by decide)
  have hEB4 := ivkEndB_byte sp J 63#8 4 (by decide)
  have hEB5 := ivkEndB_byte sp J 63#8 5 (by decide)
  have hEB6 := ivkEndB_byte sp J 63#8 6 (by decide)
  have hEB7 := ivkEndB_byte sp J 63#8 7 (by decide)
  have hEB2_0 := ivkEndB2_byte0 sp J
  have hEB2_1 := ivkEndB2_byte1 sp J
  have hpA24 : sp + 18446744073709551424#64 ≠ 0#64 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpA24' : (sp + 18446744073709551424#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, hpA24, not_false_eq_true]
  have hpB24 : sp + 18446744073709551456#64 ≠ 0#64 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpB24' : (sp + 18446744073709551456#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, hpB24, not_false_eq_true]
  have hpeA : sp + 18446744073709551424#64 ≠ ptrB sp := by
    simp only [ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  sym_exec
  all_goals (first
    -- the inner range is not exhausted
    | (exfalso; sym_subst; rw [bytes_word, seqz_or_xor _ _ _ hpeA] at hbr86; exact hbr86 (by decide))
    | skip)
  -- `Pad`'s padding: `510 % 10 = 0`, none
  all_goals (
    have h52 : v52 = 0#64 := by
      rw [← v52_def, ← v50_def, ← v49_def, ← v47_def, ← v46_def, ← v45_def, ← v44_def, ← v43_def,
        ← v42_def]
      decide
    first
    | (rw [h52] at hbr93; exact absurd hbr93 (by decide))
    | skip)
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter [1#64, v52, 0#64, ptrB sp + 24#64, replaceByte (ivkEndB sp J) 0 63#8, ivkEndB2 sp J,
        0#64, ptrA sp + 24#64, replaceByte (ivkEndA sp J) 0 63#8, ivkEndA2 sp J,
        replaceByte J[8]! 0 (BitVec.truncate 8 2#64), 510#64] t →
      t.getReg .x10 = 2#64 → Safe P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 (Region.of_eq h5 ?_) h6
    rw [h52]
  sym_close hk'

end Cases.Zip2005
