import Cases.Zip2005.Sinsemilla.PadIvkDefs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Image.F_78021e7c
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Pad<…>::next` (0x78021e7c), phase B

One `next` at position `255 + m`, `1 ≤ m ≤ 254`: the inner chain is exhausted (tag 2, its
cursor at bit 255 of `ak`'s words) and the outer cursor (`nk`'s bits) has `255 - m` left at
bit `m`. The call yields bit `m` of `nk` and advances the outer cursor.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option machineChecked.sym.foldBytes true in
theorem pad_next_ivk_b_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4)
    (m : Nat) (hm1 : 1 ≤ m) (hm254 : m ≤ 254) (j nB pB : Word) (hB : BitVec 8)
    (hnB : BitVec.ofNat 64 (255 - m) = nB) (hpB : pB = ptrB sp + BitVec.ofNat 64 (8 * (m / 64)))
    (hhB : BitVec.ofNat 8 (m % 64) = hB)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (padIvkB sp J j nB pB hB (BitVec.ofNat 64 (255 + m))) s)
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
      Region iter (padIvkB sp J j (BitVec.ofNat 64 (255 - (m + 1)))
        (ptrB sp + BitVec.ofNat 64 (8 * ((m + 1) / 64))) (BitVec.ofNat 8 ((m + 1) % 64))
        (BitVec.ofNat 64 (255 + (m + 1)))) t →
      t.getReg .x10 = bw (wordsBit B m) → SafeN G n P t) :
    SafeN G n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(spn - 0x10#64, 2), (iter, 12)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x10#64) 2 s
  -- the loaded bytes of the block's constant words, as the executor rewrites them
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
  have hHdB := ivkEndB_head sp J hB
  have hEB1 := ivkEndB_byte sp J hB 1 (by decide)
  have hEB2 := ivkEndB_byte sp J hB 2 (by decide)
  have hEB3 := ivkEndB_byte sp J hB 3 (by decide)
  have hEB4 := ivkEndB_byte sp J hB 4 (by decide)
  have hEB5 := ivkEndB_byte sp J hB 5 (by decide)
  have hEB6 := ivkEndB_byte sp J hB 6 (by decide)
  have hEB7 := ivkEndB_byte sp J hB 7 (by decide)
  have hEB2_0 := ivkEndB2_byte0 sp J
  have hEB2_1 := ivkEndB2_byte1 sp J
  -- the pointers are not null, the count not zero, the cursors short of their ends
  have hpA24 : sp + 18446744073709551424#64 ≠ 0#64 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpA24' : (sp + 18446744073709551424#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, hpA24, not_false_eq_true]
  have hpB0 : (sp + (18446744073709551432#64 + BitVec.ofNat 64 (8 * (m / 64))) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add] at this
    rw [Bn.toNat_ofNat' (8 * (m / 64))] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hnB0 : nB ≠ 0#64 := by
    rw [← hnB]
    intro h
    have := congrArg BitVec.toNat h
    rw [Bn.toNat_ofNat'] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpeA : sp + 18446744073709551424#64 ≠ ptrB sp := by
    simp only [ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpeB : sp + (18446744073709551432#64 + BitVec.ofNat 64 (8 * (m / 64))) ≠ endB sp := by
    simp only [endB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add] at this
    rw [Bn.toNat_ofNat' (8 * (m / 64))] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hB4 : [B[0]!, B[1]!, B[2]!, B[3]!] = B := by
    match B, hBl with
    | [_, _, _, _], _ => rfl
  sym_exec [hunwrap_opt]
  all_goals (first
    -- the outer cursor is not null
    | (simp only [← v6_def, hpB0] at hbr85; exact absurd hbr85 (by decide))
    -- the inner range is not exhausted
    | (exfalso; sym_subst; rw [bytes_word, seqz_or_xor _ _ _ hpeA] at hbr86; exact hbr86 (by decide))
    -- the outer range is not exhausted
    | (exfalso; sym_subst; rw [bytes_word, seqz_or_xor _ _ _ hpeB] at hbr92; exact hbr92 (by decide))
    | skip)
  -- the live path: the block's new cells and the bit, as the executor left them
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter [0#64, j, nB + 18446744073709551615#64, v97, v101, ivkEndB2 sp J, 0#64,
        ptrA sp + 24#64, replaceByte (ivkEndA sp J) 0 63#8, ivkEndA2 sp J,
        replaceByte J[8]! 0 (BitVec.truncate 8 2#64), v37 + 1#64] t →
      t.getReg .x10 = v110 → SafeN G n P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 (Region.of_eq h5 ?_) ?_
    · simp only [padIvkB, List.cons.injEq, and_true, true_and, eq_self]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← hnB]; exact countNext m hm254
      · rw [← v97_def, ← v96_def, ← v95_def, ← v93_def, ← v7_def, ← v6_def, ← hhB,
          ptrStep (m % 64) (Nat.mod_lt _ (by decide))]
        exact ptrNext sp _ m
      · rw [← v101_def, ← v99_def, ← v93_def, ← v7_def, ← hhB,
          replaceByte_replaceByte _ _ (by decide), headNext (m % 64) (Nat.mod_lt _ (by decide)),
          Nat.mod_add_mod]
      · rw [← v37_def]; exact lenNext (255 + m)
    · rw [h6, ← v110_def, ← v109_def, ← v103_def, ← v93_def, ← v7_def, ← hhB,
        Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
      exact bitNext B m
  sym_close hk'

end Cases.Zip2005
