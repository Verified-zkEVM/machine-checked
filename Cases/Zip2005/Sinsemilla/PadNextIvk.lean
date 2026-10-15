import Cases.Zip2005.Sinsemilla.PadIvkDefs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Image.F_78021e7c
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Pad<Chain<Chain<Empty, Take<BitValIter>>, Take<BitValIter>>>::next` (0x78021e7c), phase A

`commit_ivk`'s message iterator (`iter::empty().chain(ak bits.take(255)).chain(nk bits.take(255))`
under `sinsemilla::Pad`, K = 10): one `next` at position `1 ≤ k ≤ 254`, while the inner cursor
(`ak`'s bits) is live. The block is `padIvkA` (`Proof/Sinsemilla/PadIvkDefs.lean`): the inner
`Take` has `255 - k` left, its cursor at bit `k` of `ak`'s words, the `Option<Empty>` tag `0`
(the first call, `k = 0`, which clears it from `1`, is `PadNextIvk0.lean`). The call yields
bit `k` and advances the cursor.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option asmverif.sym.foldBytes true in
theorem pad_next_ivk_a_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4)
    (k : Nat) (hk1 : 1 ≤ k) (hk254 : k ≤ 254) (j nA pA : Word) (hA : BitVec 8)
    (hnA : BitVec.ofNat 64 (255 - k) = nA) (hpA : pA = ptrA sp + BitVec.ofNat 64 (8 * (k / 64)))
    (hhA : BitVec.ofNat 8 (k % 64) = hA)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (padIvkA sp J j nA pA hA 0#64 (BitVec.ofNat 64 k)) s)
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
      Region iter (padIvkA sp J j (BitVec.ofNat 64 (255 - (k + 1)))
        (ptrA sp + BitVec.ofNat 64 (8 * ((k + 1) / 64))) (BitVec.ofNat 8 ((k + 1) % 64)) 0#64
        (BitVec.ofNat 64 (k + 1))) t →
      t.getReg .x10 = bw (wordsBit A k) → SafeN G n P t) :
    SafeN G n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(spn - 0x10#64, 2), (iter, 12)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x10#64) 2 s
  -- the loaded bytes of the block's constant words, as the executor rewrites them
  have hTag := ivkTag_byte0 J
  have hHd := ivkEndA_head sp J hA
  have hEA1 := ivkEndA_byte sp J hA 1 (by decide)
  have hEA2 := ivkEndA_byte sp J hA 2 (by decide)
  have hEA3 := ivkEndA_byte sp J hA 3 (by decide)
  have hEA4 := ivkEndA_byte sp J hA 4 (by decide)
  have hEA5 := ivkEndA_byte sp J hA 5 (by decide)
  have hEA6 := ivkEndA_byte sp J hA 6 (by decide)
  have hEA7 := ivkEndA_byte sp J hA 7 (by decide)
  have hEA2_0 := ivkEndA2_byte0 sp J
  have hEA2_1 := ivkEndA2_byte1 sp J
  -- the pointers are not null, the count not zero, the cursor short of its end
  have hpB0 : (ptrB sp == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpA0 : (sp + (18446744073709551400#64 + BitVec.ofNat 64 (8 * (k / 64))) == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add] at this
    rw [Bn.toNat_ofNat' (8 * (k / 64))] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hnA0 : nA ≠ 0#64 := by
    rw [← hnA]
    intro h
    have := congrArg BitVec.toNat h
    rw [Bn.toNat_ofNat'] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpe : sp + (18446744073709551400#64 + BitVec.ofNat 64 (8 * (k / 64))) ≠ ptrB sp := by
    simp only [ptrB]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add] at this
    rw [Bn.toNat_ofNat' (8 * (k / 64))] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hA4 : [A[0]!, A[1]!, A[2]!, A[3]!] = A := by
    match A, hAl with
    | [_, _, _, _], _ => rfl
  sym_exec [hunwrap_opt]
  all_goals (first
    -- the inner cursor is not null
    | (simp only [← v35_def, hpA0] at hbr54; exact absurd hbr54 (by decide))
    -- the inner range is not exhausted
    | (exfalso; sym_subst; rw [bytes_word, seqz_or_xor _ _ _ hpe] at hbr86; exact hbr86 (by decide))
    | skip)
  -- the live path: the block's new cells and the bit, as the executor left them
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      Region iter [0#64, j, 255#64, ptrB sp, ivkEndB sp J, ivkEndB2 sp J,
        nA + 18446744073709551615#64, v98, v102, ivkEndA2 sp J,
        replaceByte J[8]! 0 (BitVec.truncate 8 0#64), v37 + 1#64] t →
      t.getReg .x10 = v111 → SafeN G n P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 (Region.of_eq h5 ?_) ?_
    · simp only [padIvkA, List.cons.injEq, and_true, true_and, eq_self]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← hnA]; exact countNext k hk254
      · rw [← v98_def, ← v97_def, ← v96_def, ← v94_def, ← v57_def, ← v35_def, ← hhA,
          ptrStep (k % 64) (Nat.mod_lt _ (by decide))]
        exact ptrNext sp _ k
      · rw [← v102_def, ← v100_def, ← v94_def, ← v57_def, ← hhA,
          replaceByte_replaceByte _ _ (by decide), headNext (k % 64) (Nat.mod_lt _ (by decide)),
          Nat.mod_add_mod]
      · rw [← v37_def]; exact lenNext k
    · rw [h6, ← v111_def, ← v110_def, ← v104_def, ← v94_def, ← v57_def, ← hhA,
        Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
      exact bitNext A k
  sym_close hk'

end Cases.Zip2005
