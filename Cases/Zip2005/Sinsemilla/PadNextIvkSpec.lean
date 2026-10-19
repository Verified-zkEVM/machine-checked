import Cases.Zip2005.Sinsemilla.PadNextIvk0
import Cases.Zip2005.Sinsemilla.PadNextIvk
import Cases.Zip2005.Sinsemilla.PadNextIvkB
import Cases.Zip2005.Sinsemilla.PadNextIvkEnds
import Cases.Zip2005.Orchard.CommitIvk
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Pad<…>::next` (0x78021e7c): one specification over the message position

`ivkState sp J j k` is the iterator block after `k` calls (`0 ≤ k ≤ 511`): the inner cursor
(`ak`'s bits) live through position 255, the outer (`nk`'s) through 510, then `Pad` spent
(`padding_left = Some(0)`: 510 bits is a multiple of K = 10). `pad_next_ivk_spec` glues the
phase lemmas: call `k < 510` yields message bit `k` (`ivkBit`), call 510 yields `None` (2).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- The iterator block after `k` calls. -/
def ivkState (sp : Word) (J : List Word) (j : Word) (k : Nat) : List Word :=
  if k ≤ 255 then
    padIvkA sp J j (BitVec.ofNat 64 (255 - k)) (ptrA sp + BitVec.ofNat 64 (8 * (k / 64)))
      (BitVec.ofNat 8 (k % 64)) (if k = 0 then 1#64 else 0#64) (BitVec.ofNat 64 k)
  else if k ≤ 510 then
    padIvkB sp J j (BitVec.ofNat 64 (255 - (k - 255))) (ptrB sp + BitVec.ofNat 64 (8 * ((k - 255) / 64)))
      (BitVec.ofNat 8 ((k - 255) % 64)) (BitVec.ofNat 64 k)
  else
    [1#64, 0#64, 0#64, ptrB sp + 24#64, replaceByte (ivkEndB sp J) 0 63#8, ivkEndB2 sp J,
     0#64, ptrA sp + 24#64, replaceByte (ivkEndA sp J) 0 63#8, ivkEndA2 sp J,
     replaceByte J[8]! 0 (BitVec.truncate 8 2#64), 510#64]

@[simp] theorem ivkState_length (sp : Word) (J : List Word) (j : Word) (k : Nat) :
    (ivkState sp J j k).length = 12 := by
  unfold ivkState
  split <;> (try split) <;> rfl

/-! ## The phases, as rewrite rules -/

theorem ivkState_0 (sp : Word) (J : List Word) (j : Word) :
    ivkState sp J j 0 = padIvkA sp J j 255#64 (ptrA sp) 0#8 1#64 0#64 := by
  rw [ivkState, if_pos (by decide), if_pos rfl, show (8 * (0 / 64) : Nat) = 0 from rfl, BitVec.add_zero]

theorem ivkState_A (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 255) :
    ivkState sp J j k = padIvkA sp J j (BitVec.ofNat 64 (255 - k)) (ptrA sp + BitVec.ofNat 64 (8 * (k / 64)))
      (BitVec.ofNat 8 (k % 64)) 0#64 (BitVec.ofNat 64 k) := by
  rw [ivkState, if_pos hk, if_neg (by omega)]

theorem ivkState_B (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk : 256 ≤ k) (hk' : k ≤ 510) :
    ivkState sp J j k = padIvkB sp J j (BitVec.ofNat 64 (255 - (k - 255)))
      (ptrB sp + BitVec.ofNat 64 (8 * ((k - 255) / 64))) (BitVec.ofNat 8 ((k - 255) % 64))
      (BitVec.ofNat 64 k) := by
  rw [ivkState, if_neg (by omega), if_pos hk']

theorem ivkState_end (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk : 511 ≤ k) :
    ivkState sp J j k =
      [1#64, 0#64, 0#64, ptrB sp + 24#64, replaceByte (ivkEndB sp J) 0 63#8, ivkEndB2 sp J,
       0#64, ptrA sp + 24#64, replaceByte (ivkEndA sp J) 0 63#8, ivkEndA2 sp J,
       replaceByte J[8]! 0 (BitVec.truncate 8 2#64), 510#64] := by
  rw [ivkState, if_neg (by omega), if_neg (by omega)]

/-- The inner end word with its head byte written as `0`: the block's own word. -/
theorem ivkEndA_head_zero (sp : Word) (J : List Word) :
    replaceByte (ivkEndA sp J) 0 0#8 = ivkEndA sp J := by
  apply word_ext
  intro i hi
  by_cases h : i = 0
  · subst h
    rw [extractByte_replaceByte _ _ (by decide)]
    simp (disch := decide) only [ivkEndA, extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  · rw [extractByte_replaceByte_ne _ _ _ _ hi (Ne.symm h)]

/-- The block as `commit_ivk` hands it to `from_iter` (`iterIvkW`, before any call). -/
theorem ivkState_zero (sp : Word) (J : List Word) (j : Word) :
    ivkState sp J j 0 = [0#64, j] ++ iterIvkW sp J ++ [0#64] := by
  rw [ivkState_0]
  show [0#64, j, 255#64, ptrB sp, ivkEndB sp J, ivkEndB2 sp J, 255#64, ptrA sp,
      replaceByte (ivkEndA sp J) 0 0#8, ivkEndA2 sp J, replaceByte J[8]! 0 (BitVec.truncate 8 1#64), 0#64] =
    [0#64, j, 255#64, ptrB sp, ivkEndB sp J, ivkEndB2 sp J, 255#64, ptrA sp, ivkEndA sp J, ivkEndA2 sp J,
      replaceByte J[8]! 0 (BitVec.truncate 8 1#64), 0#64]
  rw [ivkEndA_head_zero]

set_option maxHeartbeats 4000000 in
theorem pad_next_ivk_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word) (k : Nat) (hk510 : k ≤ 510)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (ivkState sp J j k) s)
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
      Region iter (ivkState sp J j (k + 1)) t →
      t.getReg .x10 = (if k < 510 then bw (ivkBit A B k) else 2#64) → SafeN G n P t) :
    SafeN G n P s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- the first call
    rw [ivkState_0] at hI
    refine pad_next_ivk_0_spec s ra spn sp iter J A B hAl hBl j hpc hcode hcw hro hheap hra hra1 hsp hstk
      hsp_lo hsp_hi ha0 hI hokI hiter hAr hokA hBr hokB hdjI hdjI' hdjS hdjSA hdjSB hdjAB hunwrap_opt ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [ivkState_A _ _ _ 1 (by decide) (by decide), show (8 * (1 / 64) : Nat) = 0 from rfl,
        BitVec.add_zero]
      exact h5
    · rw [h6, if_pos (by decide), ivkBit, if_pos (by decide)]
  rcases Nat.lt_or_ge k 255 with h255 | h255
  · -- phase A
    rw [ivkState_A _ _ _ k hk1 (by omega)] at hI
    refine pad_next_ivk_a_spec s ra spn sp iter J A B hAl hBl k hk1 (by omega) j _ _ _ rfl rfl rfl
      hpc hcode hcw hro hheap hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hiter hAr hokA hBr hokB hdjI hdjI' hdjS
      hdjSA hdjSB hdjAB hunwrap_opt ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [ivkState_A _ _ _ (k + 1) (by omega) (by omega)]
      exact h5
    · rw [h6, if_pos (by omega), ivkBit, if_pos h255]
  rcases Nat.eq_or_lt_of_le h255 with h255' | h256
  · -- the phase change
    subst h255'
    rw [ivkState_A _ _ _ 255 (by decide) (by decide)] at hI
    refine pad_next_ivk_255_spec s ra spn sp iter J A B hAl hBl j hpc hcode hcw hra hra1 hsp hstk
      hsp_lo hsp_hi ha0 hI hokI hAr hokA hBr hokB hdjI hdjI' hdjS hdjSA hdjSB hdjAB ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [ivkState_B _ _ _ (255 + 1) (by decide) (by decide),
        show (8 * ((255 + 1 - 255) / 64) : Nat) = 0 from rfl, BitVec.add_zero]
      exact h5
    · rw [h6, if_pos (by decide), ivkBit, if_neg (by decide), Nat.sub_self]
  rcases Nat.lt_or_ge k 510 with h510 | h510
  · -- phase B
    obtain ⟨m, rfl⟩ : ∃ m, k = 255 + m := ⟨k - 255, by omega⟩
    rw [ivkState_B _ _ _ (255 + m) (by omega) (by omega), Nat.add_sub_cancel_left] at hI
    refine pad_next_ivk_b_spec s ra spn sp iter J A B hAl hBl m (by omega) (by omega) j _ _ _ rfl rfl rfl
      hpc hcode hcw hro hheap hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hiter hAr hokA hBr hokB hdjI hdjI' hdjS
      hdjSA hdjSB hdjAB hunwrap_opt ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [ivkState_B _ _ _ (255 + m + 1) (by omega) (by omega), show 255 + m + 1 - 255 = m + 1 by omega]
      exact h5
    · rw [h6, if_pos (by omega), ivkBit, if_neg (by omega), Nat.add_sub_cancel_left]
  · -- the end
    have hk510' : k = 510 := by omega
    subst hk510'
    rw [ivkState_B _ _ _ 510 (by decide) (by decide)] at hI
    refine pad_next_ivk_510_spec s ra spn sp iter J A B hAl hBl j hpc hcode hcw hra hra1 hsp hstk
      hsp_lo hsp_hi ha0 hI hokI hAr hokA hBr hokB hdjI hdjI' hdjS hdjSA hdjSB hdjAB ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [ivkState_end _ _ _ (510 + 1) (by decide)]
      exact h5
    · rw [h6, if_neg (by decide)]

/-- The calls that yield a bit: `k < 510`. -/
theorem pad_next_ivk_lt_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word) (k : Nat) (hk510 : k < 510)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (ivkState sp J j k) s)
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
      Region iter (ivkState sp J j (k + 1)) t →
      t.getReg .x10 = bw (ivkBit A B k) → SafeN G n P t) :
    SafeN G n P s := by
  refine pad_next_ivk_spec s ra spn sp iter J A B hAl hBl j k (by omega) hpc hcode hcw hro hheap hra hra1 hsp hstk
    hsp_lo hsp_hi ha0 hI hokI hiter hAr hokA hBr hokB hdjI hdjI' hdjS hdjSA hdjSB hdjAB hunwrap_opt ?_
  intro t h1 h2 h3 h4 h5 h6
  exact hk t h1 h2 h3 h4 h5 (by rw [h6, if_pos hk510])

/-- The same, with the block as a list variable related to the model (the form the executor
    matches at a call inside `from_iter`'s loop). -/
theorem pad_next_ivk_var_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B I : List Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word) (k : Nat) (hk510 : k < 510)
    (hIl : I.length = 12) (hIv : ivkState sp J j k = I)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter I s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 12)
    (hiter : iter.toNat + 8 * 12 ≤ 0x78040620)
    (hAr : Region (ptrA sp) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp) 4)
    (hBr : Region (ptrB sp) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp) 4)
    (hdjI : Disjoint iter 12 (ptrA sp) 4) (hdjI' : Disjoint iter 12 (ptrB sp) 4)
    (hdjS : Disjoint (spn - 0x10#64) 2 iter 12) (hdjSA : Disjoint (spn - 0x10#64) 2 (ptrA sp) 4)
    (hdjSB : Disjoint (spn - 0x10#64) 2 (ptrB sp) 4) (hdjAB : Disjoint (ptrA sp) 4 (ptrB sp) 4)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ (t : MachineState) (I' : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      I'.length = 12 → ivkState sp J j (k + 1) = I' → Region iter I' t →
      t.getReg .x10 = bw (ivkBit A B k) → SafeN G n P t) :
    SafeN G n P s := by
  subst hIv
  refine pad_next_ivk_lt_spec s ra spn sp iter J A B hAl hBl j k hk510 hpc hcode hcw hro hheap hra hra1 hsp hstk
    hsp_lo hsp_hi ha0 hI hokI hiter hAr hokA hBr hokB hdjI hdjI' hdjS hdjSA hdjSB hdjAB hunwrap_opt ?_
  intro t h1 h2 h3 h4 h5 h6
  exact hk t _ h1 h2 h3 h4 (ivkState_length _ _ _ _) rfl h5 h6

/-- The same over the block's twelve cells (the form the executor unifies at a call inside
    `from_iter`'s loop: the model equation in the cells it tracks). -/
theorem pad_next_ivk_cells_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word) (k : Nat)
    (hIv : ivkState sp J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11]) (hk510 : k < 510)
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 12)
    (hiter : iter.toNat + 8 * 12 ≤ 0x78040620)
    (hAr : Region (ptrA sp) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp) 4)
    (hBr : Region (ptrB sp) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp) 4)
    (hdjI : Disjoint iter 12 (ptrA sp) 4) (hdjI' : Disjoint iter 12 (ptrB sp) 4)
    (hdjS : Disjoint (spn - 0x10#64) 2 iter 12) (hdjSA : Disjoint (spn - 0x10#64) 2 (ptrA sp) 4)
    (hdjSB : Disjoint (spn - 0x10#64) 2 (ptrB sp) 4) (hdjAB : Disjoint (ptrA sp) 4 (ptrB sp) 4)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' bit : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      ivkState sp J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region iter [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
      bw (ivkBit A B k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
      t.getReg .x10 = bit → SafeN G n P t) :
    SafeN G n P s := by
  refine pad_next_ivk_var_spec s ra spn sp iter J A B _ hAl hBl j k hk510 rfl hIv hpc hcode hcw hro hheap hra hra1
    hsp hstk hsp_lo hsp_hi ha0 hI hokI hiter hAr hokA hBr hokB hdjI hdjI' hdjS hdjSA hdjSB hdjAB hunwrap_opt ?_
  intro t I' h1 h2 h3 h4 hl hIv' h5 h6
  rw [list12_cells I' hl] at hIv' h5
  exact hk t _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 hIv' h5 rfl (bw_ne_two _) (bw_and255 _) h6

/-- Call 510, over the block's cells: `None` (2), `Pad` spent. -/
theorem pad_next_ivk_end_cells_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra spn sp iter : Word) (J A B : List Word)
    (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 : Word)
    (hAl : A.length = 4) (hBl : B.length = 4) (j : Word)
    (hIv : ivkState sp J j 510 = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11])
    (hpc : s.pc = 0x78021e7c#64) (hcode : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x10 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11] s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 12)
    (hiter : iter.toNat + 8 * 12 ≤ 0x78040620)
    (hAr : Region (ptrA sp) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp) 4)
    (hBr : Region (ptrB sp) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp) 4)
    (hdjI : Disjoint iter 12 (ptrA sp) 4) (hdjI' : Disjoint iter 12 (ptrB sp) 4)
    (hdjS : Disjoint (spn - 0x10#64) 2 iter 12) (hdjSA : Disjoint (spn - 0x10#64) 2 (ptrA sp) 4)
    (hdjSB : Disjoint (spn - 0x10#64) 2 (ptrB sp) 4) (hdjAB : Disjoint (ptrA sp) 4 (ptrB sp) 4)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x10#64, 2), (iter, 12)] s t →
      ivkState sp J j 511 = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] → Region iter [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11'] t →
      t.getReg .x10 = 2#64 → SafeN G n P t) :
    SafeN G n P s := by
  rw [← hIv] at hI
  refine pad_next_ivk_spec s ra spn sp iter J A B hAl hBl j 510 (by decide) hpc hcode hcw hro hheap hra hra1
    hsp hstk hsp_lo hsp_hi ha0 hI hokI hiter hAr hokA hBr hokB hdjI hdjI' hdjS hdjSA hdjSB hdjAB hunwrap_opt ?_
  intro t h1 h2 h3 h4 h5 h6
  rw [list12_cells _ (ivkState_length sp J j 511)] at h5
  exact hk t _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 rfl h5 (by rw [h6, if_neg (by decide)])

end Cases.Zip2005
