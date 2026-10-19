/-
  MachineChecked.RiscV.Check.Arith

  Address arithmetic for the checker's soundness: frame windows, footprint items, and the
  doubleword keys stores write.
-/

import MachineChecked.RiscV.Check.Spec

namespace MachineChecked.RiscV.Check

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

theorem negOff_eq {k : Word} : k = 0 - BitVec.ofNat 64 (negOff k) := by
  simp only [negOff, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega

theorem negOff_lt (k : Word) : negOff k < 2 ^ 64 := (0 - k).isLt

/-- An address `m` bytes below `e`. -/
theorem add_frame {e k : Word} : e + k = e - BitVec.ofNat 64 (negOff k) := by
  conv => lhs; rw [negOff_eq (k := k)]
  bv_omega

theorem aligned_iff (a : Word) : Aligned a ↔ a.toNat % 8 = 0 := by
  unfold Aligned
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at this
    have h7 : (7#64).toNat = 2 ^ 3 - 1 := rfl
    rw [h7, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7 : (7#64).toNat = 2 ^ 3 - 1 := rfl
    rw [h7, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h

theorem alignToDword_toNat (a : Word) :
    (alignToDword a).toNat = a.toNat - a.toNat % 8 := by
  have h := sub_alignToDword_lt a
  have hal : (alignToDword a).toNat % 8 = 0 := by
    have : Aligned (alignToDword a) := by
      unfold Aligned alignToDword
      ext i; simp only [BitVec.getElem_and, BitVec.getElem_not]
      rcases Bool.eq_false_or_eq_true ((7#64)[i]) with h7 | h7 <;> simp [h7]
    exact (aligned_iff _).mp this
  have hle : (alignToDword a).toNat ≤ a.toNat := by
    unfold alignToDword; rw [BitVec.toNat_and]; exact Nat.and_le_left
  rw [BitVec.toNat_sub] at h
  have : (2 ^ 64 - (alignToDword a).toNat + a.toNat) % 2 ^ 64 = a.toNat - (alignToDword a).toNat := by
    have := (alignToDword a).isLt
    rw [show 2 ^ 64 - (alignToDword a).toNat + a.toNat = 2 ^ 64 + (a.toNat - (alignToDword a).toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  rw [this] at h
  omega

theorem aligned_alignToDword (a : Word) : Aligned (alignToDword a) := by
  rw [aligned_iff, alignToDword_toNat]; omega

/-- The key a store of width `w` at `addr` rewrites is hit by the store's own bytes. -/
theorem hits_target (w : Width) (addr : Word) : Hits addr (wbytes w) (w.target addr) := by
  cases w with
  | d => left; simp [wbytes, Width.target]
  | sub =>
    simp only [Hits, wbytes, Width.target]
    right
    refine ⟨by omega, ?_⟩
    have := sub_alignToDword_lt addr
    exact this

/-! ## Windows -/

section Window

variable {e : Word} {D : Nat}

/-- A key hit by bytes inside `[e - D, e)`, with `D ≤ e`, lies in the window. -/
theorem inWin_of_hits {b : Word} {l : Nat} {a : Word}
    (hb : (e - b).toNat ≤ D) (hl : l ≤ (e - b).toNat)
    (hl0 : 0 < l) (h : Hits b l a) : InWin e D a := by
  unfold InWin Hits at *
  have he := e.isLt
  by_cases hlt : (a - (e - BitVec.ofNat 64 D)).toNat < D
  · left; exact hlt
  · right
    refine ⟨by omega, ?_⟩
    rcases h with h | ⟨_, h⟩ <;> bv_omega

/-- The key of a frame store of width `w`, `m` bytes below `e` (`wbytes w ≤ m ≤ D ≤ e`),
    lies in the window. -/
theorem inWin_store {w : Width} {m : Nat} (hD : D ≤ e.toNat) (hm : wbytes w ≤ m) (hmD : m ≤ D) :
    InWin e D (w.target (e - BitVec.ofNat 64 m)) := by
  have hm64 : m < 2 ^ 64 := by have := e.isLt; omega
  have hb : (e - (e - BitVec.ofNat 64 m)).toNat = m := by
    have : e - (e - BitVec.ofNat 64 m) = BitVec.ofNat 64 m := by bv_omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
  have hw : 0 < wbytes w := by cases w <;> simp [wbytes]
  exact inWin_of_hits (by omega) (by omega) hw (hits_target w _)

/-- Window keys lie below the stack top, so they are not protected. -/
theorem not_prot_of_inWin {env : Env} (hwf : env.wf = true) (he : e.toNat ≤ env.stackTop)
    (hD : D ≤ e.toNat) {a : Word} (h : InWin e D a) : ¬ env.InProt a := by
  rintro ⟨⟨b, l⟩, hR, hh⟩
  simp only [Env.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  have hR' := hwf.1.2 _ hR
  have hst := hwf.1.1
  unfold InWin Hits at h
  unfold Hits at hh
  rcases h with h | ⟨_, h⟩ <;> rcases hh with hh | ⟨_, hh⟩ <;> bv_omega

/-- Window keys are not owned either. -/
theorem not_own_of_inWin {env : Env} (hwf : env.wf = true) (he : e.toNat ≤ env.stackTop)
    (hD : D ≤ e.toNat) {a : Word} (h : InWin e D a) : ¬ env.InOwn a := by
  rintro ⟨⟨b, l⟩, hR, hh⟩
  simp only [Env.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  have hR' := (hwf.2 _ hR).1
  have hst := hwf.1.1
  unfold InWin Hits at h
  unfold Hits at hh
  rcases h with h | ⟨_, h⟩ <;> rcases hh with hh | ⟨_, hh⟩ <;> bv_omega

/-- No key is both protected and owned. -/
theorem not_own_of_prot {env : Env} (hwf : env.wf = true) {a : Word} (hp : env.InProt a) :
    ¬ env.InOwn a := by
  obtain ⟨⟨b', l'⟩, hR', hh'⟩ := hp
  rintro ⟨⟨b, l⟩, hR, hh⟩
  simp only [Env.wf, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hwf
  have hown := hwf.2 _ hR
  have hp1 := hwf.1.2 _ hR'
  have hd := hown.2 _ hR'
  have hb := hown.1
  unfold Hits at hh hh'
  have := a.isLt
  rcases hd with hd | hd <;> rcases hh with hh | ⟨_, hh⟩ <;> rcases hh' with hh' | ⟨_, hh'⟩ <;>
    bv_omega

/-- The invariant sees only owned keys. -/
theorem Env.Inv_congr {env : Env} {m m' : Word → Word}
    (h : ∀ a, Aligned a → env.InOwn a → m' a = m a) (hi : env.Inv m) : env.Inv m' := by
  have : env.ownPart m' = env.ownPart m := by
    funext a
    unfold Env.ownPart
    split
    · rename_i ha; exact h a ha.1 ha.2
    · rfl
  unfold Env.Inv; rw [this]; exact hi

/-- A callee window `m` bytes down, `m + Dg ≤ D`, lies in the caller's, on aligned keys. -/
theorem inWin_callee {m Dg : Nat} (hal : Aligned e) (hm8 : m % 8 = 0)
    (hmD : m + Dg ≤ D) {a : Word} (ha : Aligned a) (h : InWin (e - BitVec.ofNat 64 m) Dg a) :
    InWin e D a := by
  rw [aligned_iff] at hal ha
  have he := e.isLt
  unfold InWin Hits at *
  rcases h with h | ⟨h0, h⟩
  · left; bv_omega
  · by_cases hlt : (a - (e - BitVec.ofNat 64 D)).toNat < D
    · left; exact hlt
    · right; refine ⟨by omega, ?_⟩; bv_omega

/-- A slot at or above the callee's stack pointer is outside the callee's window. -/
theorem not_inWin_callee_slot {m Dg mk : Nat} (hD : D ≤ e.toNat) (hal : Aligned e)
    (hm8 : m % 8 = 0) (hmD : m + Dg ≤ D) (hk8 : mk % 8 = 0) (hk : mk ≤ m) :
    ¬ InWin (e - BitVec.ofNat 64 m) Dg (e - BitVec.ofNat 64 mk) := by
  rw [aligned_iff] at hal
  have he := e.isLt
  unfold InWin Hits
  rintro (h | ⟨h0, h⟩) <;> bv_omega

/-- A slot (an aligned key `mk` bytes below `e`, `8 ≤ mk ≤ D`) lies in the window. -/
theorem inWin_slot {mk : Nat} (hD : D ≤ e.toNat) (hk : 8 ≤ mk) (hkD : mk ≤ D) :
    InWin e D (e - BitVec.ofNat 64 mk) := by
  have := inWin_store (w := .d) hD hk hkD
  simpa [Width.target] using this

end Window

/-! ## Items -/

/-- `within` is containment of the keys hit. -/
theorem within_hits {E : Ent} {d it : Item} (h : d.within it = true) {a : Word}
    (ha : it.Hits E a) : d.Hits E a := by
  unfold Item.within at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact ha
  · unfold Item.Hits at *
    obtain ⟨db, dl⟩ := d
    obtain ⟨ib, il⟩ := it
    simp only at h ha ⊢
    cases db <;> cases ib <;> cases dl <;> cases il <;> simp only [reduceCtorEq] at h
    case lin.lin.n.n r0 k0 r k l0 l =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hk⟩, hl0⟩ := h
      simp only [AVal.eval, Len.eval] at ha ⊢
      unfold Hits at *
      rcases ha with ha | ⟨hl, ha⟩
      · left; bv_omega
      · by_cases hd : (k - k0).toNat ≥ (E r0 + k - a).toNat
        · left; bv_omega
        · right; exact ⟨by omega, by bv_omega⟩
    case const.const.n.n c0 c l0 l =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hk, hl0⟩ := h
      simp only [AVal.eval, Len.eval] at ha ⊢
      unfold Hits at *
      rcases ha with ha | ⟨hl, ha⟩
      · left; bv_omega
      · by_cases hd : (c - c0).toNat ≥ (c - a).toNat
        · left; bv_omega
        · right; exact ⟨by omega, by bv_omega⟩
    case cell.cell.n.n r0 ks0 k0 r ks k l0 l =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, hk⟩, hl0⟩ := h
      simp only [AVal.eval, Len.eval] at ha ⊢
      generalize E.deref (E r0) ks0 = X at ha ⊢
      unfold Hits at *
      rcases ha with ha | ⟨hl, ha⟩
      · left; bv_omega
      · by_cases hd : (k - k0).toNat ≥ (X + k - a).toNat
        · left; bv_omega
        · right; exact ⟨by omega, by bv_omega⟩

/-- A frame item `[e - mk, e - mk + l)` (`l ≤ mk ≤ m ≤ D ≤ e`) avoids the window of a
    callee entered `m` bytes down, and lies in the caller's window, on aligned keys. -/
theorem frameItem_keys {e : Word} {D m mk l Dg : Nat} (hD : D ≤ e.toNat) (hal : Aligned e)
    (hm8 : m % 8 = 0) (hmD : m + Dg ≤ D) (hl : l ≤ mk) (hk : mk ≤ m) {a : Word} (ha : Aligned a)
    (h : Hits (e - BitVec.ofNat 64 mk) l a) :
    ¬ InWin (e - BitVec.ofNat 64 m) Dg a ∧ InWin e D a := by
  rw [aligned_iff] at hal ha
  have he := e.isLt
  unfold InWin Hits at *
  constructor
  · rintro (h' | ⟨_, h'⟩) <;> rcases h with h | ⟨_, h⟩ <;> bv_omega
  · rcases h with h | ⟨hl0, h⟩
    · left; bv_omega
    · by_cases hlt : (a - (e - BitVec.ofNat 64 D)).toNat < D
      · left; exact hlt
      · right; refine ⟨by omega, ?_⟩; bv_omega

/-- `slotClear` keeps a slot clear of a frame item. -/
theorem slot_not_hits {e : Word} {mk mk' l : Nat} (hD : mk ≤ e.toNat) (hD' : mk' ≤ e.toNat)
    (hk8 : 8 ≤ mk) (hl : l ≤ mk')
    (h : mk' ≤ mk - 8 ∨ mk + l ≤ mk') :
    ¬ Hits (e - BitVec.ofNat 64 mk') l (e - BitVec.ofNat 64 mk) := by
  have he := e.isLt
  unfold Hits
  rintro (h' | ⟨_, h'⟩) <;> rcases h with h | h <;> bv_omega

end MachineChecked.RiscV.Check
