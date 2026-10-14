/-
  Cases.Zip2005.Memcmp

  `memcmp(a, b, n)` on doubleword-aligned blocks of `n = 8k` bytes: the result
  is zero exactly when the blocks are equal. The byte loop is proved by
  induction on the bytes left, applying the induction hypothesis at the back
  edge; the executor runs one iteration, with the loads at the symbolic offset
  `j` into the two regions.
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7803f54c
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- Byte `i` of a little-endian doubleword list. -/
def byteOf (xs : List Word) (i : Nat) : BitVec 8 := extractByte (xs[i / 8]!) (i % 8)

theorem word_eq_of_bytes (w w' : Word) (h : ∀ k, k < 8 → extractByte w k = extractByte w' k) :
    w = w' := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  have hk := h (n / 8) (by omega)
  have := congrArg (fun b : BitVec 8 => b.getLsbD (n % 8)) hk
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight] at this
  have e : n / 8 * 8 + n % 8 = n := by omega
  simpa [show n % 8 < 8 by omega, e] using this

theorem zeroExtend_byte_inj (x y : BitVec 8) (h : BitVec.zeroExtend 64 x = BitVec.zeroExtend 64 y) :
    x = y := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have hx := x.isLt; have hy := y.isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- Two lists of `k` doublewords are equal when their `8k` bytes are. -/
theorem eq_of_bytes {xs ys : List Word} {k : Nat} (hx : xs.length = k) (hy : ys.length = k)
    (h : ∀ i, i < 8 * k → byteOf xs i = byteOf ys i) : xs = ys := by
  apply List.ext_getElem (hx.trans hy.symm)
  intro n h1 h2
  apply word_eq_of_bytes
  intro b hb
  have := h (8 * n + b) (by omega)
  simp only [byteOf, show (8 * n + b) / 8 = n by omega, show (8 * n + b) % 8 = b by omega,
    getElem!_pos xs n h1, getElem!_pos ys n h2] at this
  exact this

theorem eq_of_add_neg_eq_zero {x y : Word} (h : x + -y = 0) : x = y := by
  rw [← BitVec.sub_eq_add_neg] at h
  bv_omega

theorem sext32_sub_bytes (x y : BitVec 8) :
    BitVec.signExtend 64 ((BitVec.zeroExtend 64 x + -BitVec.zeroExtend 64 y).truncate 32) =
      BitVec.zeroExtend 64 x + -BitVec.zeroExtend 64 y := by
  rw [← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · have e : (2 ^ 64 - y.toNat % 2 ^ 64 + x.toNat % 2 ^ 64) % 2 ^ 64 = x.toNat - y.toNat := by omega
    simp only [e, decide_eq_true_eq]
    split <;> omega
  · have e : (2 ^ 64 - y.toNat % 2 ^ 64 + x.toNat % 2 ^ 64) % 2 ^ 64 =
        2 ^ 64 - (y.toNat - x.toNat) := by omega
    simp only [e, decide_eq_true_eq]
    split <;> omega

theorem fold8 {xs : List Word} (h : xs.length = 8) :
    [xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[5]!, xs[6]!, xs[7]!] = xs := by
  match xs, h with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem fold4 {xs : List Word} (h : xs.length = 4) : [xs[0]!, xs[1]!, xs[2]!, xs[3]!] = xs := by
  match xs, h with
  | [_, _, _, _], _ => rfl

set_option maxHeartbeats 20000000 in
/-- The byte loop of `memcmp` on two blocks of eight doublewords, from byte `j`. -/
theorem memcmp_loop8 {P : Prop} (s₀ : MachineState) (ra a b : Word) (xs ys : List Word)
    (hxl : xs.length = 8) (hyl : ys.length = 8)
    (hk : ∀ u, u.pc = ra → CalleeSaved s₀ u → u.code = s₀.code → Unchanged [] s₀ u →
      (u.getReg .x10 = 0 ↔ xs = ys) →
      BitVec.signExtend 64 ((u.getReg .x10).truncate 32) = u.getReg .x10 → Safe P u) :
    ∀ m j (t : MachineState), 64 - j = m → j < 64 →
      t.pc = 0x7803f550#64 → CodeAt F_7803f54c.base F_7803f54c.prog t →
      CodeWithin Ro.layout.textLo Ro.layout.textHi t → t.getReg .x1 = ra → ra &&& ~~~1#64 = ra →
      t.getReg .x10 = a + BitVec.ofNat 64 j → t.getReg .x11 = b + BitVec.ofNat 64 j →
      t.getReg .x12 = BitVec.ofNat 64 (64 - j) →
      Region a xs t → RegionOk Ro.layout.textLo Ro.layout.textHi a 8 → Region b ys t → RegionOk Ro.layout.textLo Ro.layout.textHi b 8 →
      CalleeSaved s₀ t → t.code = s₀.code → Unchanged [] s₀ t →
      (∀ i, i < j → byteOf xs i = byteOf ys i) → Safe P t := by
  intro m
  induction m with
  | zero => intro j t hm hj; omega
  | succ m ih =>
    intro j t hm hj hpc hcode hcw hra hra1 ha0 ha1 ha2 hx hokx hy hoky hcs hcode₀ hu₀ hbytes
    have hu := Unchanged.refl ([] : List (Word × Nat)) t
    have hm' : m < 64 := by omega
    sym_exec stop [0x7803f550]
    · -- the bytes differ: the result is their nonzero difference
      sym_close hk
      all_goals sym_subst
      rw [hx10]
      simp only [bne_iff_ne, ne_eq] at hbr2
      constructor
      · intro h
        exact absurd (eq_of_add_neg_eq_zero h) hbr2
      · intro hxy; subst hxy; exact absurd rfl hbr2
      · rw [hx10]; exact sext32_sub_bytes _ _
    · -- the back edge: one more byte agrees
      sym_close ih (j + 1)
      · sym_subst
        by_contra h
        obtain rfl : m = 0 := by omega
        simp at hbr6
      · sym_subst
        rw [hx12, show 64 - (j + 1) = m by omega]
        simp (config := {decide := true}) only [AsmVerif.RiscV.Sym.add_ofNat_big]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      · sym_subst
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact hbytes i h
        · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hbr2
          have := zeroExtend_byte_inj _ _ hbr2
          rwa [fold8 hxl, fold8 hyl] at this
    · -- the last byte agrees: the blocks are equal
      sym_close hk
      sym_subst
      rw [hx10]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      obtain rfl : m = 0 := by
        by_contra h
        apply hbr6
        simp only [bne_iff_ne, ne_eq]
        intro h0
        simp (config := {decide := true}) only [AsmVerif.RiscV.Sym.add_ofNat_big] at h0
        have := congrArg BitVec.toNat h0
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hbr2
      have hlast := zeroExtend_byte_inj _ _ hbr2
      rw [fold8 hxl, fold8 hyl] at hlast
      apply eq_of_bytes hxl hyl
      intro i hi
      rcases Nat.lt_or_ge i j with h | h
      · exact hbytes i h
      · obtain rfl : i = j := by omega
        exact hlast

/-- `memcmp(a, b, 64)` on two blocks of eight doublewords: zero exactly when they are equal. -/
theorem memcmp8_spec {P : Prop} (s : MachineState) (ra a b : Word) (xs ys : List Word)
    (hxl : xs.length = 8) (hyl : ys.length = 8)
    (hpc : s.pc = 0x7803f54c#64) (hcode : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a) (ha1 : s.getReg .x11 = b) (ha2 : s.getReg .x12 = 64#64)
    (hx : Region a xs s) (hokx : RegionOk Ro.layout.textLo Ro.layout.textHi a 8)
    (hy : Region b ys s) (hoky : RegionOk Ro.layout.textLo Ro.layout.textHi b 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      (t.getReg .x10 = 0 ↔ xs = ys) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl ([] : List (Word × Nat)) s
  sym_exec stop [0x7803f550]
  sym_close memcmp_loop8 s ra a b xs ys hxl hyl hk 64 0

set_option maxHeartbeats 20000000 in
/-- The byte loop of `memcmp` on two blocks of four doublewords, from byte `j`. -/
theorem memcmp_loop4 {P : Prop} (s₀ : MachineState) (ra a b : Word) (xs ys : List Word)
    (hxl : xs.length = 4) (hyl : ys.length = 4)
    (hk : ∀ u, u.pc = ra → CalleeSaved s₀ u → u.code = s₀.code → Unchanged [] s₀ u →
      (u.getReg .x10 = 0 ↔ xs = ys) →
      BitVec.signExtend 64 ((u.getReg .x10).truncate 32) = u.getReg .x10 → Safe P u) :
    ∀ m j (t : MachineState), 32 - j = m → j < 32 →
      t.pc = 0x7803f550#64 → CodeAt F_7803f54c.base F_7803f54c.prog t →
      CodeWithin Ro.layout.textLo Ro.layout.textHi t → t.getReg .x1 = ra → ra &&& ~~~1#64 = ra →
      t.getReg .x10 = a + BitVec.ofNat 64 j → t.getReg .x11 = b + BitVec.ofNat 64 j →
      t.getReg .x12 = BitVec.ofNat 64 (32 - j) →
      Region a xs t → RegionOk Ro.layout.textLo Ro.layout.textHi a 4 → Region b ys t → RegionOk Ro.layout.textLo Ro.layout.textHi b 4 →
      CalleeSaved s₀ t → t.code = s₀.code → Unchanged [] s₀ t →
      (∀ i, i < j → byteOf xs i = byteOf ys i) → Safe P t := by
  intro m
  induction m with
  | zero => intro j t hm hj; omega
  | succ m ih =>
    intro j t hm hj hpc hcode hcw hra hra1 ha0 ha1 ha2 hx hokx hy hoky hcs hcode₀ hu₀ hbytes
    have hu := Unchanged.refl ([] : List (Word × Nat)) t
    have hm' : m < 32 := by omega
    sym_exec stop [0x7803f550]
    · -- the bytes differ: the result is their nonzero difference
      sym_close hk
      all_goals sym_subst
      rw [hx10]
      simp only [bne_iff_ne, ne_eq] at hbr2
      constructor
      · intro h
        exact absurd (eq_of_add_neg_eq_zero h) hbr2
      · intro hxy; subst hxy; exact absurd rfl hbr2
      · rw [hx10]; exact sext32_sub_bytes _ _
    · -- the back edge: one more byte agrees
      sym_close ih (j + 1)
      · sym_subst
        by_contra h
        obtain rfl : m = 0 := by omega
        simp at hbr6
      · sym_subst
        rw [hx12, show 32 - (j + 1) = m by omega]
        simp (config := {decide := true}) only [AsmVerif.RiscV.Sym.add_ofNat_big]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      · sym_subst
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact hbytes i h
        · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hbr2
          have := zeroExtend_byte_inj _ _ hbr2
          rwa [fold4 hxl, fold4 hyl] at this
    · -- the last byte agrees: the blocks are equal
      sym_close hk
      sym_subst
      rw [hx10]
      refine ⟨fun _ => ?_, fun _ => rfl⟩
      obtain rfl : m = 0 := by
        by_contra h
        apply hbr6
        simp only [bne_iff_ne, ne_eq]
        intro h0
        simp (config := {decide := true}) only [AsmVerif.RiscV.Sym.add_ofNat_big] at h0
        have := congrArg BitVec.toNat h0
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hbr2
      have hlast := zeroExtend_byte_inj _ _ hbr2
      rw [fold4 hxl, fold4 hyl] at hlast
      apply eq_of_bytes hxl hyl
      intro i hi
      rcases Nat.lt_or_ge i j with h | h
      · exact hbytes i h
      · obtain rfl : i = j := by omega
        exact hlast

/-- `memcmp(a, b, 32)` on two blocks of four doublewords: zero exactly when they are equal. -/
theorem memcmp4_spec {P : Prop} (s : MachineState) (ra a b : Word) (xs ys : List Word)
    (hxl : xs.length = 4) (hyl : ys.length = 4)
    (hpc : s.pc = 0x7803f54c#64) (hcode : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a) (ha1 : s.getReg .x11 = b) (ha2 : s.getReg .x12 = 32#64)
    (hx : Region a xs s) (hokx : RegionOk Ro.layout.textLo Ro.layout.textHi a 4)
    (hy : Region b ys s) (hoky : RegionOk Ro.layout.textLo Ro.layout.textHi b 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      (t.getReg .x10 = 0 ↔ xs = ys) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl ([] : List (Word × Nat)) s
  sym_exec stop [0x7803f550]
  sym_close memcmp_loop4 s ra a b xs ys hxl hyl hk 32 0

end Cases.Zip2005
