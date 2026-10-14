/-
  Cases.Zip2005.FpSub

  Field subtraction as the guest compiles `Fp::sub`: `sbb` on four limbs, the final
  borrow spread by `sra 63` into a mask, and `p` masked and added back. Its result on
  canonical operands is `(a + p - b) % p`, so it is zero exactly when they are equal --
  the shape of every `ct_eq` / `is_zero` test on field elements (`sqrt_alt`).
-/

import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Field.Fp

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

/-- Field subtraction on canonical representatives (`Fp::sub`: `a - b`, plus `p` on borrow). -/
def Fp.sub (a b : Nat) : Nat := (a + Fp.p - b) % Fp.p

theorem Fp.sub_lt (a b : Nat) : Fp.sub a b < Fp.p := Nat.mod_lt _ Fp.p_pos

/-- The field difference of canonical representatives is zero exactly when they are equal. -/
theorem Fp.sub_eq_zero_iff {a b : Nat} (ha : a < Fp.p) (hb : b < Fp.p) :
    Fp.sub a b = 0 ↔ a = b := by
  unfold Fp.sub
  constructor
  · intro h
    rcases Nat.lt_or_ge a b with hab | hab
    · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
    · rw [show a + Fp.p - b = (a - b) + Fp.p by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at h
      omega
  · rintro rfl
    rw [show a + Fp.p - a = Fp.p by omega, Nat.mod_self]

/-- `ROOT_OF_UNITY` (a generator of the 2-adic subgroup, a non-square), in Montgomery form. -/
def Fp.rootOfUnity : Nat := 0x3ec928747b89c6dafba6b9ca9dc8448e9083cd03d3b539dfa28db849bad6dbf0

theorem Fp.rootOfUnity_lt : Fp.rootOfUnity < Fp.p := by decide +kernel

/-- Its limbs, as the guest's rodata holds them. -/
theorem Fp.limbs_root : leLimbsToNat [11713220832667294704#64, 10413392179731184095#64,
    18133385229535560846#64, 4524191781424318170#64] = Fp.rootOfUnity := by decide +kernel

/-- Four limbs are zero exactly when their value is. -/
theorem limbs_zero4 (a b c d : Word) :
    leLimbsToNat [a, b, c, d] = 0 ↔ a = 0#64 ∧ b = 0#64 ∧ c = 0#64 ∧ d = 0#64 := by
  simp only [leLimbsToNat_cons, leLimbsToNat_nil, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  omega

namespace Bn

/-- `x - y` as the guest writes it (`x + -y`): the difference, or the difference plus `2^64`. -/
theorem sub_fact {x y v : Word} (h : x + -y = v) :
    (y.toNat ≤ x.toNat ∧ v.toNat + y.toNat = x.toNat) ∨
      (x.toNat < y.toNat ∧ v.toNat + y.toNat = x.toNat + 2 ^ 64) := by
  subst h
  have hx := x.isLt; have hy := y.isLt
  rw [BitVec.toNat_add, BitVec.toNat_neg]
  by_cases hle : y.toNat ≤ x.toNat
  · left; exact ⟨hle, by omega⟩
  · right; exact ⟨by omega, by omega⟩

/-- An unsigned-less-than flag. -/
theorem ult_fact {x y v : Word} (h : (if x.ult y = true then 1#64 else 0#64) = v) :
    (v.toNat = 1 ∧ x.toNat < y.toNat) ∨ (v.toNat = 0 ∧ y.toNat ≤ x.toNat) := by
  subst h
  simp only [BitVec.ult, decide_eq_true_eq]
  by_cases hlt : x.toNat < y.toNat
  · left; simp [hlt]
  · right; simp [hlt]; omega

/-- A sum, with its carry. -/
theorem add_fact' {x y v : Word} (h : x + y = v) :
    v.toNat = x.toNat + y.toNat ∨ v.toNat + 2 ^ 64 = x.toNat + y.toNat := by
  subst h
  have hx := x.isLt; have hy := y.isLt
  rw [BitVec.toNat_add]
  by_cases hc : x.toNat + y.toNat < 2 ^ 64
  · left; exact Nat.mod_eq_of_lt hc
  · right; omega

/-- `and` with an all-or-nothing mask. -/
theorem mask_fact {m c v : Word} (hm : m.toNat = 0 ∨ m.toNat = 2 ^ 64 - 1) (h : m &&& c = v) :
    (m.toNat = 0 ∧ v.toNat = 0) ∨ (m.toNat = 2 ^ 64 - 1 ∧ v.toNat = c.toNat) := by
  subst h
  rcases hm with h0 | h1
  · left
    refine ⟨h0, ?_⟩
    have : m = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
    rw [this, BitVec.zero_and]; rfl
  · right
    refine ⟨h1, ?_⟩
    have : m = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by rw [h1, BitVec.toNat_allOnes])
    rw [this, BitVec.allOnes_and]

end Bn

/-! ### The `sbb` chain, limb by limb -/

/-- Limbs 0 and 1: the difference limbs `f0`, `d1` and the borrow out, as the word `bm`
    (`0` or all ones). -/
theorem fsub_s1 {a0 a1 b0 b1 f0 c0 f1 c1 s d1 c2 bm : Word}
    (hf0 : a0 + -b0 = f0) (hc0 : (if a0.ult b0 = true then 1#64 else 0#64) = c0)
    (hf1 : a1 + -b1 = f1) (hc1 : (if a1.ult b1 = true then 1#64 else 0#64) = c1)
    (hs : c0 + c1 = s) (hd1 : f1 + -c0 = d1)
    (hc2 : (if d1.ult f1 = true then 1#64 else 0#64) = c2) (hbm : c2 + -s = bm) :
    (bm.toNat = 0 ∧
        a0.toNat + 2 ^ 64 * a1.toNat = b0.toNat + 2 ^ 64 * b1.toNat + f0.toNat + 2 ^ 64 * d1.toNat) ∨
      (bm.toNat = 2 ^ 64 - 1 ∧
        a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 =
          b0.toNat + 2 ^ 64 * b1.toNat + f0.toNat + 2 ^ 64 * d1.toNat) := by
  have e0 := Bn.sub_fact hf0
  have e1 := Bn.sub_fact hf1
  have e2 := Bn.sub_fact hd1
  have e3 := Bn.sub_fact hbm
  have k0 := Bn.ult_fact hc0
  have k1 := Bn.ult_fact hc1
  have k2 := Bn.ult_fact hc2
  have es := Bn.add_fact' hs
  have := f0.isLt; have := d1.isLt; have := f1.isLt; have := bm.isLt
  rcases k0 with ⟨k0, _⟩ | ⟨k0, _⟩ <;> rcases k1 with ⟨k1, _⟩ | ⟨k1, _⟩ <;>
    rcases k2 with ⟨k2, _⟩ | ⟨k2, _⟩ <;> omega

/-- A later limb: borrow in as the mask `bm`, difference limb `d`, borrow out as the mask
    `bm'`. -/
theorem fsub_s2 {a b bm m c f d c' t bm' : Word} (hbm : bm.toNat = 0 ∨ bm.toNat = 2 ^ 64 - 1)
    (hm : bm.sshiftRight 63 = m) (hc : (if a.ult b = true then 1#64 else 0#64) = c)
    (hf : a + -b = f) (hd : m + f = d) (hc' : (if d.ult m = true then 1#64 else 0#64) = c')
    (ht : m + -c = t) (hbm' : t + c' = bm') :
    (bm.toNat = 0 →
      (bm'.toNat = 0 ∧ a.toNat = b.toNat + d.toNat) ∨
        (bm'.toNat = 2 ^ 64 - 1 ∧ a.toNat + 2 ^ 64 = b.toNat + d.toNat)) ∧
    (bm.toNat = 2 ^ 64 - 1 →
      (bm'.toNat = 0 ∧ a.toNat = b.toNat + d.toNat + 1) ∨
        (bm'.toNat = 2 ^ 64 - 1 ∧ a.toNat + 2 ^ 64 = b.toNat + d.toNat + 1)) := by
  have sm := Bn.sar_fact hm
  have kc := Bn.ult_fact hc
  have ef := Bn.sub_fact hf
  have ed := Bn.add_fact' hd
  have kc' := Bn.ult_fact hc'
  have et := Bn.sub_fact ht
  have eb := Bn.add_fact' hbm'
  have := f.isLt; have := d.isLt; have := t.isLt; have := bm'.isLt; have := m.isLt
  rcases hbm with h | h <;> rcases kc with ⟨kc, _⟩ | ⟨kc, _⟩ <;>
    rcases kc' with ⟨kc', _⟩ | ⟨kc', _⟩ <;> constructor <;> intro hh <;> omega

/-- The add-back of `p` (limbs `P0, P1, 0, P3`), masked by the final borrow `M`. -/
theorem fsub_s4 {P0 P1 P3 : Nat} {M f0 d1 d2 d3 m0 r0 k0 m1 e1 k1 r1 k1' k r2 k2 m3 e3 r3 : Word}
    (hM : M.toNat = 0 ∨ M.toNat = 2 ^ 64 - 1)
    (hm0 : M &&& BitVec.ofNat 64 P0 = m0) (hr0 : m0 + f0 = r0)
    (hk0 : (if r0.ult m0 = true then 1#64 else 0#64) = k0)
    (hm1 : M &&& BitVec.ofNat 64 P1 = m1) (he1 : m1 + d1 = e1)
    (hk1 : (if e1.ult m1 = true then 1#64 else 0#64) = k1) (hr1 : e1 + k0 = r1)
    (hk1' : (if r1.ult e1 = true then 1#64 else 0#64) = k1') (hk : k1 + k1' = k)
    (hr2 : k + d2 = r2) (hk2 : (if r2.ult k = true then 1#64 else 0#64) = k2)
    (hm3 : M &&& BitVec.ofNat 64 P3 = m3) (he3 : m3 + d3 = e3) (hr3 : e3 + k2 = r3)
    (hP0 : P0 < 2 ^ 64) (hP1 : P1 < 2 ^ 64) (hP3 : P3 < 2 ^ 64) :
    let D := f0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * d3.toNat
    let R := r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat
    let P := P0 + 2 ^ 64 * P1 + 2 ^ 192 * P3
    (M.toNat = 0 → R = D) ∧ (M.toNat = 2 ^ 64 - 1 → R = D + P ∨ R + 2 ^ 256 = D + P) := by
  intro D R P
  have x0 := Bn.mask_fact hM hm0
  have x1 := Bn.mask_fact hM hm1
  have x3 := Bn.mask_fact hM hm3
  simp only [Bn.toNat_ofNat', Nat.mod_eq_of_lt hP0, Nat.mod_eq_of_lt hP1, Nat.mod_eq_of_lt hP3] at x0 x1 x3
  have a0 := Bn.add_fact' hr0
  have a1 := Bn.add_fact' he1
  have a2 := Bn.add_fact' hr1
  have a3 := Bn.add_fact' hk
  have a4 := Bn.add_fact' hr2
  have a5 := Bn.add_fact' he3
  have a6 := Bn.add_fact' hr3
  have c0 := Bn.ult_fact hk0
  have c1 := Bn.ult_fact hk1
  have c2 := Bn.ult_fact hk1'
  have c3 := Bn.ult_fact hk2
  have := r0.isLt; have := r1.isLt; have := r2.isLt; have := r3.isLt
  have := e1.isLt; have := e3.isLt; have := k.isLt; have := m0.isLt; have := m1.isLt
  have := m3.isLt; have := f0.isLt; have := d1.isLt; have := d2.isLt; have := d3.isLt
  rcases hM with hM | hM <;>
    rcases c0 with ⟨c0, _⟩ | ⟨c0, _⟩ <;> rcases c1 with ⟨c1, _⟩ | ⟨c1, _⟩ <;>
    rcases c2 with ⟨c2, _⟩ | ⟨c2, _⟩ <;> rcases c3 with ⟨c3, _⟩ | ⟨c3, _⟩ <;>
    constructor <;> intro hh <;> omega

/-- The whole `Fp::sub` chain on canonical operands: the result is `Fp.sub A B`. -/
theorem fsub_chain {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    {f0 c0 f1 c1 s d1 c2 bm1 m2 cc2 ff2 d2 c2' t2 bm2 m3 cc3 ff3 d3 c3' t3 M
      m0 r0 k0 m1 e1 k1 r1 k1' k r2 k2 mm3 e3 r3 : Word}
    (hf0 : a0 + -b0 = f0) (hc0 : (if a0.ult b0 = true then 1#64 else 0#64) = c0)
    (hf1 : a1 + -b1 = f1) (hc1 : (if a1.ult b1 = true then 1#64 else 0#64) = c1)
    (hs : c0 + c1 = s) (hd1 : f1 + -c0 = d1)
    (hc2 : (if d1.ult f1 = true then 1#64 else 0#64) = c2) (hbm1 : c2 + -s = bm1)
    (hm2 : bm1.sshiftRight 63 = m2) (hcc2 : (if a2.ult b2 = true then 1#64 else 0#64) = cc2)
    (hff2 : a2 + -b2 = ff2) (hd2 : m2 + ff2 = d2)
    (hc2' : (if d2.ult m2 = true then 1#64 else 0#64) = c2') (ht2 : m2 + -cc2 = t2)
    (hbm2 : t2 + c2' = bm2)
    (hm3 : bm2.sshiftRight 63 = m3) (hcc3 : (if a3.ult b3 = true then 1#64 else 0#64) = cc3)
    (hff3 : a3 + -b3 = ff3) (hd3 : m3 + ff3 = d3)
    (hc3' : (if d3.ult m3 = true then 1#64 else 0#64) = c3') (ht3 : m3 + -cc3 = t3)
    (hM : t3 + c3' = M)
    (hm0 : M &&& 11037532056220336129#64 = m0) (hr0 : m0 + f0 = r0)
    (hk0 : (if r0.ult m0 = true then 1#64 else 0#64) = k0)
    (hm1 : M &&& 2469829653914515739#64 = m1) (he1 : m1 + d1 = e1)
    (hk1 : (if e1.ult m1 = true then 1#64 else 0#64) = k1) (hr1 : e1 + k0 = r1)
    (hk1' : (if r1.ult e1 = true then 1#64 else 0#64) = k1') (hk : k1 + k1' = k)
    (hr2 : k + d2 = r2) (hk2 : (if r2.ult k = true then 1#64 else 0#64) = k2)
    (hmm3 : M &&& 4611686018427387904#64 = mm3) (he3 : mm3 + d3 = e3) (hr3 : e3 + k2 = r3)
    (hA : leLimbsToNat [a0, a1, a2, a3] < Fp.p) (hB : leLimbsToNat [b0, b1, b2, b3] < Fp.p) :
    leLimbsToNat [r0, r1, r2, r3] = Fp.sub (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3]) := by
  have e1s := fsub_s1 hf0 hc0 hf1 hc1 hs hd1 hc2 hbm1
  have hbm1' : bm1.toNat = 0 ∨ bm1.toNat = 2 ^ 64 - 1 := by rcases e1s with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have e2s := fsub_s2 hbm1' hm2 hcc2 hff2 hd2 hc2' ht2 hbm2
  have hbm2' : bm2.toNat = 0 ∨ bm2.toNat = 2 ^ 64 - 1 := by
    rcases hbm1' with h | h
    · rcases e2s.1 h with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    · rcases e2s.2 h with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
  have e3s := fsub_s2 hbm2' hm3 hcc3 hff3 hd3 hc3' ht3 hM
  have hM' : M.toNat = 0 ∨ M.toNat = 2 ^ 64 - 1 := by
    rcases hbm2' with h | h
    · rcases e3s.1 h with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    · rcases e3s.2 h with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
  have e4s := fsub_s4 hM' hm0 hr0 hk0 hm1 he1 hk1 hr1 hk1' hk hr2 hk2 hmm3 he3 hr3
    (by decide) (by decide) (by decide)
  simp only at e4s
  have hp : Fp.p = 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 4611686018427387904 := by
    decide +kernel
  have eA : leLimbsToNat [a0, a1, a2, a3] =
      a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have eB : leLimbsToNat [b0, b1, b2, b3] =
      b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat + 2 ^ 192 * b3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have eR : leLimbsToNat [r0, r1, r2, r3] =
      r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  rw [eA, hp] at hA; rw [eB, hp] at hB
  rw [eA, eB, eR, Fp.sub, hp]
  have := f0.isLt; have := d1.isLt; have := d2.isLt; have := d3.isLt
  have := r0.isLt; have := r1.isLt; have := r2.isLt; have := r3.isLt
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have hDlt : f0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * d3.toNat < 2 ^ 256 := by
    omega
  have hRlt : r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat < 2 ^ 256 := by
    omega
  have hPlt : 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 4611686018427387904 <
      2 ^ 256 := by decide
  -- the difference `D` and the borrow, from the three limb stages
  have key : (M.toNat = 0 ∧
        a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat =
          b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat + 2 ^ 192 * b3.toNat +
            (f0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * d3.toNat)) ∨
      (M.toNat = 2 ^ 64 - 1 ∧
        a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat + 2 ^ 256 =
          b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat + 2 ^ 192 * b3.toNat +
            (f0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * d3.toNat)) := by
    rcases e1s with ⟨h1, e1⟩ | ⟨h1, e1⟩
    · rcases e2s.1 h1 with ⟨h2, e2⟩ | ⟨h2, e2⟩
      · rcases e3s.1 h2 with ⟨h3, e3⟩ | ⟨h3, e3⟩
        · left; exact ⟨h3, by linarith⟩
        · right; exact ⟨h3, by linarith⟩
      · rcases e3s.2 h2 with ⟨h3, e3⟩ | ⟨h3, e3⟩
        · left; exact ⟨h3, by linarith⟩
        · right; exact ⟨h3, by linarith⟩
    · rcases e2s.2 h1 with ⟨h2, e2⟩ | ⟨h2, e2⟩
      · rcases e3s.1 h2 with ⟨h3, e3⟩ | ⟨h3, e3⟩
        · left; exact ⟨h3, by linarith⟩
        · right; exact ⟨h3, by linarith⟩
      · rcases e3s.2 h2 with ⟨h3, e3⟩ | ⟨h3, e3⟩
        · left; exact ⟨h3, by linarith⟩
        · right; exact ⟨h3, by linarith⟩
  generalize a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat = A at *
  generalize b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat + 2 ^ 192 * b3.toNat = B at *
  generalize f0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * d3.toNat = D at *
  generalize r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat = R at *
  generalize 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 4611686018427387904 = P at *
  rcases key with ⟨h0, e⟩ | ⟨h0, e⟩
  · -- no borrow: `R = D = A - B`
    have := e4s.1 h0
    rw [show A + P - B = (A - B) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · -- borrow: `R = D + P - 2^256 = A + P - B`
    rcases e4s.2 h0 with h | h
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

end Cases.Zip2005
