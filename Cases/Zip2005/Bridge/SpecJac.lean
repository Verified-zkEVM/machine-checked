import Cases.Zip2005.Bridge.PoseidonBridge
import Cases.Zip2005.Curve.EpModel
import Cases.Zip2005.Bridge.SpecMul
import Cases.Zip2005.Precompile

/-!
# The guest's Jacobian arithmetic is the spec's group law

Montgomery representatives read in `Fp` through `D n = n · R⁻¹` (`Proof/Spec/PoseidonBridge.lean`): here
subtraction (`D_sub`) and `Fp::invert` (`D_invert`, Fermat through the square-and-multiply
chain), then points. `affD X Y Z` is the affine point a Jacobian triple stands for, `(0, 0)` for
the identity, the spec's sentinel. On points on the curve (or the identity):

- `affD_dblJ`: `Ep::double` (`dbl-2009-l`) is `ShortWeierstrass.add 0 P P`;
- `affD_addJ`: `Ep::add` (`add-2007-bl` and its four special cases) is `ShortWeierstrass.add 0 P Q`,
  the spec's complete addition (`Zcash.Circuits.Point.add`); the general case is the identity
  `add2007bl` over free variables;
- `D_toAffine`: `Ep::to_affine` gives `affD`'s coordinates.

`y_ne_zero_of_onCurve` (no Pallas point has `y = 0`) rules out the degenerate doubling.
-/

namespace Cases.Zip2005.Poseidon
theorem D_sub (a b : Nat) (hb : b < Fp.p) : D (Fp.sub a b) = D a - D b := by
  have hle : b ≤ a + Fp.p := by omega
  unfold D Fp.sub
  have hle' : b ≤ a + CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by rw [Fp.p_card]; exact hle
  rw [← Fp.p_card, ZMod.natCast_mod, Nat.cast_sub hle', Nat.cast_add, ZMod.natCast_self]
  ring

theorem D_sqmul (x a : Nat) (b : Bool) :
    D (Fp.sqmul x a b) = D a ^ 2 * D x ^ (if b then 1 else 0) := by
  unfold Fp.sqmul
  cases b
  · simp only [Bool.false_eq_true, if_false, D_mul, pow_zero, mul_one]; ring
  · simp only [if_true, D_mul, pow_one]; ring

theorem mod_two_pow_succ' (e i : Nat) :
    e % 2 ^ (i + 1) = (if e.testBit i then 1 else 0) * 2 ^ i + e % 2 ^ i := by
  rw [Nat.pow_succ, Nat.mod_mul, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ i) with h | h
  · simp [h]
  · simp [h]; ring

theorem D_powBits (x e : Nat) : ∀ i a, D (Fp.powBits x e i a) = D a ^ (2 ^ i) * D x ^ (e % 2 ^ i)
  | 0, a => by simp [Fp.powBits, Nat.mod_one]
  | i + 1, a => by
    rw [Fp.powBits, D_powBits x e i, D_sqmul, mod_two_pow_succ']
    generalize (if e.testBit i = true then 1 else 0) = c
    rw [pow_succ 2 i]
    ring

theorem D_powBitsV (x e : Nat) : ∀ i a f, (f = false → D a = 1) →
    D (Fp.powBitsV x e i a f) = D (Fp.powBits x e i a)
  | 0, _, _, _ => rfl
  | i + 1, a, true, _ => by rw [Fp.powBitsV_true]
  | i + 1, a, false, h => by
    have ha := h rfl
    by_cases hb : e.testBit i = true
    · rw [Fp.powBitsV_set a false hb, Fp.powBitsV_true, Fp.powBits, Fp.sqmul, if_pos hb]
      simp only [Bool.false_eq_true, if_false]
      rw [D_powBits, D_powBits, D_mul, D_mul, D_mul, ha]
      ring
    · have hb' : e.testBit i = false := by simpa using hb
      rw [Fp.powBitsV_clear a false hb', Fp.powBits, Fp.sqmul, if_neg hb]
      simp only [Bool.false_eq_true, if_false]
      rw [D_powBitsV x e i a false (fun _ => ha), D_powBits, D_powBits, D_mul, ha]
      ring

theorem pow_p_sub_two (y : F) : y ^ (Fp.p - 2) = y⁻¹ := by
  by_cases hy : y = 0
  · subst hy
    rw [inv_zero, zero_pow (by decide +kernel)]
  · have h1 := ZMod.pow_card_sub_one_eq_one hy
    have e : Fp.p - 2 + 1 = CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - 1 := by
      rw [Fp.p_card]; decide +kernel
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, e, h1]

/-- `Fp::invert` is the field inverse on the values its representatives stand for. -/
theorem D_invert (x : Nat) : D (Fp.invert x) = (D x)⁻¹ := by
  unfold Fp.invert
  rw [D_powBits, D_powBits, D_powBits, D_powBitsV x _ 64 Fp.R false (fun _ => D_R), D_powBits, D_R,
    one_pow, one_mul, ← pow_p_sub_two]
  simp only [← pow_mul, ← pow_add]
  congr 1


open CompElliptic.CurveForms

/-- The affine point a Jacobian triple of representatives stands for, `(0, 0)` for the
identity (`Z = 0`). -/
noncomputable def affD (X Y Z : ℕ) : F × F :=
  if D Z = 0 then (0, 0) else (D X / D Z ^ 2, D Y / D Z ^ 3)

theorem D_ne_zero_of {n : ℕ} (hn : n < Fp.p) (h0 : n ≠ 0) : D n ≠ 0 := by
  unfold D
  have hr : (Fp.rInv : F) ≠ 0 := by
    intro h
    have := D_R
    unfold D at this
    rw [h, mul_zero] at this; exact zero_ne_one this
  refine mul_ne_zero ?_ hr
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact h0 (Nat.eq_zero_of_dvd_of_lt (Fp.p_card ▸ h) hn)

/-- No point of `y² = x³ + 5` over `Fp` has `y = 0`. -/
theorem y_ne_zero_of_onCurve {x y : F} (h : y ^ 2 = x ^ 3 + 5) : y ≠ 0 := by
  intro hy
  apply Cases.Zip2005.SpecMul.onCurve_y_ne_zero (x := x.val)
  rw [Cases.Zip2005.Precompile.Pallas.onCurve_iff]
  have hx : ((x.val : ℕ) : Cases.Zip2005.Precompile.Pallas.F) = x := ZMod.natCast_zmod_val x
  rw [hx]
  rw [hy] at h
  simp only [Nat.cast_zero]
  exact h

theorem Z_eq_zero_of_D {n : ℕ} (hn : n < Fp.p) (h : D n = 0) : n = 0 := by
  by_contra h0; exact D_ne_zero_of hn h0 h

theorem two_ne_zero_F : (2 : F) ≠ 0 := by decide

/-- **`Ep::double` is doubling** on the affine points the representatives stand for. -/
theorem affD_dblJ {X Y Z : ℕ} (hZ : Z < Fp.p)
    (hc : D Z ≠ 0 → (D Y / D Z ^ 3) ^ 2 = (D X / D Z ^ 2) ^ 3 + 5) :
    affD (Fp.dblJ X Y Z).1 (Fp.dblJ X Y Z).2.1 (Fp.dblJ X Y Z).2.2 =
      ShortWeierstrass.add 0 (affD X Y Z) (affD X Y Z) := by
  by_cases hz : D Z = 0
  · have hz0 := Z_eq_zero_of_D hZ hz
    have e : affD X Y Z = (0, 0) := by unfold affD; rw [if_pos hz]
    rw [e, ShortWeierstrass.zero_add]
    simp only [Fp.dblJ, if_pos hz0]
    unfold affD; rw [D_zero, if_pos rfl]
  have hz0 : Z ≠ 0 := fun h => hz (by rw [h, D_zero])
  have hon := hc hz
  have hy : D Y / D Z ^ 3 ≠ 0 := y_ne_zero_of_onCurve hon
  have hY : D Y ≠ 0 := fun h => hy (by rw [h, zero_div])
  have e : affD X Y Z = (D X / D Z ^ 2, D Y / D Z ^ 3) := by unfold affD; rw [if_neg hz]
  rw [e]
  unfold ShortWeierstrass.add
  have hne : (D X / D Z ^ 2, D Y / D Z ^ 3) ≠ ((0 : F), (0 : F)) := by
    intro h; exact hy (Prod.mk.inj h).2
  rw [if_neg hne, if_neg hne, if_pos rfl, if_neg (by
    intro h; apply hy; have : (2 : F) * (D Y / D Z ^ 3) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero_F)]
  simp only [Fp.dblJ, if_neg hz0]
  unfold affD
  simp only [D_mul, D_add, D_sub _ _ (Fp.mul_lt _ _), D_sub _ _ (Fp.add_lt _ _),
    D_sub _ _ (Fp.sub_lt _ _)]
  have hZ3 : D Z * D Y + D Z * D Y ≠ 0 := by
    rw [← two_mul]; exact mul_ne_zero two_ne_zero_F (mul_ne_zero hz hY)
  rw [if_neg hZ3]
  have h2 : (2 : F) ≠ 0 := two_ne_zero_F
  have h4 : (4 : F) ≠ 0 := by decide
  have h8 : (8 : F) ≠ 0 := by decide
  simp only [Prod.mk.injEq]
  constructor
  · field_simp
    linear_combination (9 * D X ^ 4 - 8 * D X * D Y ^ 2) * inv_mul_cancel₀ h4
  · field_simp
    linear_combination (36 * D X ^ 3 * D Y ^ 2 - 27 * D X ^ 6 - 8 * D Y ^ 4) * inv_mul_cancel₀ h8

theorem rInv_ne_zero : (Fp.rInv : F) ≠ 0 := by
  intro h
  have := D_R
  unfold D at this
  rw [h, mul_zero] at this; exact zero_ne_one this

theorem D_inj {a b : ℕ} (ha : a < Fp.p) (hb : b < Fp.p) (h : D a = D b) : a = b := by
  unfold D at h
  have h' : (a : F) = (b : F) := mul_right_cancel₀ rInv_ne_zero h
  have ha' : a < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by rw [Fp.p_card]; exact ha
  have hb' : b < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by rw [Fp.p_card]; exact hb
  rw [← ZMod.val_cast_of_lt ha', ← ZMod.val_cast_of_lt hb', h']

theorem add2007bl (a1 b1 c1 a2 b2 c2 : F) (hc1 : c1 ≠ 0) (hc2 : c2 ≠ 0)
    (hh : a2 * c1 ^ 2 - a1 * c2 ^ 2 ≠ 0) (h2 : (2 : F) ≠ 0) :
    let h := a2 * (c1 * c1) - a1 * (c2 * c2)
    let i := (h + h) * (h + h)
    let j := h * i
    let r := (b2 * (c1 * c1) * c1 - b1 * (c2 * c2) * c2) + (b2 * (c1 * c1) * c1 - b1 * (c2 * c2) * c2)
    let v := a1 * (c2 * c2) * i
    let x3 := r * r - j - v - v
    let y3 := r * (v - x3) - (b1 * (c2 * c2) * c2 * j + b1 * (c2 * c2) * c2 * j)
    let z3 := ((c1 + c2) * (c1 + c2) - c1 * c1 - c2 * c2) * h
    x3 / z3 ^ 2 = ((b2 / c2 ^ 3 - b1 / c1 ^ 3) / (a2 / c2 ^ 2 - a1 / c1 ^ 2)) ^ 2 - a1 / c1 ^ 2 - a2 / c2 ^ 2 ∧
    y3 / z3 ^ 3 = ((b2 / c2 ^ 3 - b1 / c1 ^ 3) / (a2 / c2 ^ 2 - a1 / c1 ^ 2)) *
      (a1 / c1 ^ 2 - (((b2 / c2 ^ 3 - b1 / c1 ^ 3) / (a2 / c2 ^ 2 - a1 / c1 ^ 2)) ^ 2 - a1 / c1 ^ 2 - a2 / c2 ^ 2)) -
      b1 / c1 ^ 3 := by
  intro h i j r v x3 y3 z3
  obtain ⟨d, rfl⟩ : ∃ d, a2 = (d + a1 * c2 ^ 2) / c1 ^ 2 :=
    ⟨a2 * c1 ^ 2 - a1 * c2 ^ 2, by field_simp; ring⟩
  have hd : d ≠ 0 := by
    intro h0; apply hh; rw [h0]; field_simp; ring
  have hh' : h = d := by simp only [h]; field_simp; ring
  have hz : z3 = 2 * c1 * c2 * d := by simp only [z3]; rw [hh']; ring
  have hden : (d + a1 * c2 ^ 2) / c1 ^ 2 / c2 ^ 2 - a1 / c1 ^ 2 = d / (c1 ^ 2 * c2 ^ 2) := by
    field_simp; ring
  simp only [x3, y3, v, j, i, r, hz, hh']
  rw [hden]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **`Ep::add` is the group law** on the affine points the representatives stand for. -/
theorem affD_addJ {X1 Y1 Z1 X2 Y2 Z2 : ℕ} (hZ1 : Z1 < Fp.p) (hZ2 : Z2 < Fp.p)
    (hc1 : D Z1 ≠ 0 → (D Y1 / D Z1 ^ 3) ^ 2 = (D X1 / D Z1 ^ 2) ^ 3 + 5)
    (hc2 : D Z2 ≠ 0 → (D Y2 / D Z2 ^ 3) ^ 2 = (D X2 / D Z2 ^ 2) ^ 3 + 5) :
    affD (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).1 (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.1
        (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 =
      ShortWeierstrass.add 0 (affD X1 Y1 Z1) (affD X2 Y2 Z2) := by
  by_cases hz1 : Z1 = 0
  · rw [Fp.addJ_z1_zero hz1]
    have e : affD X1 Y1 Z1 = (0, 0) := by unfold affD; rw [hz1, D_zero, if_pos rfl]
    rw [e, ShortWeierstrass.zero_add]
  by_cases hz2 : Z2 = 0
  · rw [Fp.addJ_z2_zero hz1 hz2]
    have e : affD X2 Y2 Z2 = (0, 0) := by unfold affD; rw [hz2, D_zero, if_pos rfl]
    rw [e, ShortWeierstrass.add_zero]
  have d1 : D Z1 ≠ 0 := D_ne_zero_of hZ1 hz1
  have d2 : D Z2 ≠ 0 := D_ne_zero_of hZ2 hz2
  have on1 := hc1 d1
  have on2 := hc2 d2
  have e1 : affD X1 Y1 Z1 = (D X1 / D Z1 ^ 2, D Y1 / D Z1 ^ 3) := by unfold affD; rw [if_neg d1]
  have e2 : affD X2 Y2 Z2 = (D X2 / D Z2 ^ 2, D Y2 / D Z2 ^ 3) := by unfold affD; rw [if_neg d2]
  have y1 : D Y1 / D Z1 ^ 3 ≠ 0 := y_ne_zero_of_onCurve on1
  have y2 : D Y2 / D Z2 ^ 3 ≠ 0 := y_ne_zero_of_onCurve on2
  have n1 : (D X1 / D Z1 ^ 2, D Y1 / D Z1 ^ 3) ≠ ((0 : F), (0 : F)) := fun h => y1 (Prod.mk.inj h).2
  have n2 : (D X2 / D Z2 ^ 2, D Y2 / D Z2 ^ 3) ≠ ((0 : F), (0 : F)) := fun h => y2 (Prod.mk.inj h).2
  -- `u1 = u2` is equality of `x`, `s1 = s2` of `y`
  have hu : Fp.mul X1 (Fp.mul Z2 Z2) = Fp.mul X2 (Fp.mul Z1 Z1) ↔
      D X1 / D Z1 ^ 2 = D X2 / D Z2 ^ 2 := by
    constructor
    · intro h
      have := congrArg D h
      simp only [D_mul] at this
      field_simp
      linear_combination this
    · intro h
      apply D_inj (Fp.mul_lt _ _) (Fp.mul_lt _ _)
      simp only [D_mul]
      field_simp at h
      linear_combination h
  have hs : Fp.mul (Fp.mul Y1 (Fp.mul Z2 Z2)) Z2 = Fp.mul (Fp.mul Y2 (Fp.mul Z1 Z1)) Z1 ↔
      D Y1 / D Z1 ^ 3 = D Y2 / D Z2 ^ 3 := by
    constructor
    · intro h
      have := congrArg D h
      simp only [D_mul] at this
      field_simp
      linear_combination this
    · intro h
      apply D_inj (Fp.mul_lt _ _) (Fp.mul_lt _ _)
      simp only [D_mul]
      field_simp at h
      linear_combination h
  rw [e1, e2]
  by_cases hx : Fp.mul X1 (Fp.mul Z2 Z2) = Fp.mul X2 (Fp.mul Z1 Z1)
  · by_cases hy : Fp.mul (Fp.mul Y1 (Fp.mul Z2 Z2)) Z2 = Fp.mul (Fp.mul Y2 (Fp.mul Z1 Z1)) Z1
    · rw [Fp.addJ_double hz1 hz2 hx hy, affD_dblJ hZ1 hc1, e1]
      rw [hu.mp hx, hs.mp hy]
    · rw [Fp.addJ_identity hz1 hz2 hx hy]
      have hxe := hu.mp hx
      have hye : D Y1 / D Z1 ^ 3 ≠ D Y2 / D Z2 ^ 3 := fun h => hy (hs.mpr h)
      unfold ShortWeierstrass.add
      rw [if_neg n1, if_neg n2, if_pos hxe]
      have hsum : D Y1 / D Z1 ^ 3 + D Y2 / D Z2 ^ 3 = 0 := by
        have hsq : (D Y1 / D Z1 ^ 3) ^ 2 = (D Y2 / D Z2 ^ 3) ^ 2 := by rw [on1, on2, hxe]
        have hm : (D Y1 / D Z1 ^ 3 - D Y2 / D Z2 ^ 3) * (D Y1 / D Z1 ^ 3 + D Y2 / D Z2 ^ 3) = 0 := by
          linear_combination hsq
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hye)
      rw [if_pos hsum]
      unfold affD; rw [D_zero, if_pos rfl]
  · rw [Fp.addJ_general hz1 hz2 hx]
    have hxe : D X1 / D Z1 ^ 2 ≠ D X2 / D Z2 ^ 2 := fun h => hx (hu.mpr h)
    unfold ShortWeierstrass.add
    rw [if_neg n1, if_neg n2, if_neg hxe]
    unfold Fp.addJ_main affD
    simp only [D_mul, D_add, D_sub _ _ (Fp.mul_lt _ _), D_sub _ _ (Fp.add_lt _ _),
      D_sub _ _ (Fp.sub_lt _ _)]
    have hdx : D X2 * D Z1 ^ 2 - D X1 * D Z2 ^ 2 ≠ 0 := by
      intro h; apply hxe; field_simp; linear_combination -h
    have hZ3 : ((D Z1 + D Z2) * (D Z1 + D Z2) - D Z1 * D Z1 - D Z2 * D Z2) *
        (D X2 * (D Z1 * D Z1) - D X1 * (D Z2 * D Z2)) ≠ 0 := by
      have : ((D Z1 + D Z2) * (D Z1 + D Z2) - D Z1 * D Z1 - D Z2 * D Z2) = 2 * D Z1 * D Z2 := by ring
      rw [this]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero_F d1) d2) ?_
      convert hdx using 1; ring
    rw [if_neg hZ3]
    obtain ⟨hX3, hY3⟩ := add2007bl (D X1) (D Y1) (D Z1) (D X2) (D Y2) (D Z2) d1 d2 hdx two_ne_zero_F
    simp only [Prod.mk.injEq]
    exact ⟨hX3, hY3⟩

theorem D_invert_ne_zero {Z : ℕ} (hZ : Z < Fp.p) (hz : Z ≠ 0) : Fp.invert Z ≠ 0 := by
  intro h
  have := D_invert Z
  rw [h, D_zero] at this
  exact inv_ne_zero (D_ne_zero_of hZ hz) this.symm

/-- `Ep::to_affine` on representatives is the affine reading `affD`. -/
theorem D_toAffine (X Y : ℕ) {Z : ℕ} (hZ : Z < Fp.p) :
    (D (Fp.toAffine X Y Z).1, D (Fp.toAffine X Y Z).2) = affD X Y Z := by
  unfold Fp.toAffine affD
  by_cases hR : Z = Fp.R
  · rw [if_pos hR, hR, D_R, if_neg one_ne_zero, one_pow, one_pow, div_one, div_one]
  rw [if_neg hR]
  by_cases hz : Z = 0
  · rw [if_pos hz, if_pos rfl, hz, D_zero, if_pos rfl]
  have hinv := D_invert Z
  have hne := D_invert_ne_zero hZ hz
  generalize Fp.invert Z = zi at hinv hne ⊢
  simp only [if_neg hz, if_neg hne, if_neg (D_ne_zero_of hZ hz), D_mul, hinv, Prod.mk.injEq]
  constructor <;> field_simp

end Cases.Zip2005.Poseidon
