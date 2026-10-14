import Cases.Zip2005.Bridge.SpecJac
import Cases.Zip2005.Bridge.SpecPoint
import Cases.Zip2005.Orchard.NullifierDerive

/-!
# Jacobian triples read as spec points

`specT X Y Z` is the spec point a Jacobian triple of Montgomery representatives denotes (`affD`,
the identity's encodings giving `(0, 0)`). `JacOk` is the invariant `Fp.addJ` needs of its
inputs (`affD_addJ`): `Z` reduced, and the affine reading on the curve when `Z ≠ 0`. It holds of
the identity's encodings and is preserved by `Fp.addJ` (`jacOk_addJ`), so sums chain.
-/

namespace Cases.Zip2005.Poseidon

open RiscvZkvm.Rv64 CompElliptic.CurveForms WeierstrassCurve.Affine
open Zcash.Circuits (Point)

set_option autoImplicit false

/-- The invariant: `Z` reduced, and on the curve when `Z` is not zero. -/
def JacOk (X Y Z : ℕ) : Prop :=
  Z < Fp.p ∧ (D Z ≠ 0 → (D Y / D Z ^ 3) ^ 2 = (D X / D Z ^ 2) ^ 3 + 5)

/-- A Jacobian triple of Montgomery representatives as a spec point. -/
noncomputable def specT (X Y Z : ℕ) : Point Zcash.Circuits.Fp := Point.ofCoords (affD X Y Z)

theorem castD (n : ℕ) : (((n * Fp.rInv % Fp.p : ℕ)) : Zcash.Circuits.Fp) = D n := by
  unfold D; rw [← Fp.p_card, ZMod.natCast_mod, Nat.cast_mul]

theorem specPt_eq (m : List Word) (hz : ptZ m < Fp.p) :
    Cases.Zip2005.SpecMul.specPt m = specT (ptX m) (ptY m) (ptZ m) := by
  unfold Cases.Zip2005.SpecMul.specPt specT Cases.Zip2005.SpecMul.jacXY
  rw [castD, castD, ← D_toAffine _ _ hz]
  rfl

theorem specT_valid {X Y Z : ℕ} (h : JacOk X Y Z) : (specT X Y Z).Valid := by
  unfold specT affD
  split
  · right; rfl
  · left
    show _ ^ 2 = _ ^ 3 + Zcash.Circuits.pallasB
    exact h.2 ‹_›

theorem specT_addJ {X1 Y1 Z1 X2 Y2 Z2 : ℕ} (h1 : JacOk X1 Y1 Z1) (h2 : JacOk X2 Y2 Z2) :
    specT (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).1 (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.1
      (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 = specT X1 Y1 Z1 + specT X2 Y2 Z2 := by
  unfold specT
  rw [affD_addJ h1.1 h2.1 h1.2 h2.2, Point.add_def, Point.ofCoords_coords, Point.ofCoords_coords,
    show Zcash.Circuits.pallasA = 0 from rfl]

/-- Two points on the curve that are not inverses add to a point on the curve. -/
theorem onCurve_add {P Q : F × F} (hP : ShortWeierstrass.OnCurve (0 : F) 5 P)
    (hQ : ShortWeierstrass.OnCurve (0 : F) 5 Q) (hn : ¬(P.1 = Q.1 ∧ P.2 + Q.2 = 0)) :
    ShortWeierstrass.OnCurve (0 : F) 5 (ShortWeierstrass.add 0 P Q) := by
  obtain ⟨x₁, y₁⟩ := P
  obtain ⟨x₂, y₂⟩ := Q
  have h5 : (5 : F) ≠ 0 := by decide
  have hp0 : (x₁, y₁) ≠ (0, 0) := fun h => ShortWeierstrass.not_onCurve_zero (a := (0 : F)) h5 (h ▸ hP)
  have hq0 : (x₂, y₂) ≠ (0, 0) := fun h => ShortWeierstrass.not_onCurve_zero (a := (0 : F)) h5 (h ▸ hQ)
  rw [ShortWeierstrass.add_eq_addXY (b := (5 : F)) hp0 hq0 hn]
  have hneg : negY (ShortWeierstrass.toW (0 : F) 5) x₂ y₂ = -y₂ := by simp [negY]
  have hxy' : ¬(x₁ = x₂ ∧ y₁ = negY (ShortWeierstrass.toW (0 : F) 5) x₂ y₂) := by
    rintro ⟨hx, hyeq⟩
    refine hn ⟨hx, ?_⟩
    rw [hneg] at hyeq; show y₁ + y₂ = 0; rw [hyeq]; ring
  have hns := nonsingular_add (ShortWeierstrass.nonsingular_toW hP)
    (ShortWeierstrass.nonsingular_toW hQ) hxy'
  exact ShortWeierstrass.equation_toW.mp hns.left

theorem addJ_Z_lt {X1 Y1 Z1 X2 Y2 Z2 : ℕ} (h1 : Z1 < Fp.p) (h2 : Z2 < Fp.p) :
    (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 < Fp.p := by
  by_cases hZ1 : Z1 = 0
  · rw [Fp.addJ_z1_zero hZ1]; exact h2
  by_cases hZ2 : Z2 = 0
  · rw [Fp.addJ_z2_zero hZ1 hZ2]; exact h1
  by_cases hu : Fp.mul X1 (Fp.mul Z2 Z2) = Fp.mul X2 (Fp.mul Z1 Z1)
  · by_cases hs : Fp.mul (Fp.mul Y1 (Fp.mul Z2 Z2)) Z2 = Fp.mul (Fp.mul Y2 (Fp.mul Z1 Z1)) Z1
    · rw [Fp.addJ_double hZ1 hZ2 hu hs]
      unfold Fp.dblJ; split
      · exact Fp.p_pos
      · exact Fp.add_lt _ _
    · rw [Fp.addJ_identity hZ1 hZ2 hu hs]; exact Fp.p_pos
  · rw [Fp.addJ_general hZ1 hZ2 hu]
    exact Fp.mul_lt _ _

theorem onCurve_of_eq {x y : F} (h : y ^ 2 = x ^ 3 + 5) : ShortWeierstrass.OnCurve (0 : F) 5 (x, y) := by
  show _ = _ + 0 * _ + 5; rw [zero_mul, add_zero]; exact h

/-- `Fp.addJ` keeps the invariant: a sum is the identity's encoding or a point on the curve. -/
theorem jacOk_addJ {X1 Y1 Z1 X2 Y2 Z2 : ℕ} (h1 : JacOk X1 Y1 Z1) (h2 : JacOk X2 Y2 Z2) :
    JacOk (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).1 (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.1
      (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 := by
  by_cases hz1 : Z1 = 0
  · rw [Fp.addJ_z1_zero hz1]; exact h2
  by_cases hz2 : Z2 = 0
  · rw [Fp.addJ_z2_zero hz1 hz2]; exact h1
  refine ⟨addJ_Z_lt h1.1 h2.1, fun hz3 => ?_⟩
  have hD1 : D Z1 ≠ 0 := D_ne_zero_of h1.1 hz1
  have hD2 : D Z2 ≠ 0 := D_ne_zero_of h2.1 hz2
  have hA := affD_addJ h1.1 h2.1 h1.2 h2.2
  have e1 : affD X1 Y1 Z1 = (D X1 / D Z1 ^ 2, D Y1 / D Z1 ^ 3) := by unfold affD; rw [if_neg hD1]
  have e2 : affD X2 Y2 Z2 = (D X2 / D Z2 ^ 2, D Y2 / D Z2 ^ 3) := by unfold affD; rw [if_neg hD2]
  have e3 : affD (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).1 (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.1
      (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 =
      (D (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).1 / D (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 ^ 2,
        D (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.1 / D (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 ^ 3) := by
    unfold affD; rw [if_neg hz3]
  rw [e1, e2, e3] at hA
  have hn : ¬ (D X1 / D Z1 ^ 2 = D X2 / D Z2 ^ 2 ∧ D Y1 / D Z1 ^ 3 + D Y2 / D Z2 ^ 3 = 0) := by
    rintro ⟨hx, hy⟩
    rw [div_eq_div_iff (pow_ne_zero 2 hD1) (pow_ne_zero 2 hD2)] at hx
    have hu : Fp.mul X1 (Fp.mul Z2 Z2) = Fp.mul X2 (Fp.mul Z1 Z1) :=
      D_inj (Fp.mul_lt _ _) (Fp.mul_lt _ _) (by rw [D_mul, D_mul, D_mul, D_mul]; linear_combination hx)
    by_cases hs : Fp.mul (Fp.mul Y1 (Fp.mul Z2 Z2)) Z2 = Fp.mul (Fp.mul Y2 (Fp.mul Z1 Z1)) Z1
    · have hs' := congrArg D hs
      rw [D_mul, D_mul, D_mul, D_mul, D_mul, D_mul] at hs'
      rw [div_add_div _ _ (pow_ne_zero 3 hD1) (pow_ne_zero 3 hD2), div_eq_zero_iff] at hy
      have hy' := hy.resolve_right (mul_ne_zero (pow_ne_zero 3 hD1) (pow_ne_zero 3 hD2))
      have h2y : 2 * (D Y1 * D Z2 ^ 3) = 0 := by linear_combination hy' + hs'
      have hY0 : D Y1 = 0 := by
        rcases mul_eq_zero.mp h2y with h | h
        · exact absurd h two_ne_zero_F
        · exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 3 hD2)
      exact y_ne_zero_of_onCurve (h1.2 hD1) (by rw [hY0, zero_div])
    · rw [Fp.addJ_identity hz1 hz2 hu hs] at hz3
      exact hz3 D_zero
  have hon := onCurve_add (onCurve_of_eq (h1.2 hD1)) (onCurve_of_eq (h2.2 hD2)) hn
  rw [← hA] at hon
  have := hon
  simp only [ShortWeierstrass.OnCurve, zero_mul, add_zero] at this
  exact this

end Cases.Zip2005.Poseidon
