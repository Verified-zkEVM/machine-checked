/-
  Cases.Zip2005.Precompile.Pallas -- `PALLAS_ADD` / `PALLAS_DOUBLE` compute the Pallas group
  law.

  The model (`riscv-zkvm`, `Rv64/Sp1Accel.lean`) computes both precompiles with
  `Accel.curveAddL` / `Accel.curveDblL` over `Sp1.pallasP`: textbook affine
  chord-and-tangent formulas on `Nat`, with the inverse taken by Fermat through
  `Accel.powMod`. This file proves they agree with Mathlib's group law on the
  affine Weierstrass curve `y² = x³ + 5` over `ZMod pallasP`
  (`WeierstrassCurve.Affine.Point`, an `AddCommGroup`), under exactly the side
  conditions the model's `sp1AccelValid` imposes -- coordinates reduced,
  `x₁ ≠ x₂` for an add, `y ≠ 0` for a double -- **plus** that the inputs are on
  the curve, which the model does not check (and neither does the real
  precompile: see the faithfulness notes in `Cases.Zip2005.Precompile.lean`).

  ## Reading a point

  `pointOf x y` is the group element with affine coordinates `(x, y)` when that
  pair satisfies the curve equation, and `0` otherwise. The `0` default is never
  load-bearing: every theorem below also concludes `OnCurve` of its output, so a
  consumer never has to reason through the fallback.
-/

import Cases.Zip2005.Precompile.Prime
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace Cases.Zip2005.Precompile.Pallas

open RiscvZkvm.Rv64 WeierstrassCurve

/-- The Pallas base field. A field by `pallasP_prime`. -/
abbrev F := ZMod Sp1.pallasP

/-- Pallas, `y² = x³ + 5`, as a Weierstrass curve over `F`. -/
def W : WeierstrassCurve F := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 5 }

/-- ...in affine coordinates, where Mathlib's group law lives. -/
abbrev C : Affine F := W.toAffine

theorem W_Δ : W.Δ = -10800 := by
  simp only [W, Δ, b₂, b₄, b₆, b₈]
  ring

instance : W.IsElliptic := by
  refine ⟨Ne.isUnit ?_⟩
  rw [W_Δ, neg_ne_zero]
  have : ((10800 : ℕ) : F) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    simp [Sp1.pallasP] at this
  exact_mod_cast this

/-- The affine equation, on `Nat` coordinates read in `F`. -/
def OnCurve (x y : ℕ) : Prop := C.Equation (x : F) (y : F)

theorem onCurve_iff (x y : ℕ) : OnCurve x y ↔ (y : F) ^ 2 = (x : F) ^ 3 + 5 := by
  simp [OnCurve, Affine.equation_iff, C, W]

/-- The same condition as `Nat` arithmetic -- what a concrete check evaluates. -/
theorem onCurve_iff_nat (x y : ℕ) :
    OnCurve x y ↔ y ^ 2 % Sp1.pallasP = (x ^ 3 + 5) % Sp1.pallasP := by
  rw [onCurve_iff, ← ZMod.natCast_eq_natCast_iff']
  push_cast
  rfl

open Classical in
/-- The group element a coordinate pair denotes (`0` off the curve -- never
    load-bearing, see the module docstring). -/
noncomputable def pointOf (x y : ℕ) : C.Point :=
  if h : OnCurve x y then Affine.Point.mk h else 0

theorem pointOf_of_onCurve {x y : ℕ} (h : OnCurve x y) :
    pointOf x y = .some _ _ (Affine.equation_iff_nonsingular.mp h) := by
  simp [pointOf, h, Affine.Point.mk]

/-! ### `Nat` casts of the model's arithmetic -/

local notation "p" => Sp1.pallasP

theorem p_gt_two : 2 < p := by simp [Sp1.pallasP]
theorem p_lt_two_pow_256 : p < 2 ^ 256 := by simp [Sp1.pallasP]
theorem p_lt : p < 2 ^ 512 := by decide +kernel

theorem cast_inv (x : ℕ) : ((Accel.invMod x p : ℕ) : F) = (x : F)⁻¹ :=
  cast_invMod p_gt_two p_lt x

theorem cast_ne_of_ne {a b : ℕ} (ha : a < p) (hb : b < p) (h : a ≠ b) : (a : F) ≠ (b : F) := by
  rw [ne_eq, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact h

/-- The model's "add `p` before subtracting" idiom is subtraction in `F`. -/
theorem cast_add_p_sub (a : ℕ) {b : ℕ} (hb : b < p) : ((a + p - b : ℕ) : F) = (a : F) - b := by
  rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

/-- The shared tail of both formulas: from a slope `L`, the model forms
    `x₃ = (L² + 2p - x₁ - x₂) mod p` and `y₃ = (L (x₁ - x₃) - y₁) mod p`. -/
theorem cast_tail {L x1 y1 x2 : ℕ} (hx1 : x1 < p) (hy1 : y1 < p) (hx2 : x2 < p) :
    let x3 := (L * L + 2 * p - x1 - x2) % p
    x3 < p ∧ (L * ((x1 + p - x3) % p) + p - y1) % p < p ∧
    (x3 : F) = (L : F) ^ 2 - x1 - x2 ∧
    (((L * ((x1 + p - x3) % p) + p - y1) % p : ℕ) : F) = (L : F) * ((x1 : F) - x3) - y1 := by
  intro x3
  have hp0 : 0 < p := by omega
  have hx3 : x3 < p := Nat.mod_lt _ hp0
  refine ⟨hx3, Nat.mod_lt _ hp0, ?_, ?_⟩
  · simp only [x3]
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast [ZMod.natCast_self]
    ring
  · rw [ZMod.natCast_mod, cast_add_p_sub _ hy1, Nat.cast_mul, ZMod.natCast_mod,
      cast_add_p_sub _ hx3]

/-- `curveAdd` computes, in `F`, `λ = (y₂ - y₁)/(x₂ - x₁)`,
    `x₃ = λ² - x₁ - x₂`, `y₃ = λ(x₁ - x₃) - y₁`, each coordinate reduced. -/
theorem curveAdd_cast {x1 y1 x2 y2 : ℕ} (hx1 : x1 < p) (hy1 : y1 < p) (hx2 : x2 < p) :
    let r := Accel.curveAdd p x1 y1 x2 y2
    let lam : F := ((y2 : F) - y1) * ((x2 : F) - x1)⁻¹
    r.1 < p ∧ r.2 < p ∧
    (r.1 : F) = lam ^ 2 - x1 - x2 ∧ (r.2 : F) = lam * ((x1 : F) - r.1) - y1 := by
  intro r lam
  have hL : (((y2 + p - y1) * Accel.invMod ((x2 + p - x1) % p) p % p : ℕ) : F) = lam := by
    rw [ZMod.natCast_mod, Nat.cast_mul, cast_add_p_sub _ hy1, cast_inv, ZMod.natCast_mod,
      cast_add_p_sub _ hx1]
  obtain ⟨h1, h2, h3, h4⟩ := cast_tail (L := (y2 + p - y1) * Accel.invMod ((x2 + p - x1) % p) p % p)
    hx1 hy1 hx2
  rw [hL] at h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- `curveDbl` computes, in `F`, `λ = 3x₁²/(2y₁)`, `x₃ = λ² - 2x₁`,
    `y₃ = λ(x₁ - x₃) - y₁`, each coordinate reduced. -/
theorem curveDbl_cast {x1 y1 : ℕ} (hx1 : x1 < p) (hy1 : y1 < p) :
    let r := Accel.curveDbl p x1 y1
    let lam : F := 3 * (x1 : F) ^ 2 * (2 * (y1 : F))⁻¹
    r.1 < p ∧ r.2 < p ∧
    (r.1 : F) = lam ^ 2 - x1 - x1 ∧ (r.2 : F) = lam * ((x1 : F) - r.1) - y1 := by
  intro r lam
  have hL : ((3 * x1 * x1 % p * Accel.invMod (2 * y1 % p) p % p : ℕ) : F) = lam := by
    rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, cast_inv, ZMod.natCast_mod]
    push_cast
    simp only [lam]
    ring
  obtain ⟨h1, h2, h3, h4⟩ := cast_tail (L := 3 * x1 * x1 % p * Accel.invMod (2 * y1 % p) p % p)
    hx1 hy1 hx1
  rw [hL] at h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-! ### The group law -/

/-- **Chord addition is the group law.** For reduced, on-curve inputs with
    distinct `x` -- the model's `PALLAS_ADD` validity conditions plus on-curve --
    `curveAdd` returns a reduced, on-curve pair denoting `P + Q`. -/
theorem curveAdd_spec {x1 y1 x2 y2 : ℕ} (hx1 : x1 < p) (hy1 : y1 < p) (hx2 : x2 < p)
    (hne : x1 ≠ x2) (h1 : OnCurve x1 y1) (h2 : OnCurve x2 y2) :
    let r := Accel.curveAdd p x1 y1 x2 y2
    r.1 < p ∧ r.2 < p ∧ OnCurve r.1 r.2 ∧
      pointOf r.1 r.2 = pointOf x1 y1 + pointOf x2 y2 := by
  intro r
  obtain ⟨hr1, hr2, hX, hY⟩ := curveAdd_cast (y2 := y2) hx1 hy1 hx2
  have hne' : (x1 : F) ≠ x2 := cast_ne_of_ne hx1 hx2 hne
  have n1 : C.Nonsingular x1 y1 := Affine.equation_iff_nonsingular.mp h1
  have n2 : C.Nonsingular x2 y2 := Affine.equation_iff_nonsingular.mp h2
  have hslope : C.slope x1 x2 y1 y2 = ((y2 : F) - y1) * ((x2 : F) - x1)⁻¹ := by
    rw [Affine.slope_of_X_ne hne', div_eq_mul_inv, ← neg_sub (y2 : F) y1, ← neg_sub (x2 : F) x1,
      inv_neg, neg_mul_neg]
  have hXe : (r.1 : F) = C.addX x1 x2 (C.slope x1 x2 y1 y2) := by
    rw [hX, hslope]; simp [Affine.addX, C, W]
  have hYe : (r.2 : F) = C.addY x1 x2 y1 (C.slope x1 x2 y1 y2) := by
    rw [hY, hXe, hslope]; simp [Affine.addY, Affine.negAddY, Affine.negY, C, W]; ring
  have hon : OnCurve r.1 r.2 := by
    unfold OnCurve; rw [hXe, hYe]
    exact Affine.equation_add h1 h2 fun h => hne' h.1
  refine ⟨hr1, hr2, hon, ?_⟩
  rw [pointOf_of_onCurve hon, pointOf_of_onCurve h1, pointOf_of_onCurve h2,
    Affine.Point.add_of_X_ne hne']
  simp only [Affine.Point.some.injEq]
  exact ⟨hXe, hYe⟩

/-- **Tangent doubling is the group law.** For a reduced, on-curve input with
    `y ≠ 0` -- the model's `PALLAS_DOUBLE` validity conditions plus on-curve --
    `curveDbl` returns a reduced, on-curve pair denoting `2 • P`. -/
theorem curveDbl_spec {x1 y1 : ℕ} (hx1 : x1 < p) (hy1 : y1 < p) (hy0 : y1 ≠ 0)
    (h1 : OnCurve x1 y1) :
    let r := Accel.curveDbl p x1 y1
    r.1 < p ∧ r.2 < p ∧ OnCurve r.1 r.2 ∧ pointOf r.1 r.2 = 2 • pointOf x1 y1 := by
  intro r
  obtain ⟨hr1, hr2, hX, hY⟩ := curveDbl_cast hx1 hy1
  have hp0 : 0 < p := by simp [Sp1.pallasP]
  have hy0' : (y1 : F) ≠ 0 := by
    have := cast_ne_of_ne hy1 hp0 hy0; rwa [Nat.cast_zero] at this
  have h20 : (2 : F) ≠ 0 := by
    have := cast_ne_of_ne (a := 2) (b := 0) p_gt_two hp0 (by omega)
    rwa [Nat.cast_zero, Nat.cast_ofNat] at this
  have hneg : (y1 : F) ≠ C.negY x1 y1 := by
    simp only [Affine.negY, C, W, sub_zero]
    intro h
    apply mul_ne_zero h20 hy0'
    linear_combination h
  have n1 : C.Nonsingular x1 y1 := Affine.equation_iff_nonsingular.mp h1
  have hslope : C.slope x1 x1 y1 y1 = 3 * (x1 : F) ^ 2 * (2 * (y1 : F))⁻¹ := by
    rw [Affine.slope_of_Y_ne rfl hneg]
    simp only [Affine.negY, C, W, mul_zero, sub_zero, zero_mul, add_zero, div_eq_mul_inv]
    congr 2
    ring
  have hXe : (r.1 : F) = C.addX x1 x1 (C.slope x1 x1 y1 y1) := by
    rw [hX, hslope]; simp [Affine.addX, C, W]
  have hYe : (r.2 : F) = C.addY x1 x1 y1 (C.slope x1 x1 y1 y1) := by
    rw [hY, hXe, hslope]; simp [Affine.addY, Affine.negAddY, Affine.negY, C, W]; ring
  have hon : OnCurve r.1 r.2 := by
    unfold OnCurve; rw [hXe, hYe]
    exact Affine.equation_add h1 h1 fun h => hneg h.2
  refine ⟨hr1, hr2, hon, ?_⟩
  rw [pointOf_of_onCurve hon, pointOf_of_onCurve h1, two_nsmul,
    Affine.Point.add_self_of_Y_ne hneg]
  simp only [Affine.Point.some.injEq]
  exact ⟨hXe, hYe⟩

/-! ### On the wire format -/

/-- The `x` coordinate of a four-limb-per-coordinate `x || y` point. -/
def xOf (pt : List Word) : ℕ := Accel.leLimbsToNat (pt.take 4)
/-- The `y` coordinate of a four-limb-per-coordinate `x || y` point. -/
def yOf (pt : List Word) : ℕ := Accel.leLimbsToNat (pt.drop 4)

theorem ptValid_iff (pt : List Word) :
    Accel.ptValid p 4 pt = true ↔ xOf pt < p ∧ yOf pt < p := by
  simp [Accel.ptValid, xOf, yOf]

/-- Encoding a reduced pair and reading it back. -/
theorem encode_decode {a b : ℕ} (ha : a < p) (hb : b < p) :
    let out := Accel.natToLeLimbs 4 a ++ Accel.natToLeLimbs 4 b
    out.length = 8 ∧ xOf out = a ∧ yOf out = b := by
  have ha' := Nat.lt_trans ha p_lt_two_pow_256
  have hb' := Nat.lt_trans hb p_lt_two_pow_256
  refine ⟨by simp, ?_, ?_⟩
  · simp only [xOf, take_natToLeLimbs_append, leLimbsToNat_natToLeLimbs_four ha']
  · simp only [yOf, drop_natToLeLimbs_append, leLimbsToNat_natToLeLimbs_four hb']

/-- **`PALLAS_ADD` on the wire.** Under the model's validity guard for the
    operation (both points reduced, `x₁ ≠ x₂`) and on-curve inputs, the eight
    limbs the model writes are a reduced, on-curve point denoting `P + Q`. -/
theorem curveAddL_spec (pt1 pt2 : List Word)
    (hv1 : Accel.ptValid p 4 pt1 = true) (hv2 : Accel.ptValid p 4 pt2 = true)
    (hne : xOf pt1 ≠ xOf pt2)
    (h1 : OnCurve (xOf pt1) (yOf pt1)) (h2 : OnCurve (xOf pt2) (yOf pt2)) :
    let out := Accel.curveAddL p 4 pt1 pt2
    out.length = 8 ∧ Accel.ptValid p 4 out = true ∧ OnCurve (xOf out) (yOf out) ∧
      pointOf (xOf out) (yOf out) = pointOf (xOf pt1) (yOf pt1) + pointOf (xOf pt2) (yOf pt2) := by
  rw [ptValid_iff] at hv1 hv2
  obtain ⟨hr1, hr2, hon, hsum⟩ := curveAdd_spec hv1.1 hv1.2 hv2.1 hne h1 h2
  obtain ⟨hlen, hx, hy⟩ := encode_decode hr1 hr2
  have hout : Accel.curveAddL p 4 pt1 pt2 =
      Accel.natToLeLimbs 4 (Accel.curveAdd p (xOf pt1) (yOf pt1) (xOf pt2) (yOf pt2)).1 ++
      Accel.natToLeLimbs 4 (Accel.curveAdd p (xOf pt1) (yOf pt1) (xOf pt2) (yOf pt2)).2 := rfl
  simp only [hout]
  rw [ptValid_iff, hx, hy]
  exact ⟨hlen, ⟨hr1, hr2⟩, hon, hsum⟩

/-- **`PALLAS_DOUBLE` on the wire.** Under the model's validity guard for the
    operation (reduced, `y ≠ 0`) and an on-curve input, the eight limbs the model
    writes are a reduced, on-curve point denoting `2 • P`. -/
theorem curveDblL_spec (pt : List Word) (hv : Accel.ptValid p 4 pt = true) (hy0 : yOf pt ≠ 0)
    (h1 : OnCurve (xOf pt) (yOf pt)) :
    let out := Accel.curveDblL p 4 pt
    out.length = 8 ∧ Accel.ptValid p 4 out = true ∧ OnCurve (xOf out) (yOf out) ∧
      pointOf (xOf out) (yOf out) = 2 • pointOf (xOf pt) (yOf pt) := by
  rw [ptValid_iff] at hv
  obtain ⟨hr1, hr2, hon, hdbl⟩ := curveDbl_spec hv.1 hv.2 hy0 h1
  obtain ⟨hlen, hx, hy⟩ := encode_decode hr1 hr2
  have hout : Accel.curveDblL p 4 pt =
      Accel.natToLeLimbs 4 (Accel.curveDbl p (xOf pt) (yOf pt)).1 ++
      Accel.natToLeLimbs 4 (Accel.curveDbl p (xOf pt) (yOf pt)).2 := rfl
  simp only [hout]
  rw [ptValid_iff, hx, hy]
  exact ⟨hlen, ⟨hr1, hr2⟩, hon, hdbl⟩

end Cases.Zip2005.Precompile.Pallas
