import Cases.Zip2005.Bridge.SpecMul
import Cases.Zip2005.Spec.Zip2005.Imported
import Cases.Zip2005.Precompile

/-!
# Points of the guest's words as the spec's `Point Fp`

`specPt m` is the spec point (`Zcash.Circuits.Point Fp`) a twelve-word Jacobian point in
Montgomery form denotes: its affine coordinates out of Montgomery form, with the identity's
encodings giving `(0, 0)`, the spec's identity sentinel. `grp` reads a spec point into Mathlib's
group on the same curve (CompElliptic's `toPt`), which is definitionally `Cases.Zip2005.Precompile.Pallas.C`, the
group `Cases.Zip2005.SpecMul` works in.

`specPt_mulW`: the model of `Ep::mul` is the spec's `Zip2005.smul` by the scalar out of Montgomery
form, for an input that is a valid spec point.
-/

namespace Cases.Zip2005.SpecMul

open RiscvZkvm.Rv64 Cases.Zip2005.Precompile.Pallas MachineChecked.RiscV.Wire CompElliptic.CurveForms
open Zcash.Circuits (Fp Fq Point)

/-- Mathlib's group on the spec's curve `y² = x³ + 5` (definitionally `Cases.Zip2005.Precompile.Pallas.C`). -/
abbrev G := WeierstrassCurve.Affine.Point (ShortWeierstrass.toW (0 : Fp) 5)

instance instEll : (ShortWeierstrass.toW (0 : Fp) 5).IsElliptic := inferInstanceAs W.IsElliptic
instance instEll' : (ShortWeierstrass.toW Zcash.Circuits.pallasA 5).IsElliptic :=
  inferInstanceAs W.IsElliptic

/-- The spec point a twelve-word Jacobian point (Montgomery form) denotes. The identity's
encodings give `(0, 0)`, the spec's identity sentinel. -/
def specPt (m : List Word) : Point Fp := ⟨((jacXY m).1 : Fp), ((jacXY m).2 : Fp)⟩

/-- A spec point read into Mathlib's group. -/
noncomputable def grp (P : Point Fp) : G := ShortWeierstrass.toPt (0 : Fp) 5 P.coords

theorem onCurve_iff_sw (x y : ℕ) :
    OnCurve x y ↔ ShortWeierstrass.OnCurve (0 : Fp) 5 ((x : Fp), (y : Fp)) := by
  rw [OnCurve, ← ShortWeierstrass.equation_toW]; rfl

theorem pointOf_eq_grp (x y : ℕ) : (pointOf x y : G) = grp ⟨(x : Fp), (y : Fp)⟩ := by
  unfold pointOf grp ShortWeierstrass.toPt Point.coords
  by_cases h : OnCurve x y
  · rw [dif_pos h, dif_pos ((onCurve_iff_sw x y).mp h)]; rfl
  · rw [dif_neg h, dif_neg (fun h' => h ((onCurve_iff_sw x y).mpr h'))]; rfl

theorem jacPt_eq_grp (m : List Word) : (jacPt m : G) = grp (specPt m) := pointOf_eq_grp _ _

theorem five_ne_zero : (5 : Fp) ≠ 0 := by decide

theorem grp_smul (n : ℕ) {P : Point Fp} (hP : P.Valid) : grp (n • P) = n • grp P := by
  have hv : ShortWeierstrass.Valid (0 : Fp) 5 P.coords := (Point.valid_iff P).mp hP
  induction n with
  | zero =>
    show ShortWeierstrass.toPt (0 : Fp) 5 (ShortWeierstrass.smul 0 0 P.coords) = (0 : ℕ) • grp P
    rw [zero_nsmul]; exact ShortWeierstrass.toPt_zero five_ne_zero
  | succ n ih =>
    show ShortWeierstrass.toPt (0 : Fp) 5 (ShortWeierstrass.smul 0 (n + 1) P.coords) =
      (n + 1) • grp P
    rw [ShortWeierstrass.smul,
      ShortWeierstrass.toPt_add five_ne_zero (ShortWeierstrass.valid_smul hv n) hv, succ_nsmul]
    congr 1

/-- `grp` is injective on valid points. -/
theorem grp_inj {P Q : Point Fp} (hP : P.Valid) (hQ : Q.Valid) (h : grp P = grp Q) : P = Q := by
  have e1 := ShortWeierstrass.ofPt_toPt five_ne_zero ((Point.valid_iff P).mp hP)
  have e2 := ShortWeierstrass.ofPt_toPt five_ne_zero ((Point.valid_iff Q).mp hQ)
  apply Point.ext_coords
  calc P.coords = ShortWeierstrass.ofPt (ShortWeierstrass.toPt (0 : Fp) 5 P.coords) := e1.symm
    _ = ShortWeierstrass.ofPt (ShortWeierstrass.toPt (0 : Fp) 5 Q.coords) := congrArg _ h
    _ = Q.coords := e2


theorem specPt_valid {m : List Word}
    (h : OnCurve (jacXY m).1 (jacXY m).2 ∨ jacXY m = (0, 0)) : (specPt m).Valid := by
  rcases h with h | h
  · left
    rw [Point.onCurve_iff]
    exact (onCurve_iff_sw _ _).mp h
  · right
    unfold specPt; rw [h]; rfl

theorem jacXY_of_Z {m : List Word} (hz : ptZ m = 0) : jacXY m = (0, 0) := by
  unfold jacXY; rw [hz, toAffine_Z_zero]; rfl

/-- `mulW`'s output is a valid spec point. -/
theorem mulW_valid (pt k : List Word) (hb : ptZ pt ≠ 0 → ValidA (mulBase pt)) (hf : mulFacts pt k) :
    (specPt (mulW pt k)).Valid := by
  apply specPt_valid
  by_cases hz : ptZ pt = 0
  · right; rw [mulW, if_pos hz]; exact jacXY_of_Z ptZ_replicate
  obtain ⟨hok, hcan⟩ := hf hz
  obtain ⟨hSv, -⟩ := mulSum_spec pt k (hb hz) hok
  rw [mulW, if_neg hz]
  by_cases h0 : (mulSum pt k)[0]! = 0
  · right; rw [if_pos h0]; exact jacXY_of_Z ptZ_replicate
  rw [if_neg h0]
  left
  obtain ⟨hxl, hyl⟩ := hcan h0
  obtain ⟨ht, hd⟩ := drop1_take4 hSv.1
  have hxs := Fp.mul_lt (Accel.leLimbsToNat [(mulSum pt k)[1]!, (mulSum pt k)[2]!,
    (mulSum pt k)[3]!, (mulSum pt k)[4]!]) Fp.R2
  have hys := Fp.mul_lt (Accel.leLimbsToNat [(mulSum pt k)[5]!, (mulSum pt k)[6]!,
    (mulSum pt k)[7]!, (mulSum pt k)[8]!]) Fp.R2
  obtain ⟨cx, cy, cz⟩ := cells3 _ _ _ (lt_trans hxs Fp.p_lt) (lt_trans hys Fp.p_lt)
    (lt_trans Fp.R_lt Fp.p_lt)
  have hc := (hSv.2 h0).2
  unfold jacXY
  rw [cx, cy, cz, Fp.toAffine, if_pos rfl]
  simp only
  rw [mont_in_out _ hxl, mont_in_out _ hyl]
  rw [xOf, yOf, ht, hd] at hc
  exact hc

theorem valid_nsmul (n : ℕ) {P : Point Fp} (hP : P.Valid) : (n • P).Valid :=
  (Point.valid_iff _).mpr (ShortWeierstrass.valid_smul ((Point.valid_iff _).mp hP) n)

/-- The two readings of Mathlib's group agree on `n • x`. -/
theorem smul_CG (n : ℕ) (x : C.Point) : ((n • x : C.Point) : G) = n • (x : G) := rfl

/-- `mulW_spec` in the spec curve's group. -/
theorem mulW_spec_G (pt k : List Word) (hb : ptZ pt ≠ 0 → ValidA (mulBase pt)) (hf : mulFacts pt k) :
    (jacPt (mulW pt k) : G) = (Accel.leLimbsToNat k * Fq.rInv % Fq.q) • (jacPt pt : G) := by
  rw [← smul_CG]
  exact congrArg (fun x : C.Point => (x : G)) (mulW_spec pt k hb hf)

/-- **`Ep::mul`'s model is the spec's scalar multiplication** `Zip2005.smul`, for an input that is a
valid spec point and the scalar out of Montgomery form. -/
theorem specPt_mulW (pt k : List Word) (hb : ptZ pt ≠ 0 → ValidA (mulBase pt))
    (hf : mulFacts pt k) (hP : (specPt pt).Valid) :
    specPt (mulW pt k) =
      Zip2005.smul ((Accel.leLimbsToNat k * Fq.rInv % Fq.q : ℕ) : Fq) (specPt pt) := by
  have hlt : Accel.leLimbsToNat k * Fq.rInv % Fq.q < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD :=
    Nat.mod_lt _ Fq.q_pos
  have hn : (((Accel.leLimbsToNat k * Fq.rInv % Fq.q : ℕ) : Fq)).val =
      Accel.leLimbsToNat k * Fq.rInv % Fq.q := ZMod.val_cast_of_lt hlt
  unfold Zip2005.smul
  rw [hn]
  apply grp_inj (mulW_valid pt k hb hf) (valid_nsmul _ hP)
  rw [grp_smul _ hP, ← jacPt_eq_grp, ← jacPt_eq_grp]
  exact mulW_spec_G pt k hb hf

end Cases.Zip2005.SpecMul
