import Cases.Zip2005.Precompile.Pallas
import Cases.Zip2005.Precompile.PowMod

import Cases.Zip2005.Curve.MulModel

/-!
# `Ep::mul`'s model is scalar multiplication

The bridge from `Cases.Zip2005.mulW` (the twelve Montgomery-form words `sp1_pallas::zkvm::mul` returns,
`Proof/Curve/MulModel.lean`) to the group law: `mulW_spec` says the point it denotes is `[s] P` for the
point `P` the input denotes and the scalar `s` out of Montgomery form. Points are read into
Mathlib's affine Weierstrass group over `ZMod p` (`Cases.Zip2005.Precompile.Pallas.C`), through the accelerator
lemmas `curveAddL_spec` / `curveDblL_spec`:

- `completeAddW_spec`: the guest's complete addition on tagged nine-word points is the group sum
  (identity tags, doubling, inverse pairs, distinct `x`), using `onCurve_y_ne_zero` (no Pallas
  point has `y = 0`: `-5` is not a cube mod `p`);
- `mulLoop_spec`: the double-and-add loop keeps `acc + [bits] base`;
- `mulSum_spec`: the fixed offset `Q` and `-Q` cancel and the 255 bits spell the canonical scalar;
- `mulW_spec`: with `jacPt` (affine coordinates out of Montgomery form, the identity's encodings
  read as `0`).

The hypotheses are the run's own facts (`mulFacts`) and that the input's affine point is on the
curve (`ValidA (mulBase pt)`).
-/

namespace Cases.Zip2005.SpecMul
open RiscvZkvm.Rv64 Cases.Zip2005.Precompile.Pallas MachineChecked.RiscV.Wire

local notation "p" => Sp1.pallasP

/-- `-5` is not a cube modulo `p`: no Pallas point has `y = 0`. -/
theorem neg5_pow : Accel.powMod (p - 5) ((p - 1) / 3) p ≠ 1 := by decide +kernel

theorem onCurve_y_ne_zero {x : ℕ} (h : OnCurve x 0) : False := by
  rw [onCurve_iff] at h
  have hx3 : (x : F) ^ 3 = -5 := by
    have : (0 : F) = (x : F) ^ 3 + 5 := by simpa using h
    linear_combination -this
  have h5 : ((p - 5 : ℕ) : F) = -5 := by
    rw [Nat.cast_sub (by simp [Sp1.pallasP])]; simp
  have hx0 : (x : F) ≠ 0 := by
    intro h0; rw [h0] at hx3
    have : ((5 : ℕ) : F) = 0 := by simpa using hx3.symm
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    simp [Sp1.pallasP] at this
  have hferm := ZMod.pow_card_sub_one_eq_one hx0
  have hdiv : p - 1 = 3 * ((p - 1) / 3) := by
    have : (p - 1) % 3 = 0 := by decide +kernel
    omega
  rw [hdiv, pow_mul, hx3, ← h5, ← Cases.Zip2005.Precompile.cast_powMod (by decide +kernel)] at hferm
  apply neg5_pow
  have hlt : Accel.powMod (p - 5) ((p - 1) / 3) p < p := by
    rw [Cases.Zip2005.Precompile.powMod_eq (by decide +kernel)]; exact Nat.mod_lt _ (by decide)
  have := (ZMod.natCast_eq_natCast_iff' (Accel.powMod (p - 5) ((p - 1) / 3) p) 1 p).mp
    (by rw [hferm, Nat.cast_one])
  rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by decide)] at this

/-- The group element a tagged nine-word point denotes (tag `0`: the identity). -/
noncomputable def ptA (w : List Word) : C.Point :=
  if w[0]! = 0#64 then 0 else pointOf (xOf (w.drop 1)) (yOf (w.drop 1))

/-- A tagged point: nine words, and when the tag is set, reduced coordinates on the curve. -/
def ValidA (w : List Word) : Prop :=
  w.length = 9 ∧ (w[0]! ≠ 0#64 →
    Accel.ptValid p 4 (w.drop 1) = true ∧ OnCurve (xOf (w.drop 1)) (yOf (w.drop 1)))

theorem limbs_eq_of_val {a b : List Word} (hl : a.length = b.length)
    (h : Accel.leLimbsToNat a = Accel.leLimbsToNat b) : a = b := by
  rw [← Cases.Zip2005.Precompile.natToLeLimbs_leLimbsToNat a, ← Cases.Zip2005.Precompile.natToLeLimbs_leLimbsToNat b, h, hl]

/-- Two points on the curve with the same `x` and different `y` are inverse. -/
theorem add_eq_zero_of_x_eq {x y1 y2 : ℕ} (hy1 : y1 < p) (hy2 : y2 < p) (hy : y1 ≠ y2)
    (h1 : OnCurve x y1) (h2 : OnCurve x y2) : pointOf x y1 + pointOf x y2 = 0 := by
  rw [pointOf_of_onCurve h1, pointOf_of_onCurve h2]
  have hne : (y1 : F) ≠ y2 := cast_ne_of_ne hy1 hy2 hy
  rw [onCurve_iff] at h1 h2
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
  have hm : ((y1 : F) - y2) * (y1 + y2) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.mp hm with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · simp only [WeierstrassCurve.Affine.negY, C, W, zero_mul, sub_zero]
    linear_combination h

theorem ptA_cons {t : Word} {X : List Word} (ht : t ≠ 0#64) :
    ptA (t :: X) = pointOf (xOf X) (yOf X) := by
  unfold ptA; rw [List.getElem!_cons_zero, if_neg ht]; rfl

theorem ptA_zero (X : List Word) : ptA ((0 : Word) :: X) = 0 := by
  unfold ptA; rw [List.getElem!_cons_zero]; exact if_pos rfl

theorem ptA_of_tag {a : List Word} (h : a[0]! ≠ 0#64) :
    ptA a = pointOf (xOf (a.drop 1)) (yOf (a.drop 1)) := by
  unfold ptA; rw [if_neg h]

/-- **`completeAddW` is the group law** on tagged points. -/
theorem completeAddW_spec {a b : List Word} (ha : ValidA a) (hb : ValidA b) :
    ValidA (completeAddW a b) ∧ ptA (completeAddW a b) = ptA a + ptA b := by
  obtain ⟨hal, hav⟩ := ha
  obtain ⟨hbl, hbv⟩ := hb
  unfold completeAddW
  by_cases h0 : a[0]! = 0
  · rw [if_pos h0]
    exact ⟨⟨hbl, hbv⟩, by simp [ptA, h0]⟩
  rw [if_neg h0]
  by_cases h1 : b[0]! = 0
  · rw [if_pos h1]
    exact ⟨⟨hal, hav⟩, by simp [ptA, h1]⟩
  rw [if_neg h1]
  obtain ⟨hva, hca⟩ := hav h0
  obtain ⟨hvb, hcb⟩ := hbv h1
  have hal1 : (a.drop 1).length = 8 := by rw [List.length_drop, hal]
  have hbl1 : (b.drop 1).length = 8 := by rw [List.length_drop, hbl]
  split
  · rename_i heq
    have hy0 : yOf (a.drop 1) ≠ 0 := fun h => onCurve_y_ne_zero (h ▸ hca)
    obtain ⟨hl, hv, hc, hpt⟩ := curveDblL_spec (a.drop 1) hva hy0 hca
    refine ⟨⟨by rw [List.length_cons, hl], fun _ => ⟨hv, hc⟩⟩, ?_⟩
    rw [ptA_cons h0, ptA_of_tag h0, ptA_of_tag h1, hpt, ← heq, two_nsmul]
  split
  · rename_i hne hx
    refine ⟨⟨by rw [List.length_cons, hal1], fun h => absurd rfl h⟩, ?_⟩
    rw [ptA_zero, ptA_of_tag h0, ptA_of_tag h1]
    have hxe : xOf (a.drop 1) = xOf (b.drop 1) := by simp only [xOf, hx]
    rw [hxe]
    rw [ptValid_iff] at hva hvb
    refine (add_eq_zero_of_x_eq hva.2 hvb.2 ?_ (hxe ▸ hca) hcb).symm
    intro hy
    apply hne
    have hd : (a.drop 1).drop 4 = (b.drop 1).drop 4 :=
      limbs_eq_of_val (by simp [hal, hbl]) hy
    rw [← List.take_append_drop 4 (a.drop 1), ← List.take_append_drop 4 (b.drop 1), hx, hd]
  · rename_i hne hx
    have hxne : xOf (a.drop 1) ≠ xOf (b.drop 1) := fun h =>
      hx (limbs_eq_of_val (by simp [hal, hbl]) h)
    obtain ⟨hl, hv, hc, hpt⟩ := curveAddL_spec (a.drop 1) (b.drop 1) hva hvb hxne hca hcb
    refine ⟨⟨by rw [List.length_cons, hl], fun _ => ⟨hv, hc⟩⟩, ?_⟩
    rw [ptA_cons h0, ptA_of_tag h0, ptA_of_tag h1, hpt]


/-- `doubleW` is doubling on tagged points. -/
theorem doubleW_spec {a : List Word} (ha : ValidA a) :
    ValidA (doubleW a) ∧ ptA (doubleW a) = 2 • ptA a := by
  obtain ⟨hal, hav⟩ := ha
  unfold doubleW
  by_cases h0 : a[0]! = 0
  · rw [if_pos h0]
    refine ⟨⟨hal, hav⟩, ?_⟩
    have : ptA a = 0 := by unfold ptA; exact if_pos h0
    rw [this, nsmul_zero]
  rw [if_neg h0]
  obtain ⟨hva, hca⟩ := hav h0
  have hy0 : yOf (a.drop 1) ≠ 0 := fun h => onCurve_y_ne_zero (h ▸ hca)
  obtain ⟨hl, hv, hc, hpt⟩ := curveDblL_spec (a.drop 1) hva hy0 hca
  refine ⟨⟨by rw [List.length_cons, hl], fun _ => ⟨hv, hc⟩⟩, ?_⟩
  rw [ptA_cons h0, ptA_of_tag h0, hpt]

/-- The scalar the bits `i, …, i + n - 1` spell, least significant first. -/
def bitsVal (bits : ℕ → Bool) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if bits i then 1 else 0) + 2 * bitsVal bits (i + 1) n

theorem ptA_retag {t : Word} {a : List Word} (ht : t ≠ 0#64) (ha : a[0]! ≠ 0#64) :
    ptA (t :: a.drop 1) = ptA a := by
  rw [ptA_cons ht, ptA_of_tag ha]

/-- The loop: `acc + [bitsVal] base`, `base` doubled `n` times, every accumulator tagged. -/
theorem mulLoop_spec (bits : ℕ → Bool) :
    ∀ n i (acc base : List Word), ValidA acc → acc[0]! ≠ 0#64 → ValidA base →
      mulOk bits i n acc base →
      ValidA (mulLoop bits i n acc base).1 ∧ (mulLoop bits i n acc base).1[0]! ≠ 0#64 ∧
      ValidA (mulLoop bits i n acc base).2 ∧
      ptA (mulLoop bits i n acc base).1 = ptA acc + bitsVal bits i n • ptA base ∧
      ptA (mulLoop bits i n acc base).2 = (2 ^ n) • ptA base
  | 0, i, acc, base, ha, ht, hb, _ => by
    refine ⟨ha, ht, hb, ?_, ?_⟩
    · simp only [mulLoop, bitsVal, zero_nsmul, add_zero]
    · simp only [mulLoop, pow_zero, one_nsmul]
  | n + 1, i, acc, base, ha, ht, hb, hok => by
    obtain ⟨hok0, hokr⟩ := hok
    obtain ⟨hcv, hcp⟩ := completeAddW_spec ha hb
    obtain ⟨hdv, hdp⟩ := doubleW_spec hb
    have h1 : (1#64 : Word) ≠ 0#64 := by decide
    -- the next accumulator
    have hacc : ValidA (mulStep (bits i) acc base).1 ∧ (mulStep (bits i) acc base).1[0]! ≠ 0#64 ∧
        ptA (mulStep (bits i) acc base).1 = ptA acc + (if bits i then 1 else 0) • ptA base := by
      unfold mulStep
      cases hbi : bits i
      · simp only [Bool.false_eq_true, if_false, zero_nsmul, add_zero]
        refine ⟨⟨?_, fun _ => ?_⟩, by rw [List.getElem!_cons_zero]; exact h1, ptA_retag h1 ht⟩
        · rw [List.length_cons, List.length_drop, ha.1]
        · have := ha.2 ht; simpa using this
      · simp only [if_true, one_nsmul]
        refine ⟨⟨?_, fun _ => ?_⟩, by rw [List.getElem!_cons_zero]; exact h1, ?_⟩
        · rw [List.length_cons, List.length_drop, hcv.1]
        · have := hcv.2 hok0; simpa using this
        · rw [ptA_retag h1 hok0, hcp]
    obtain ⟨hav', hat', hap'⟩ := hacc
    have hbase : (mulStep (bits i) acc base).2 = doubleW base := rfl
    obtain ⟨r1, r2, r3, r4, r5⟩ := mulLoop_spec bits n (i + 1) _ _ hav' hat' (hbase ▸ hdv) hokr
    refine ⟨r1, r2, r3, ?_, ?_⟩
    · rw [show mulLoop bits i (n + 1) acc base =
          mulLoop bits (i + 1) n (mulStep (bits i) acc base).1 (mulStep (bits i) acc base).2 from rfl,
        r4, hap', hbase, hdp, bitsVal, smul_smul, add_assoc, ← add_smul]
      congr 2
      ring
    · rw [show mulLoop bits i (n + 1) acc base =
          mulLoop bits (i + 1) n (mulStep (bits i) acc base).1 (mulStep (bits i) acc base).2 from rfl,
        r5, hbase, hdp, smul_smul, pow_succ]


theorem natToLeLimbs_getElem! {n x j : ℕ} (h : j < n) :
    (Accel.natToLeLimbs n x)[j]! = BitVec.ofNat 64 (x >>> (64 * j)) := by
  simp [Accel.natToLeLimbs, h]

/-- The loop's bit `i` of a scalar's limbs is the scalar's bit `i`. -/
theorem scalarBit_natToLeLimbs (s i : ℕ) (hi : i < 256) :
    scalarBit (Accel.natToLeLimbs 4 s) i = s.testBit i := by
  unfold scalarBit
  rw [natToLeLimbs_getElem! (by omega)]
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftRight]
  have h1 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have h2 : i / 8 % 8 * 8 + i % 8 < 64 := by omega
  simp only [h1, h2, decide_true, Bool.true_and]
  congr 1
  omega

theorem bitsVal_testBit (n : ℕ) : ∀ m i, bitsVal (fun j => n.testBit j) i m = (n >>> i) % 2 ^ m
  | 0, i => by simp [bitsVal, Nat.mod_one]
  | m + 1, i => by
    rw [bitsVal, bitsVal_testBit n m (i + 1), pow_succ', Nat.mod_mul]
    have e : n >>> (i + 1) = (n >>> i) / 2 := by
      rw [Nat.shiftRight_succ]
    rw [e, Nat.testBit_eq_decide_div_mod_eq]
    have : n / 2 ^ i = n >>> i := (Nat.shiftRight_eq_div_pow n i).symm
    rw [this]
    rcases Nat.mod_two_eq_zero_or_one (n >>> i) with h | h <;> simp [h]

/-- The 255 bits the loop reads spell the canonical scalar. -/
theorem bitsVal_scalar (s : ℕ) (hs : s < 2 ^ 255) :
    bitsVal (scalarBit (Accel.natToLeLimbs 4 s)) 0 255 = s := by
  have key : ∀ m i, i + m ≤ 256 →
      bitsVal (scalarBit (Accel.natToLeLimbs 4 s)) i m = bitsVal (fun j => s.testBit j) i m := by
    intro m
    induction m with
    | zero => intro i _; rfl
    | succ m ih =>
      intro i hm
      rw [bitsVal, bitsVal, ih (i + 1) (by omega), scalarBit_natToLeLimbs s i (by omega)]
  rw [key 255 0 (by decide), bitsVal_testBit, Nat.shiftRight_zero, Nat.mod_eq_of_lt hs]


theorem Qw_valid : ValidA Qw := by
  refine ⟨rfl, fun _ => ⟨by decide +kernel, ?_⟩⟩
  rw [onCurve_iff_nat]; decide +kernel

theorem negQw_valid : ValidA negQw := by
  refine ⟨rfl, fun _ => ⟨by decide +kernel, ?_⟩⟩
  rw [onCurve_iff_nat]; decide +kernel

theorem Qw_tag : Qw[0]! ≠ 0#64 := by decide +kernel
theorem negQw_tag : negQw[0]! ≠ 0#64 := by decide +kernel

theorem pointOf_neg {x y y' : ℕ} (h : OnCurve x y) (h' : OnCurve x y') (hy : (y' : F) = -(y : F)) :
    pointOf x y' = -pointOf x y := by
  rw [pointOf_of_onCurve h, pointOf_of_onCurve h', WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.negY, C, W, zero_mul, sub_zero]
  congr

theorem ptA_negQw : ptA negQw = -ptA Qw := by
  rw [ptA_of_tag negQw_tag, ptA_of_tag Qw_tag]
  have hq := (Qw_valid.2 Qw_tag).2
  have hn := (negQw_valid.2 negQw_tag).2
  have hx : xOf (negQw.drop 1) = xOf (Qw.drop 1) := by decide +kernel
  have hy : (yOf (negQw.drop 1) : F) = -(yOf (Qw.drop 1) : F) := by
    have e : yOf (negQw.drop 1) = Sp1.pallasP - yOf (Qw.drop 1) := by decide +kernel
    rw [e, Nat.cast_sub (by decide +kernel)]; simp
  rw [hx] at hn ⊢
  exact pointOf_neg hq hn hy

/-- **The scalar multiplication's sum**: `Q + [k] base - Q` is `[k] base`, the scalar canonical. -/
theorem mulSum_spec (pt k : List Word) (hb : ValidA (mulBase pt))
    (hok : mulOk (scalarBit (mulScalar k)) 0 255 Qw (mulBase pt)) :
    ValidA (mulSum pt k) ∧
      ptA (mulSum pt k) = (Accel.leLimbsToNat k * Fq.rInv % Fq.q) • ptA (mulBase pt) := by
  obtain ⟨r1, -, -, r4, -⟩ := mulLoop_spec _ 255 0 Qw (mulBase pt) Qw_valid Qw_tag hb hok
  obtain ⟨c1, c2⟩ := completeAddW_spec r1 negQw_valid
  refine ⟨c1, ?_⟩
  unfold mulSum
  rw [c2, r4, ptA_negQw, mulScalar, bitsVal_scalar]
  · abel
  · exact lt_trans (Nat.mod_lt _ Fq.q_pos) (by decide +kernel)


/-- The affine coordinates, out of Montgomery form, of a twelve-word Jacobian point. -/
def jacXY (m : List Word) : ℕ × ℕ :=
  ((Fp.toAffine (ptX m) (ptY m) (ptZ m)).1 * Fp.rInv % Fp.p,
    (Fp.toAffine (ptX m) (ptY m) (ptZ m)).2 * Fp.rInv % Fp.p)

/-- The group element a twelve-word Jacobian point (Montgomery form) denotes. The identity's
encodings (`Z = 0`, or a `Z` with no inverse) give `(0, 0)`, which `pointOf` reads as `0`. -/
noncomputable def jacPt (m : List Word) : C.Point := pointOf (jacXY m).1 (jacXY m).2

theorem pointOf_zero : pointOf 0 0 = 0 := by
  have h : ¬OnCurve 0 0 := by rw [onCurve_iff_nat]; decide +kernel
  simp [pointOf, h]

theorem toAffine_Z_zero (X Y : ℕ) : Fp.toAffine X Y 0 = (0, 0) := by
  have hR : (0 : ℕ) ≠ Fp.R := by decide +kernel
  simp [Fp.toAffine, hR]

theorem jacPt_of_Z {m : List Word} (hz : ptZ m = 0) : jacPt m = 0 := by
  unfold jacPt jacXY; rw [hz, toAffine_Z_zero]; exact pointOf_zero

theorem ptZ_replicate : ptZ (List.replicate 12 (0#64 : Word)) = 0 := by decide +kernel

theorem cells3 (X Y Z : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) (hZ : Z < 2 ^ 256) :
    ptX (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z) = X ∧
    ptY (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z) = Y ∧
    ptZ (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z) = Z := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ptX
    rw [show [(Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[0]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[1]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[2]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[3]!] =
        Accel.natToLeLimbs 4 X from rfl]
    exact Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hX
  · unfold ptY
    rw [show [(Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[4]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[5]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[6]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[7]!] =
        Accel.natToLeLimbs 4 Y from rfl]
    exact Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hY
  · unfold ptZ
    rw [show [(Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[8]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[9]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[10]!,
        (Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++ Accel.natToLeLimbs 4 Z)[11]!] =
        Accel.natToLeLimbs 4 Z from rfl]
    exact Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hZ

/-- Into Montgomery form by `R²` and back out by `R⁻¹`. -/
theorem mont_in_out (a : ℕ) (ha : a < Fp.p) : Fp.mul a Fp.R2 * Fp.rInv % Fp.p = a := by
  have hp : (Fp.p : ℕ) = Sp1.pallasP := rfl
  have key : ((Fp.mul a Fp.R2 * Fp.rInv % Fp.p : ℕ) : F) = (a : F) := by
    have h1 : Fp.rInv * 2 ^ 256 % Sp1.pallasP = 1 := Fp.rInv_spec
    have hr : ((Fp.rInv : ℕ) : F) * ((2 ^ 256 : ℕ) : F) = 1 := by
      rw [← Nat.cast_mul, ← ZMod.natCast_mod, h1, Nat.cast_one]
    have hR : ((Fp.R : ℕ) : F) = ((2 ^ 256 : ℕ) : F) := by
      rw [Fp.R_spec, hp, ZMod.natCast_mod]
    have hR2 : ((Fp.R2 : ℕ) : F) = (Fp.R : F) * (Fp.R : F) := by
      rw [Fp.R2_spec, hp, ZMod.natCast_mod, Nat.cast_mul]
    simp only [Fp.mul, hp, ZMod.natCast_mod, Nat.cast_mul, hR2, hR]
    linear_combination (a : F) * ((2 ^ 256 : ℕ) : F) * (Fp.rInv : F) * hr + (a : F) * hr
  have hlt : Fp.mul a Fp.R2 * Fp.rInv % Fp.p < Sp1.pallasP := Nat.mod_lt _ Fp.p_pos
  have ha' : a < Sp1.pallasP := ha
  rw [← ZMod.val_cast_of_lt hlt, key, ZMod.val_cast_of_lt ha']

theorem drop1_take4 {S : List Word} (h : S.length = 9) :
    (S.drop 1).take 4 = [S[1]!, S[2]!, S[3]!, S[4]!] ∧
      (S.drop 1).drop 4 = [S[5]!, S[6]!, S[7]!, S[8]!] := by
  match S, h with
  | [_, _, _, _, _, _, _, _, _], _ => exact ⟨rfl, rfl⟩

theorem ptA_mulBase (pt : List Word) : ptA (mulBase pt) = jacPt pt := by
  unfold mulBase jacPt jacXY
  rw [ptA_cons (by decide)]
  obtain ⟨-, hx, hy⟩ := encode_decode (a := (Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).1 * Fp.rInv % Fp.p)
    (b := (Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).2 * Fp.rInv % Fp.p)
    (Nat.mod_lt _ Fp.p_pos) (Nat.mod_lt _ Fp.p_pos)
  rw [hx, hy]

/-- **`Ep::mul`'s model is scalar multiplication** of the group element the input denotes, by the
scalar out of Montgomery form. -/
theorem mulW_spec (pt k : List Word) (hb : ptZ pt ≠ 0 → ValidA (mulBase pt)) (hf : mulFacts pt k) :
    jacPt (mulW pt k) = (Accel.leLimbsToNat k * Fq.rInv % Fq.q) • jacPt pt := by
  by_cases hz : ptZ pt = 0
  · rw [mulW, if_pos hz, jacPt_of_Z ptZ_replicate, jacPt_of_Z hz, nsmul_zero]
  obtain ⟨hok, hcan⟩ := hf hz
  obtain ⟨hSv, hSp⟩ := mulSum_spec pt k (hb hz) hok
  rw [ptA_mulBase] at hSp
  rw [mulW, if_neg hz]
  by_cases h0 : (mulSum pt k)[0]! = 0
  · rw [if_pos h0, jacPt_of_Z ptZ_replicate, ← hSp]
    unfold ptA; rw [if_pos (show (mulSum pt k)[0]! = 0#64 from h0)]
  rw [if_neg h0]
  obtain ⟨hxl, hyl⟩ := hcan h0
  obtain ⟨ht, hd⟩ := drop1_take4 hSv.1
  have hxs := Fp.mul_lt (Accel.leLimbsToNat [(mulSum pt k)[1]!, (mulSum pt k)[2]!,
    (mulSum pt k)[3]!, (mulSum pt k)[4]!]) Fp.R2
  have hys := Fp.mul_lt (Accel.leLimbsToNat [(mulSum pt k)[5]!, (mulSum pt k)[6]!,
    (mulSum pt k)[7]!, (mulSum pt k)[8]!]) Fp.R2
  obtain ⟨cx, cy, cz⟩ := cells3 _ _ _ (lt_trans hxs Fp.p_lt) (lt_trans hys Fp.p_lt)
    (lt_trans Fp.R_lt Fp.p_lt)
  rw [← hSp, ptA_of_tag h0]
  unfold jacPt jacXY
  rw [cx, cy, cz, Fp.toAffine, if_pos rfl]
  simp only
  rw [mont_in_out _ hxl, mont_in_out _ hyl, xOf, yOf, ht, hd]

end Cases.Zip2005.SpecMul
