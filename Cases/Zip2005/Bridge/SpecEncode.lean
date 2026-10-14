import Cases.Zip2005.Bridge.SpecKeys
import Cases.Zip2005.Precompile

/-!
# Point encodings

`repr_ℙ` (the spec's compressed encoding `x + 2^255 ỹ`) is injective on valid points
(`reprPNat_inj`: no curve point has `x = 0` because `5` is not a square mod `p`, `no_sqrt5`; `ỹ`
fixes the sign of `y` because `p` is odd). `Ep::to_bytes`'s number is `repr_ℙ` of the spec point
(`tbX_repr`), and `EpAffine::from_bytes` with flag `1` decodes its bytes to a valid point with that
encoding (`fb_decode`), so a decoded point is the input's unique valid preimage.
-/

namespace Cases.Zip2005.SpecMul

open RiscvZkvm.Rv64 Cases.Zip2005.Precompile.Pallas
open Zcash.Circuits (Fp Fq Point)

set_option autoImplicit false

local notation "p" => Sp1.pallasP

theorem five_pow : Accel.powMod 5 ((p - 1) / 2) p ≠ 1 := by decide +kernel

/-- `5` is not a square mod `p`: no point of the curve has `x = 0`. -/
theorem no_sqrt5 {y : F} (h : y ^ 2 = 5) : False := by
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0] at h
    have : ((5 : ℕ) : F) = 0 := by simpa using h.symm
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    simp [Sp1.pallasP] at this
  have hferm := ZMod.pow_card_sub_one_eq_one hy0
  have hdiv : p - 1 = 2 * ((p - 1) / 2) := by
    have : (p - 1) % 2 = 0 := by decide +kernel
    omega
  rw [hdiv, pow_mul, h, show (5 : F) = ((5 : ℕ) : F) by norm_num,
    ← Cases.Zip2005.Precompile.cast_powMod (by decide +kernel)] at hferm
  apply five_pow
  have hlt : Accel.powMod 5 ((p - 1) / 2) p < p := by
    rw [Cases.Zip2005.Precompile.powMod_eq (by decide +kernel)]; exact Nat.mod_lt _ (by decide)
  have := (ZMod.natCast_eq_natCast_iff' (Accel.powMod 5 ((p - 1) / 2) p) 1 p).mp
    (by rw [hferm, Nat.cast_one])
  rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by decide)] at this

theorem onCurve_x_ne_zero {P : Point Fp} (h : P.OnCurve) : P.x ≠ 0 := by
  intro hx
  have h' : P.y ^ 2 = P.x ^ 3 + Zcash.Circuits.pallasB := h
  rw [hx] at h'
  have h2 : P.y ^ 2 = 5 := by rw [h']; norm_num [Zcash.Circuits.pallasB]
  exact no_sqrt5 (y := (P.y : F)) h2

theorem onCurve_y_ne_zero' {P : Point Fp} (h : P.OnCurve) : P.y ≠ 0 :=
  Cases.Zip2005.Poseidon.y_ne_zero_of_onCurve (x := P.x) (by have h' : P.y ^ 2 = P.x ^ 3 + Zcash.Circuits.pallasB := h; rw [h']; rfl)

theorem p_odd : Fp.p % 2 = 1 := by decide +kernel

/-- **`repr_ℙ` is injective on valid points** (`x` below `2^255`, `ỹ` one bit; on the curve `x`
fixes `y` up to sign, `ỹ` the sign since `p` is odd; no curve point has `x = 0`, so the identity's
encoding is its own). -/
theorem reprPNat_inj {P Q : Point Fp} (hP : P.Valid) (hQ : Q.Valid)
    (h : Zip2005.reprPNat P = Zip2005.reprPNat Q) : P = Q := by
  unfold Zip2005.reprPNat Zip2005.ytilde at h
  have hxP := Cases.Zip2005.Poseidon.val_lt_255 P.x
  have hxQ := Cases.Zip2005.Poseidon.val_lt_255 Q.x
  have htP : P.y.val % 2 < 2 := Nat.mod_lt _ (by decide)
  have htQ : Q.y.val % 2 < 2 := Nat.mod_lt _ (by decide)
  have hx : P.x.val = Q.x.val := by omega
  have ht : P.y.val % 2 = Q.y.val % 2 := by omega
  have hx' : P.x = Q.x := ZMod.val_injective _ hx
  rcases hP with hP | hP0 <;> rcases hQ with hQ | hQ0
  · have eP : P.y ^ 2 = P.x ^ 3 + Zcash.Circuits.pallasB := hP
    have eQ : Q.y ^ 2 = Q.x ^ 3 + Zcash.Circuits.pallasB := hQ
    have hy2 : P.y ^ 2 = Q.y ^ 2 := by rw [eP, eQ, hx']
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2 with hy | hy
    · cases P; cases Q; simp only at hx' hy; rw [hx', hy]
    · exfalso
      have hQy := onCurve_y_ne_zero' hQ
      rw [hy, ZMod.neg_val, if_neg hQy] at ht
      have hlt : Q.y.val < Fp.p := ZMod.val_lt Q.y
      have hpos : 0 < Q.y.val := by
        rcases Nat.eq_zero_or_pos Q.y.val with h0 | h0
        · exact absurd ((ZMod.val_eq_zero _).mp h0) hQy
        · exact h0
      have hp := p_odd
      have e : (CompElliptic.Fields.Pasta.PALLAS_BASE_CARD - Q.y.val) % 2 = (Fp.p - Q.y.val) % 2 := rfl
      rw [e] at ht
      omega
  · exfalso; rw [hQ0] at hx'; exact onCurve_x_ne_zero hP hx'
  · exfalso; rw [hP0] at hx'; exact onCurve_x_ne_zero hQ hx'.symm
  · rw [hP0, hQ0]

/-- `Ep::to_bytes`'s number (`tbX`) is `repr_ℙ` of the spec point. -/
theorem tbX_repr (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 : Word) :
    Cases.Zip2005.tbX l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 =
      Zip2005.reprPNat (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]) := by
  have ex : Cases.Zip2005.ptX [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11] = Accel.leLimbsToNat [l0, l1, l2, l3] := rfl
  have ey : Cases.Zip2005.ptY [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11] = Accel.leLimbsToNat [l4, l5, l6, l7] := rfl
  have ez : Cases.Zip2005.ptZ [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11] = Accel.leLimbsToNat [l8, l9, l10, l11] := rfl
  unfold Cases.Zip2005.tbX Zip2005.reprPNat Zip2005.ytilde specPt jacXY
  rw [ex, ey, ez]
  simp only
  generalize (Fp.toAffine (Accel.leLimbsToNat [l0, l1, l2, l3]) (Accel.leLimbsToNat [l4, l5, l6, l7])
    (Accel.leLimbsToNat [l8, l9, l10, l11])) = T
  have hA : T.1 * Fp.rInv % Fp.p < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := Nat.mod_lt _ Fp.p_pos
  have hB : T.2 * Fp.rInv % Fp.p < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := Nat.mod_lt _ Fp.p_pos
  rw [ZMod.val_cast_of_lt hA, ZMod.val_cast_of_lt hB]
  ring

/-- The 32 bytes' number: the low 255 bits and the sign bit `b3`'s top bit. -/
theorem bytes_split (b0 b1 b2 b3 : Word) :
    Accel.leLimbsToNat [b0, b1, b2, b3] =
      Accel.leLimbsToNat [b0, b1, b2, b3 &&& 0x7fffffffffffffff#64] + (if b3.msb then 1 else 0) * 2 ^ 255 := by
  simp only [Cases.Zip2005.Precompile.leLimbsToNat_cons, Cases.Zip2005.Precompile.leLimbsToNat_nil, BitVec.toNat_and]
  rw [show (0x7fffffffffffffff#64 : Word).toNat = 2 ^ 63 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.msb_eq_decide]
  have := b3.isLt
  split_ifs with h <;> simp at h <;> omega

/-- **`from_bytes` with flag `1` decodes the bytes**: the twelve words are a valid spec point (the
guest's point invariant `JacW`), and its `repr_ℙ` is the 32 bytes' number. -/
theorem fb_decode (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 b0 b1 b2 b3 : Word)
    (h : Cases.Zip2005.FromBytesPost b0 b1 b2 b3 (Accel.leLimbsToNat [x0, x1, x2, x3])
      (Accel.leLimbsToNat [y0, y1, y2, y3]) 1#8)
    (hz : Accel.leLimbsToNat [z0, z1, z2, z3] =
      if Accel.leLimbsToNat [x0, x1, x2, x3] = 0 ∧ Accel.leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) :
    Cases.Zip2005.Poseidon.JacW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] ∧
      (specPt [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]).Valid ∧
      Zip2005.reprPNat (specPt [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]) =
        Accel.leLimbsToNat [b0, b1, b2, b3] := by
  have ex : Cases.Zip2005.ptX [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] = Accel.leLimbsToNat [x0, x1, x2, x3] := rfl
  have ey : Cases.Zip2005.ptY [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] = Accel.leLimbsToNat [y0, y1, y2, y3] := rfl
  have ez : Cases.Zip2005.ptZ [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] = Accel.leLimbsToNat [z0, z1, z2, z3] := rfl
  have hsp : specPt [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] =
      ⟨(((Fp.toAffine (Accel.leLimbsToNat [x0, x1, x2, x3]) (Accel.leLimbsToNat [y0, y1, y2, y3])
        (Accel.leLimbsToNat [z0, z1, z2, z3])).1 * Fp.rInv % Fp.p : ℕ) : Fp),
       (((Fp.toAffine (Accel.leLimbsToNat [x0, x1, x2, x3]) (Accel.leLimbsToNat [y0, y1, y2, y3])
        (Accel.leLimbsToNat [z0, z1, z2, z3])).2 * Fp.rInv % Fp.p : ℕ) : Fp)⟩ := by
    unfold specPt jacXY; rw [ex, ey, ez]
  have hbs := bytes_split b0 b1 b2 b3
  generalize Accel.leLimbsToNat [x0, x1, x2, x3] = x at h hz hsp ex
  generalize Accel.leLimbsToNat [y0, y1, y2, y3] = y at h hz hsp ey
  generalize Accel.leLimbsToNat [z0, z1, z2, z3] = z at hz hsp ez
  unfold Cases.Zip2005.FromBytesPost at h
  set X := Accel.leLimbsToNat [b0, b1, b2, b3 &&& 0x7fffffffffffffff#64] with hXd
  obtain ⟨hxp, hyp, hcase⟩ := h
  rcases hcase with ⟨-, hX, hc⟩ | ⟨hf, -⟩
  swap
  · exact absurd hf (by decide)
  rcases hc with ⟨hX0, hsign, hx0, hy0⟩ | ⟨hxm, hyy, hpar⟩
  · -- the identity's encoding
    subst hx0 hy0
    rw [if_pos ⟨rfl, rfl⟩] at hz
    subst hz
    rw [toAffine_Z_zero] at hsp
    simp only [Nat.zero_mul, Nat.zero_mod, Nat.cast_zero] at hsp
    refine ⟨Or.inl ez, ?_, ?_⟩
    · rw [hsp]; exact Or.inr rfl
    · rw [hsp, hbs, hX0, hsign]
      simp [Zip2005.reprPNat, Zip2005.ytilde]
  · -- a point on the curve
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hyy
      have := congrArg Cases.Zip2005.Poseidon.D hyy
      rw [Cases.Zip2005.Fp.rhs, Cases.Zip2005.Poseidon.D_add, Cases.Zip2005.Poseidon.D_mont 5 (by decide)] at this
      simp only [Cases.Zip2005.Poseidon.D_mul, Cases.Zip2005.Poseidon.D_zero] at this
      exact Cases.Zip2005.Poseidon.y_ne_zero_of_onCurve (x := Cases.Zip2005.Poseidon.D x) (y := 0)
        (by linear_combination this) rfl
    rw [if_neg (fun h => hy0 h.2)] at hz
    subst hz
    rw [toAffine_R] at hsp
    simp only at hsp
    rw [hxm, mont_in_out _ hX] at hsp
    have hon : (specPt [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]).OnCurve := by
      rw [hsp]
      show _ ^ 2 = _ ^ 3 + Zcash.Circuits.pallasB
      have := congrArg Cases.Zip2005.Poseidon.D hyy
      rw [Cases.Zip2005.Fp.rhs, Cases.Zip2005.Poseidon.D_add, Cases.Zip2005.Poseidon.D_mont 5 (by decide), hxm] at this
      simp only [Cases.Zip2005.Poseidon.D_mul, Cases.Zip2005.Poseidon.D_mont _ hX] at this
      rw [Cases.Zip2005.Poseidon.castD]
      simp only [Zcash.Circuits.pallasB]
      linear_combination this
    refine ⟨Or.inr ⟨ez, hon⟩, Or.inl hon, ?_⟩
    rw [hsp]
    unfold Zip2005.reprPNat Zip2005.ytilde
    simp only
    rw [ZMod.val_cast_of_lt (show X < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD from hX),
      ZMod.val_cast_of_lt (show y * Fp.rInv % Fp.p < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD from
        Nat.mod_lt _ Fp.p_pos)]
    have hp := hpar hy0
    unfold Cases.Zip2005.Fp.fromMont at hp
    rw [hp, hbs]

end Cases.Zip2005.SpecMul
