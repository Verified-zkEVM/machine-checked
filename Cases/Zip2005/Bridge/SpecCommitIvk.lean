import Cases.Zip2005.Bridge.SpecJacPt
import Cases.Zip2005.Bridge.SpecConst
import Cases.Zip2005.Bridge.SpecChunks
import Cases.Zip2005.Sinsemilla.SinsemillaCommitIvk
import Cases.Zip2005.Field.Cells4
import Cases.Zip2005.Precompile

/-!
# `commit_ivk` is the spec's `Commit^ivk`

`JacW`: a twelve-word point as the guest's point code leaves it (the identity's `Z = 0`, or
`Z = R` on the curve); `Ep::mul`'s output (`jacW_mulW`) and a Sinsemilla hash point lifted to the
curve (`jacW_toCurve`) are such points, and the Jacobian sum of two of them reads as the spec's
sum (`specPt_addJ_cells`). `ivk_spec`: for canonical `ak`, `nk` and a defined hash (flag `1`), the
spec's `Commit^ivk_rivk(ak, nk)` is the affine `x` of the guest's commitment, with `rivk` the
scalar out of Montgomery form.
-/

namespace Cases.Zip2005.Poseidon

open RiscvZkvm.Rv64 Cases.Zip2005.SpecMul Cases.Zip2005.Precompile.Pallas
open Zcash.Circuits (Point)

set_option autoImplicit false

/-- A twelve-word point as the guest's point code leaves it: the identity's encoding (`Z = 0`), or
`Z = R` and on the curve. -/
def JacW (m : List Word) : Prop := ptZ m = 0 ∨ (ptZ m = Fp.R ∧ (specPt m).OnCurve)

theorem jacOk_of_jacW {m : List Word} (h : JacW m) : JacOk (ptX m) (ptY m) (ptZ m) := by
  rcases h with h | ⟨h, hon⟩
  · exact ⟨by rw [h]; exact Fp.p_pos, fun hz => absurd (by rw [h]; exact D_zero) hz⟩
  · refine ⟨by rw [h]; exact Fp.R_lt, fun _ => ?_⟩
    rw [specPt_eq m (by rw [h]; exact Fp.R_lt)] at hon
    unfold specT affD at hon
    rw [h, D_R, if_neg one_ne_zero] at hon
    rw [h, D_R]
    exact hon

theorem ptZ_lt_of_jacW {m : List Word} (h : JacW m) : ptZ m < Fp.p := (jacOk_of_jacW h).1

/-- `Ep::mul`'s output (`mulW`), from the run's facts. -/
theorem jacW_mulW (pt k : List Word) (hb : ptZ pt ≠ 0 → ValidA (mulBase pt)) (hf : mulFacts pt k) :
    JacW (mulW pt k) := by
  by_cases hz : ptZ pt = 0
  · left; rw [mulW, if_pos hz]; exact ptZ_replicate
  obtain ⟨hok, hcan⟩ := hf hz
  obtain ⟨hSv, -⟩ := mulSum_spec pt k (hb hz) hok
  by_cases h0 : (mulSum pt k)[0]! = 0
  · left; rw [mulW, if_neg hz, if_pos h0]; exact ptZ_replicate
  right
  obtain ⟨hxl, hyl⟩ := hcan h0
  obtain ⟨ht, hd⟩ := drop1_take4 hSv.1
  have hxs := Fp.mul_lt (Accel.leLimbsToNat [(mulSum pt k)[1]!, (mulSum pt k)[2]!,
    (mulSum pt k)[3]!, (mulSum pt k)[4]!]) Fp.R2
  have hys := Fp.mul_lt (Accel.leLimbsToNat [(mulSum pt k)[5]!, (mulSum pt k)[6]!,
    (mulSum pt k)[7]!, (mulSum pt k)[8]!]) Fp.R2
  obtain ⟨cx, cy, cz⟩ := cells3 _ _ _ (lt_trans hxs Fp.p_lt) (lt_trans hys Fp.p_lt)
    (lt_trans Fp.R_lt Fp.p_lt)
  have hc := (hSv.2 h0).2
  rw [mulW, if_neg hz, if_neg h0]
  refine ⟨cz, ?_⟩
  rw [Point.onCurve_iff]
  apply (onCurve_iff_sw _ _).mp
  unfold jacXY
  rw [cx, cy, cz, Fp.toAffine, if_pos rfl]
  simp only
  rw [mont_in_out _ hxl, mont_in_out _ hyl]
  rw [xOf, yOf, ht, hd] at hc
  exact hc

theorem list8_x (L : List Word) (h : L.length = 8) :
    Accel.leLimbsToNat [L[0]!, L[1]!, L[2]!, L[3]!] = xOf L ∧
      Accel.leLimbsToNat [L[4]!, L[5]!, L[6]!, L[7]!] = yOf L := by
  match L, h with
  | [_, _, _, _, _, _, _, _], _ => exact ⟨rfl, rfl⟩

/-- The hash point lifted back to the curve (`unpack`, `to_curve`) from an accumulator on the curve. -/
theorem jacW_toCurve (L : List Word) (hL : AffOk L) :
    JacW (toCurveW (unpackW L)) ∧ specPt (toCurveW (unpackW L)) = dec8 L := by
  obtain ⟨hl, hv, hon⟩ := hL
  obtain ⟨hx, hy⟩ := (ptValid_iff L).mp hv
  obtain ⟨ex, ey⟩ := list8_x L hl
  have hxs := Fp.mul_lt (xOf L) Fp.R2
  have hys := Fp.mul_lt (yOf L) Fp.R2
  have hu : unpackW L = Accel.natToLeLimbs 4 (Fp.mul (xOf L) Fp.R2) ++
      Accel.natToLeLimbs 4 (Fp.mul (yOf L) Fp.R2) := by
    rw [unpackW, ex, ey]
  set X := Fp.mul (xOf L) Fp.R2 with hX
  set Y := Fp.mul (yOf L) Fp.R2 with hY
  have hu' : unpackW L = [BitVec.ofNat 64 (X >>> (64 * 0)), BitVec.ofNat 64 (X >>> (64 * 1)),
      BitVec.ofNat 64 (X >>> (64 * 2)), BitVec.ofNat 64 (X >>> (64 * 3)),
      BitVec.ofNat 64 (Y >>> (64 * 0)), BitVec.ofNat 64 (Y >>> (64 * 1)),
      BitVec.ofNat 64 (Y >>> (64 * 2)), BitVec.ofNat 64 (Y >>> (64 * 3))] := by
    rw [hu]; rfl
  have hl4 : ∀ V : ℕ, V < 2 ^ 256 → BitVec.ofNat 64 (V >>> (64 * 0)) = 0#64 →
      BitVec.ofNat 64 (V >>> (64 * 1)) = 0#64 → BitVec.ofNat 64 (V >>> (64 * 2)) = 0#64 →
      BitVec.ofNat 64 (V >>> (64 * 3)) = 0#64 → V = 0 := by
    intro V hV h0 h1 h2 h3
    rw [← Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hV]
    show Accel.leLimbsToNat [BitVec.ofNat 64 (V >>> (64 * 0)), BitVec.ofNat 64 (V >>> (64 * 1)),
      BitVec.ofNat 64 (V >>> (64 * 2)), BitVec.ofNat 64 (V >>> (64 * 3))] = 0
    rw [h0, h1, h2, h3]; rfl
  have hnz : ¬ ((unpackW L)[0]! = 0#64 ∧ (unpackW L)[1]! = 0#64 ∧ (unpackW L)[2]! = 0#64 ∧
      (unpackW L)[3]! = 0#64 ∧ (unpackW L)[4]! = 0#64 ∧ (unpackW L)[5]! = 0#64 ∧
      (unpackW L)[6]! = 0#64 ∧ (unpackW L)[7]! = 0#64) := by
    rw [hu']
    rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7
    have hX0 := hl4 X (lt_trans hxs Fp.p_lt) h0 h1 h2 h3
    have hY0 := hl4 Y (lt_trans hys Fp.p_lt) h4 h5 h6 h7
    have ex' := mont_in_out _ hx
    have ey' := mont_in_out _ hy
    rw [← hX, hX0, Nat.zero_mul, Nat.zero_mod] at ex'
    rw [← hY, hY0, Nat.zero_mul, Nat.zero_mod] at ey'
    rw [onCurve_iff, ← ex', ← ey'] at hon
    exact absurd hon (by decide)
  have hz : toCurveW (unpackW L) = Accel.natToLeLimbs 4 X ++ Accel.natToLeLimbs 4 Y ++
      Accel.natToLeLimbs 4 Fp.R := by
    rw [toCurveW, if_neg hnz, hu]
  obtain ⟨cx, cy, cz⟩ := cells3 _ _ _ (lt_trans hxs Fp.p_lt) (lt_trans hys Fp.p_lt)
    (lt_trans Fp.R_lt Fp.p_lt)
  have hsp : specPt (toCurveW (unpackW L)) = dec8 L := by
    unfold specPt dec8 jacXY
    rw [hz, cx, cy, cz, Fp.toAffine, if_pos rfl]
    simp only
    rw [mont_in_out _ hx, mont_in_out _ hy]
  refine ⟨Or.inr ⟨by rw [hz, cz], ?_⟩, hsp⟩
  rw [hsp]
  exact dec8_onCurve ⟨hl, hv, hon⟩

theorem p_lt_255 : Fp.p < 2 ^ 255 := by decide +kernel

/-- A sum of two point-code outputs, held as twelve words. -/
theorem specPt_addJ_cells (A B : List Word) (hA : JacW A) (hB : JacW B) :
    specPt (Accel.natToLeLimbs 4 (Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).1 ++
      Accel.natToLeLimbs 4 (Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.1 ++
      Accel.natToLeLimbs 4 (Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.2) =
      specPt A + specPt B ∧
    JacOk (Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).1
      (Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.1
      (Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.2 := by
  have b := Fp.addJ_lt (X1 := ptX A) (Y1 := ptY A) (Z1 := ptZ A) (X2 := ptX B) (Y2 := ptY B) (Z2 := ptZ B)
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
  obtain ⟨cx, cy, cz⟩ := cells3 _ _ _ b.1 b.2.1 b.2.2
  have hok := jacOk_addJ (jacOk_of_jacW hA) (jacOk_of_jacW hB)
  refine ⟨?_, hok⟩
  rw [specPt_eq _ (by rw [cz]; exact hok.1), specPt_eq _ (ptZ_lt_of_jacW hA),
    specPt_eq _ (ptZ_lt_of_jacW hB), cx, cy, cz]
  exact specT_addJ (jacOk_of_jacW hA) (jacOk_of_jacW hB)

theorem chunk_lt {M n m : ℕ} (hm : m ∈ Zcash.Circuits.Specs.Sinsemilla.chunksOf M n) : m < 1024 := by
  unfold Zcash.Circuits.Specs.Sinsemilla.chunksOf at hm
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hm
  exact lt_of_lt_of_le (Zcash.Circuits.Specs.bitrange_lt _ _ _) (by norm_num [Zcash.Circuits.Specs.K])

/-- **`commit_ivk` is the spec's `Commit^ivk`.** For `ak`, `nk` given as canonical values (their
`to_le_bits` are the message), a defined Sinsemilla hash (flag `1`) and `[rivk] R` from the run's
facts: `Commit^ivk_rivk(ak, nk)` is defined and is the commitment's affine `x` out of Montgomery
form. -/
theorem ivk_spec (av nv : ℕ) (hav : av < Fp.p) (hnv : nv < Fp.p) (rk : List Word)
    (hf : ivkFlag qIvkW (boolBytesToWords (ivkBit (Accel.natToLeLimbs 4 av)
      (Accel.natToLeLimbs 4 nv)) 65) = 1#8)
    (hm : mulFacts rIvkW rk) :
    Zip2005.commitIvk (((Accel.leLimbsToNat rk * Fq.rInv % Fq.q : ℕ)) : Zcash.Circuits.Fq)
        (av : Zcash.Circuits.Fp) (nv : Zcash.Circuits.Fp) =
      some (((jacXY (ivkW qIvkW rIvkW (boolBytesToWords (ivkBit (Accel.natToLeLimbs 4 av)
        (Accel.natToLeLimbs 4 nv)) 65) rk)).1 : ℕ) : Zcash.Circuits.Fp) := by
  set Bv := boolBytesToWords (ivkBit (Accel.natToLeLimbs 4 av) (Accel.natToLeLimbs 4 nv)) 65 with hBv
  have hch : chunks Bv 51 = Zcash.Circuits.Specs.Sinsemilla.commitIvkChunks av nv :=
    ivk_chunks av nv (lt_trans hav p_lt_255)
  obtain ⟨L, hL⟩ : ∃ L, ivkFold qIvkW Bv = some L := by
    cases h : ivkFold qIvkW Bv with
    | none => rw [ivkFlag_none h] at hf; exact absurd hf (by decide)
    | some L => exact ⟨L, rfl⟩
  have hT : ∀ m ∈ chunks Bv 51, AffOk (sEntryW sTable m) ∧
      dec8 (sEntryW sTable m) = Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S m := by
    intro m hm
    rw [hch] at hm
    exact sEntry_ok m (chunk_lt hm)
  have hLok : AffOk L := (sinFold_spec sTable _ (chunks Bv 51) hT (some (commitAcc0 qIvkW))
    (fun L' h => by cases h; exact affOk_qIvk)).2 L (by rw [← ivkFold_eq]; exact hL)
  have hfold := sinFold_hash sTable _ (chunks Bv 51) hT (commitAcc0 qIvkW) affOk_qIvk
  rw [← ivkFold_eq, hL, dec8_qIvk, hch, Option.map_some] at hfold
  unfold Zip2005.commitIvk
  rw [ZMod.val_cast_of_lt (show av < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD from hav),
    ZMod.val_cast_of_lt (show nv < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD from hnv), ← hfold,
    Option.map_some]
  refine congrArg some ?_
  obtain ⟨hJh, hsh⟩ := jacW_toCurve L hLok
  have hb : ptZ rIvkW ≠ 0 → ValidA (mulBase rIvkW) := fun _ => validA_mulBase rIvk_onCurve
  have hJm := jacW_mulW rIvkW rk hb hm
  have hsm := specPt_mulW rIvkW rk hb hm (Or.inl rIvk_onCurve)
  rw [specPt_rIvk] at hsm
  have hW : ivkW qIvkW rIvkW Bv rk =
      Accel.natToLeLimbs 4 (Fp.addJ (ptX (toCurveW (unpackW L))) (ptY (toCurveW (unpackW L)))
        (ptZ (toCurveW (unpackW L))) (ptX (mulW rIvkW rk)) (ptY (mulW rIvkW rk)) (ptZ (mulW rIvkW rk))).1 ++
      Accel.natToLeLimbs 4 (Fp.addJ (ptX (toCurveW (unpackW L))) (ptY (toCurveW (unpackW L)))
        (ptZ (toCurveW (unpackW L))) (ptX (mulW rIvkW rk)) (ptY (mulW rIvkW rk)) (ptZ (mulW rIvkW rk))).2.1 ++
      Accel.natToLeLimbs 4 (Fp.addJ (ptX (toCurveW (unpackW L))) (ptY (toCurveW (unpackW L)))
        (ptZ (toCurveW (unpackW L))) (ptX (mulW rIvkW rk)) (ptY (mulW rIvkW rk)) (ptZ (mulW rIvkW rk))).2.2 := by
    rw [ivkW, ivkJ_eq, ivkHash_some hL, jX_eq, jY_eq, jZ_eq]
  have hsum := (specPt_addJ_cells _ _ hJh hJm).1
  rw [← hW, hsh, hsm] at hsum
  show (dec8 L + _).x = _
  rw [← hsum]
  rfl

end Cases.Zip2005.Poseidon
