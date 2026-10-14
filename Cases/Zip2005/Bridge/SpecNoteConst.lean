import Cases.Zip2005.Bridge.SpecJacPt
import Cases.Zip2005.Bridge.SpecConst
import Cases.Zip2005.Poseidon.PoseidonHash
import Cases.Zip2005.Orchard.NullifierDerive
import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Precompile

/-!
# `PRF^nfOrchard`, and the note commitment's and nullifier's fixed points

`D_hash2`: the guest's `Hash::<ConstantLength<2>>::hash` (the permutation over Montgomery
representatives, `permute_bridge`) is the spec's `prfNfOrchard`. The `NoteCommit` domain point, its
blinding base and `𝒦^Orchard` as the guest holds them are ironwood's (`dec8_qNote`,
`specPt_rNote`, `specPt_kOrchard`), by kernel evaluation.
-/

namespace Cases.Zip2005.Poseidon

open RiscvZkvm.Rv64 Cases.Zip2005.BridgeMul Cases.Zip2005.Precompile.Pallas
open Zcash.Circuits (Point)
open Zcash.Circuits.Poseidon

set_option autoImplicit false

theorem D_mont (x : ℕ) (hx : x < Fp.p) : D (Fp.mul x Fp.R2) = (x : F) := by
  rw [← castD, mont_in_out _ hx]

theorem D_capacity : D capacity = Hash.ConstantLength.capacity 2 := by
  unfold capacity Hash.ConstantLength.capacity
  rw [D_mont _ (by decide +kernel)]
  norm_num

/-- **The guest's `Hash::<ConstantLength<2>>::hash` is the spec's `PRF^nfOrchard`**, on the values
its Montgomery representatives stand for. -/
theorem D_hash2 (a b : ℕ) : D (hash2 a b) = Zip2005.prfNfOrchard (D a) (D b) := by
  have h := congrArg Permute.State.x0 (permute_bridge (Fp.add 0 a, Fp.add 0 b, capacity))
  have hx : Dst (Fp.add 0 a, Fp.add 0 b, capacity) =
      Sponge.AddInput.value (Sponge.AddInputInput.mk (Permute.State.mk 0 0 (Hash.ConstantLength.capacity 2))
        (Hash.ConstantLength.blockValue (#v[D a, D b] : Vector F 2) 0)) := by
    simp only [Dst, D_add, D_zero, D_capacity, Sponge.AddInput.value, Hash.ConstantLength.blockValue,
      Hash.ConstantLength.paddedWord]
    rfl
  rw [hx] at h
  unfold hash2 Zip2005.prfNfOrchard Hash.ConstantLength.value
  simp only [show Hash.ConstantLength.blockCount 2 = 0 + 1 from rfl, Fin.foldl_succ, Fin.foldl_zero,
    Hash.ConstantLength.stepValueAt, Hash.ConstantLength.absorbPermuteValue, Permute.concreteValue,
    Sponge.GetOutput.value]
  exact h

theorem acc0_qNote : Cases.Zip2005.commitAcc0 Cases.Zip2005.qNoteW =
    Accel.natToLeLimbs 4 10629404576683096409262958701336170057000067777256141967953463442979689100381 ++
    Accel.natToLeLimbs 4 22898949290933268079297281211505753011910178734473470279111609228438645877859 := by
  decide +kernel

theorem jacXY_rNote : jacXY Cases.Zip2005.rNoteW =
    (17502433695644481444785977856966854265310331039772160001849803703443502427667,
     27531606546556235994383748883097777001194017792923801570415255878186539366371) := by
  decide +kernel

theorem jacXY_kOrchard : jacXY Cases.Zip2005.kOrchardW =
    (17144890976040313974462754624161095328261290075490099718273142830262355741301,
     9661337292872073193100428608853316471968232023361741282759000480983323509196) := by
  decide +kernel

theorem dec8_qNote : dec8 (Cases.Zip2005.commitAcc0 Cases.Zip2005.qNoteW) = Zip2005.QNoteCommit := by
  obtain ⟨_, hx, hy⟩ := encode_decode
    (a := 10629404576683096409262958701336170057000067777256141967953463442979689100381)
    (b := 22898949290933268079297281211505753011910178734473470279111609228438645877859)
    (by decide) (by decide)
  rw [acc0_qNote]
  unfold dec8
  rw [hx, hy]
  rfl

theorem specPt_rNote : specPt Cases.Zip2005.rNoteW = Zip2005.RNoteCommit := by
  unfold specPt; rw [jacXY_rNote]; rfl

theorem specPt_kOrchard : specPt Cases.Zip2005.kOrchardW = Zip2005.KOrchard := by
  unfold specPt; rw [jacXY_kOrchard]; rfl

theorem rNote_onCurve : (specPt Cases.Zip2005.rNoteW).OnCurve := by
  rw [specPt_rNote]; exact Zcash.Circuits.Action.orchardBases.noteCommitR.onCurve

theorem kOrchard_onCurve : (specPt Cases.Zip2005.kOrchardW).OnCurve := by
  rw [specPt_kOrchard]; exact Zcash.Circuits.Action.orchardBases.nullifierK.onCurve

theorem affOk_qNote : AffOk (Cases.Zip2005.commitAcc0 Cases.Zip2005.qNoteW) := by
  obtain ⟨hl, hx, hy⟩ := encode_decode
    (a := 10629404576683096409262958701336170057000067777256141967953463442979689100381)
    (b := 22898949290933268079297281211505753011910178734473470279111609228438645877859)
    (by decide) (by decide)
  have hon := Zcash.Circuits.Action.noteQ_onCurve
  rw [← show dec8 (Cases.Zip2005.commitAcc0 Cases.Zip2005.qNoteW) = Zcash.Circuits.Action.noteQ from dec8_qNote,
    Point.onCurve_iff] at hon
  rw [acc0_qNote] at hon ⊢
  refine ⟨hl, ?_, (onCurve_iff_sw _ _).mpr hon⟩
  rw [ptValid_iff, hx, hy]
  exact ⟨by decide, by decide⟩

end Cases.Zip2005.Poseidon
