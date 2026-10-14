import Cases.Zip2005.Bridge.SpecSinsemilla
import Cases.Zip2005.Orchard.CommitIvk
import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Orchard.NullifierDerive
import Cases.Zip2005.Precompile

/-!
# The guest's fixed points are the spec's

The domain points and blinding bases as the guest holds them (raw coordinates in the read-only
segment, through `from_raw` / `from_xy` / `to_curve`, or `pack`ed) against ironwood's constants,
by kernel evaluation of the guest's own arithmetic (`decide +kernel`): `dec8_qIvk`
(`Q^CommitIvk`), `specPt_rIvk` (`R^CommitIvk`, the spec's `SCommitIvk`), with the facts the bridges
need of them (`affOk_qIvk`, `rIvk_onCurve`, `validA_mulBase`).
-/

namespace Cases.Zip2005.SpecMul

open RiscvZkvm.Rv64 Cases.Zip2005.Precompile.Pallas
open Zcash.Circuits (Fp Fq Point)

set_option autoImplicit false

theorem acc0_qIvk : Cases.Zip2005.commitAcc0 Cases.Zip2005.qIvkW =
    Accel.natToLeLimbs 4 2593820817260930114322133467408868473290945477826616247349533151445648376562 ++
    Accel.natToLeLimbs 4 12214744946019415453501880094709511126888074367290315326445800415816181472958 := by
  decide +kernel

theorem jacXY_rIvk : jacXY Cases.Zip2005.rIvkW =
    (17022113834174368664964072539940476916905682548990455171271428285673934201112,
     18912017636736613471143674001158885358143653198146604093009134371854861983145) := by
  decide +kernel

theorem dec8_qIvk : dec8 (Cases.Zip2005.commitAcc0 Cases.Zip2005.qIvkW) = Zip2005.QCommitIvk := by
  obtain ⟨_, hx, hy⟩ := encode_decode
    (a := 2593820817260930114322133467408868473290945477826616247349533151445648376562)
    (b := 12214744946019415453501880094709511126888074367290315326445800415816181472958)
    (by decide) (by decide)
  rw [acc0_qIvk]
  unfold dec8
  rw [hx, hy]
  rfl

theorem specPt_rIvk : specPt Cases.Zip2005.rIvkW = Zip2005.SCommitIvk := by
  unfold specPt
  rw [jacXY_rIvk]
  rfl

/-- A Jacobian point whose spec reading is on the curve: `mul`'s tagged affine base is valid. -/
theorem validA_mulBase {pt : List Word} (h : (specPt pt).OnCurve) : ValidA (Cases.Zip2005.mulBase pt) := by
  obtain ⟨hl, hx, hy⟩ := encode_decode (a := (jacXY pt).1) (b := (jacXY pt).2)
    (Nat.mod_lt _ Fp.p_pos) (Nat.mod_lt _ Fp.p_pos)
  have e : Cases.Zip2005.mulBase pt = 1#64 :: (Accel.natToLeLimbs 4 (jacXY pt).1 ++
      Accel.natToLeLimbs 4 (jacXY pt).2) := rfl
  rw [e]
  refine ⟨by simp only [List.length_cons, hl], fun _ => ⟨?_, ?_⟩⟩
  · rw [List.drop_one, List.tail_cons, ptValid_iff, hx, hy]
    exact ⟨Nat.mod_lt _ Fp.p_pos, Nat.mod_lt _ Fp.p_pos⟩
  · rw [List.drop_one, List.tail_cons, hx, hy]
    rw [Point.onCurve_iff] at h
    exact (onCurve_iff_sw _ _).mpr h

theorem specPt_valid_of_onCurve {pt : List Word} (h : (specPt pt).OnCurve) : (specPt pt).Valid :=
  Or.inl h

theorem rIvk_onCurve : (specPt Cases.Zip2005.rIvkW).OnCurve := by
  rw [specPt_rIvk]; exact Zcash.Circuits.Action.orchardBases.commitIvkR.onCurve

theorem affOk_qIvk : AffOk (Cases.Zip2005.commitAcc0 Cases.Zip2005.qIvkW) := by
  obtain ⟨hl, hx, hy⟩ := encode_decode
    (a := 2593820817260930114322133467408868473290945477826616247349533151445648376562)
    (b := 12214744946019415453501880094709511126888074367290315326445800415816181472958)
    (by decide) (by decide)
  have hon := Zcash.Circuits.Action.ivkQ_onCurve
  rw [← show dec8 (Cases.Zip2005.commitAcc0 Cases.Zip2005.qIvkW) = Zcash.Circuits.Action.ivkQ from dec8_qIvk,
    Point.onCurve_iff] at hon
  rw [acc0_qIvk] at hon ⊢
  refine ⟨hl, ?_, (onCurve_iff_sw _ _).mpr hon⟩
  rw [ptValid_iff, hx, hy]
  exact ⟨by decide, by decide⟩

end Cases.Zip2005.SpecMul
