import Cases.Zip2005.Bridge.SpecCommitIvk
import Cases.Zip2005.Bridge.SpecNoteConst
import Cases.Zip2005.Precompile

/-!
# `NoteCommitment::derive` and `Nullifier::derive` are the spec's

`note_spec`: for the message the guest lays out from the points' encodings, `v`, `ρ`, `ψ`, a defined
hash and `[rcm] R` from the run's facts, `NoteCommit^Orchard` is defined and is the guest's
commitment point, which keeps the Jacobian invariant. `nf_spec`: the nullifier's affine `x` is
`DeriveNullifier_nk(ρ, ψ, cm)` on the values the Montgomery representatives stand for.

Proof-engineering note: a defeq check (`exact`, `unfold`, a closing `rfl`) that reaches a sum of
computed points evaluates the scalar multiplication or the Poseidon permutation symbolically;
the steps here go through equation lemmas (`rw [Zip2005.deriveNullifier]`) and an abstract triple
(`x_of_sum`) instead.
-/

namespace Cases.Zip2005.Poseidon

open RiscvZkvm.Rv64 Cases.Zip2005.SpecMul Cases.Zip2005.Precompile.Pallas
open Zcash.Circuits (Point)

set_option autoImplicit false

theorem Fq_mont_in_out (a : ℕ) (ha : a < Fq.q) : Fq.mul a Fq.R2 * Fq.rInv % Fq.q = a := by
  have key : ((Fq.mul a Fq.R2 * Fq.rInv % Fq.q : ℕ) : ZMod Fq.q) = (a : ZMod Fq.q) := by
    have h1 : ((Fq.R2 * Fq.rInv * Fq.rInv : ℕ) : ZMod Fq.q) = 1 := by
      rw [← ZMod.natCast_mod, show Fq.R2 * Fq.rInv * Fq.rInv % Fq.q = 1 by decide +kernel, Nat.cast_one]
    unfold Fq.mul
    simp only [ZMod.natCast_mod, Nat.cast_mul] at h1 ⊢
    linear_combination (a : ZMod Fq.q) * h1
  have := congrArg ZMod.val key
  rwa [ZMod.val_cast_of_lt (Nat.mod_lt _ Fq.q_pos), ZMod.val_cast_of_lt ha] at this

theorem val_lt_255 (x : Zcash.Circuits.Fp) : x.val < 2 ^ 255 :=
  lt_trans (ZMod.val_lt x) p_lt_255

/-- **`NoteCommitment::derive`'s commitment is the spec's `NoteCommit^Orchard`.** For the message
the guest lays out from the points' encodings (`x + 2^255 ỹ`), `v`, `ρ`, `ψ`, a defined hash (flag
`1`) and `[rcm] R` from the run's facts: the commitment is defined and is the guest's point, which
satisfies the Jacobian invariant (so it can be added to). -/
theorem note_spec (gd pkd : Point Zcash.Circuits.Fp) (v : Word) (ρ ψ : Zcash.Circuits.Fp) (rcm : List Word)
    (hf : commitFlag qNoteW (boolBytesToWords (noteBit
      (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
      (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
      (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137) = 1#8)
    (hm : mulFacts rNoteW rcm) :
    Zip2005.noteCommit (((Accel.leLimbsToNat rcm * Fq.rInv % Fq.q : ℕ)) : Zcash.Circuits.Fq) gd pkd v.toNat ρ ψ =
      some (specPt (commitW qNoteW rNoteW (boolBytesToWords (noteBit
        (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
        (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
        (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137) rcm)) ∧
    JacOk (ptX (commitW qNoteW rNoteW (boolBytesToWords (noteBit
        (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
        (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
        (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137) rcm))
      (ptY (commitW qNoteW rNoteW (boolBytesToWords (noteBit
        (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
        (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
        (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137) rcm))
      (ptZ (commitW qNoteW rNoteW (boolBytesToWords (noteBit
        (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
        (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
        (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137) rcm)) := by
  set Bv := boolBytesToWords (noteBit
      (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
      (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
      (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137 with hBv
  have hch : chunks Bv 109 = Zcash.Circuits.Specs.Sinsemilla.noteCommitChunks gd.x.val (Zip2005.ytilde gd)
      pkd.x.val (Zip2005.ytilde pkd) v.toNat ρ.val ψ.val :=
    note_chunks _ _ _ _ _ _ v (val_lt_255 _) (Nat.mod_lt _ (by decide)) (val_lt_255 _)
      (Nat.mod_lt _ (by decide)) (val_lt_255 _) (val_lt_255 _)
  obtain ⟨L, hL⟩ : ∃ L, commitFold qNoteW Bv = some L := by
    cases h : commitFold qNoteW Bv with
    | none => rw [commitFlag_none h] at hf; exact absurd hf (by decide)
    | some L => exact ⟨L, rfl⟩
  have hT : ∀ m ∈ chunks Bv 109, AffOk (sEntryW sTable m) ∧
      dec8 (sEntryW sTable m) = Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S m := by
    intro m hm
    rw [hch] at hm
    unfold Zcash.Circuits.Specs.Sinsemilla.noteCommitChunks at hm
    exact sEntry_ok m (chunk_lt hm)
  have hLok : AffOk L := (sinFold_spec sTable _ (chunks Bv 109) hT (some (commitAcc0 qNoteW))
    (fun L' h => by cases h; exact affOk_qNote)).2 L (by rw [← commitFold_eq]; exact hL)
  have hfold := sinFold_hash sTable _ (chunks Bv 109) hT (commitAcc0 qNoteW) affOk_qNote
  rw [← commitFold_eq, hL, dec8_qNote, hch, Option.map_some] at hfold
  obtain ⟨hJh, hsh⟩ := jacW_toCurve L hLok
  have hb : ptZ rNoteW ≠ 0 → ValidA (mulBase rNoteW) := fun _ => validA_mulBase rNote_onCurve
  have hJm := jacW_mulW rNoteW rcm hb hm
  have hsm := specPt_mulW rNoteW rcm hb hm (Or.inl rNote_onCurve)
  rw [specPt_rNote] at hsm
  have hW : commitW qNoteW rNoteW Bv rcm =
      Accel.natToLeLimbs 4 (Fp.addJ (ptX (toCurveW (unpackW L))) (ptY (toCurveW (unpackW L)))
        (ptZ (toCurveW (unpackW L))) (ptX (mulW rNoteW rcm)) (ptY (mulW rNoteW rcm)) (ptZ (mulW rNoteW rcm))).1 ++
      Accel.natToLeLimbs 4 (Fp.addJ (ptX (toCurveW (unpackW L))) (ptY (toCurveW (unpackW L)))
        (ptZ (toCurveW (unpackW L))) (ptX (mulW rNoteW rcm)) (ptY (mulW rNoteW rcm)) (ptZ (mulW rNoteW rcm))).2.1 ++
      Accel.natToLeLimbs 4 (Fp.addJ (ptX (toCurveW (unpackW L))) (ptY (toCurveW (unpackW L)))
        (ptZ (toCurveW (unpackW L))) (ptX (mulW rNoteW rcm)) (ptY (mulW rNoteW rcm)) (ptZ (mulW rNoteW rcm))).2.2 := by
    rw [commitW_eq, commitJ_eq, commitHash_some hL, jX_eq, jY_eq, jZ_eq]
  obtain ⟨hsum, hok⟩ := specPt_addJ_cells _ _ hJh hJm
  have b := Fp.addJ_lt (X1 := ptX (toCurveW (unpackW L))) (Y1 := ptY (toCurveW (unpackW L)))
    (Z1 := ptZ (toCurveW (unpackW L))) (X2 := ptX (mulW rNoteW rcm)) (Y2 := ptY (mulW rNoteW rcm))
    (Z2 := ptZ (mulW rNoteW rcm))
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
  obtain ⟨cx, cy, cz⟩ := cells3 _ _ _ b.1 b.2.1 b.2.2
  rw [← hW, hsh, hsm] at hsum
  refine ⟨?_, ?_⟩
  · unfold Zip2005.noteCommit
    rw [← hfold, Option.map_some]
    exact congrArg some hsum.symm
  · rw [hW, cx, cy, cz]
    exact hok

/-- The affine `x` of a Jacobian sum, out of Montgomery form, is the `x` of the spec sum (stated
over an abstract triple, so that no rewrite meets the computed point). -/
theorem x_of_sum (J : ℕ × ℕ × ℕ) (A B : List Word) (hA : JacOk (ptX A) (ptY A) (ptZ A))
    (hB : JacOk (ptX B) (ptY B) (ptZ B)) (hzA : ptZ A < Fp.p)
    (hJ : J = Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)) :
    ((affineX J * Fp.rInv % Fp.p : ℕ) : Zcash.Circuits.Fp) = (specPt A + specPt B).x := by
  have hsum := specT_addJ hA hB
  rw [← specPt_eq _ hzA, ← specPt_eq _ hB.1, ← hJ] at hsum
  have hZ : J.2.2 < Fp.p := by rw [hJ]; exact addJ_Z_lt hA.1 hB.1
  rw [castD, affineX_eq]
  refine (congrArg Prod.fst (D_toAffine J.1 J.2.1 hZ)).trans ?_
  rw [← hsum, specT, Point.ofCoords_x]

/-- **`Nullifier::derive` is the spec's `DeriveNullifier`.** On Montgomery representatives `nk`,
`ρ`, `ψ`, a commitment satisfying the Jacobian invariant, and `[k] 𝒦` from the run's facts: the
nullifier's affine `x` out of Montgomery form is `DeriveNullifier_nk(ρ, ψ, cm)`. -/
theorem nf_spec (nk rho psi : ℕ) (cm : List Word) (hcm : JacOk (ptX cm) (ptY cm) (ptZ cm))
    (hm : mulFacts kOrchardW (nullifierScalarW nk rho psi)) :
    ((nullifierX nk rho psi cm * Fp.rInv % Fp.p : ℕ) : Zcash.Circuits.Fp) =
      Zip2005.deriveNullifier (D nk) (D rho) (D psi) (specPt cm) := by
  have hb : ptZ kOrchardW ≠ 0 → ValidA (mulBase kOrchardW) := fun _ => validA_mulBase kOrchard_onCurve
  have hJm := jacW_mulW kOrchardW (nullifierScalarW nk rho psi) hb hm
  have hsm := specPt_mulW kOrchardW (nullifierScalarW nk rho psi) hb hm (Or.inl kOrchard_onCurve)
  rw [specPt_kOrchard] at hsm
  -- the scalar out of Montgomery form is `PRF^nf + ψ` as a number
  set c := Fp.add (hash2 nk rho) psi * Fp.rInv % Fp.p with hc
  have hcp : c < Fp.p := Nat.mod_lt _ Fp.p_pos
  have hcq : c < Fq.q := lt_trans hcp (by decide +kernel)
  have hs : Accel.leLimbsToNat (nullifierScalarW nk rho psi) * Fq.rInv % Fq.q = c := by
    unfold nullifierScalarW
    rw [Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (lt_trans (Fq.mul_lt _ _) (by decide +kernel)),
      Fq_mont_in_out _ hcq]
  rw [hs] at hsm
  have hmod : Zip2005.modRP (Zip2005.prfNfOrchard (D nk) (D rho) + D psi) = ((c : ℕ) : Zcash.Circuits.Fq) := by
    unfold Zip2005.modRP
    rw [← D_hash2, ← D_add, ← castD, ← hc,
      ZMod.val_cast_of_lt (show c < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD from hcp)]
  have key := x_of_sum (nullifierJ nk rho psi cm) _ _ (jacOk_of_jacW hJm) hcm
    (ptZ_lt_of_jacW hJm) (nullifierJ_eq nk rho psi cm)
  rw [hsm] at key
  rw [← nullifierX_eq, ← hmod] at key
  rw [Zip2005.deriveNullifier, Zip2005.extractP]
  exact key

end Cases.Zip2005.Poseidon
