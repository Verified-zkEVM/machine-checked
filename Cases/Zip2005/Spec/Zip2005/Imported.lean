import Cases.Zip2005.Spec.Zip2005.Prf
import Cases.Zip2005.Spec.Zcash.Circuits.Action.RealBases
import Cases.Zip2005.Spec.Zcash.Circuits.Poseidon.HashTheorems
import Cases.Zip2005.Spec.Zcash.Circuits.Sinsemilla.Merkle

set_option autoImplicit false

/-!
# The protocol-specification functions ZIP 2005 imports

ZIP 2005 defines very little cryptography of its own. It changes how `rcm` and
`rivk` are *derived* and leaves the commitment and hash functions alone —
`Commit^ivk`, `NoteCommit^Orchard`, `MerkleCRH`, `DeriveNullifier`, `Extract_ℙ`,
`repr_ℙ`, `GroupHash^ℙ` and RedPallas are all imported from the protocol
specification. Its Recovery Statement then *uses* them.

This module is the single place where each imported name is pinned to a
definition in `zcash/ironwood`. Nothing here is new mathematics; the point is
that an auditor can read one file to see exactly which existing, kernel-checked
definition stands behind each symbol the ZIP writes — and, just as important,
which one does not.

## Shape choices

`zcash/ironwood` states these in the *circuit's* vocabulary: fixed bases carry
precomputed window tables (`Ecc.MulFixed.FixedBase`), and messages are packed
`ℕ`s decomposed into `K`-bit chunks. A specification should not inherit that. So
the bases are re-exposed here as plain `Point Fp` via `.point`, and scalar
multiplication as one uniform operation, `smul`, on arbitrary points.

That loses nothing: `Fq • FixedBase` in ironwood is *defined* as
`s.val • B.point` (`Ecc/MulFixed/Theorems.lean`, `FixedBase.scalarMul`), so
`smul` agrees with it on every base by definition, and `smul_fixedBase` records
that.

## ⊥

Partial protocol operations return `Option`. `Sinsemilla.hashToPoint` is `⊥` when
any incomplete addition in its chain degenerates, and the ZIP's `cm ≠ ⊥` and
`ivk ∉ {0, ⊥}` conjuncts are exactly about that. We therefore use the `Option`
values directly rather than ironwood's `HashGuarded`, which is the *guarded* form
`∀ B, hash = some B → P B` and is vacuously true at `⊥` — right for a circuit
completeness argument, wrong for a statement that must *forbid* `⊥`.

## Two recorded gaps

**`GroupHash^ℙ` is not available.** ZIP 2005's Recovery Statement names
`𝒢^Orchard = GroupHash^ℙ("z.cash:Orchard", "G")`, and `Commit^ivk`'s base is
`𝒮 = GroupHash^ℙ("z.cash:Orchard-CommitIvk-r", "")`. `zcash/ironwood` does not
derive these: it certifies them as constant on-curve points (`RealBases.lean`,
with `..._onCurve` proofs and the 2^10 Sinsemilla `S` table "python-validated
on-curve"). `CompElliptic` has the SSWU map and the 3-isogeny proved against
§ 5.4.9.8, but not the BLAKE2b `hash_to_field` front end that would join them up;
`oxarbitrage/sinsemilla-formal` axiomatises `groupHash_ne_zero` for the same
reason. So the bases here are *the deployed constants*, tied to the protocol by
ironwood's certificates and by agreement with the reference implementation — not
by a derivation from `GroupHash`. Recorded, not hidden.

**Sinsemilla here uses incomplete addition.** ZIP 2005's security analysis is
explicit that protocol Theorem 5.4.4's incomplete-addition justification is
*invalid* against a discrete-log-breaking adversary, and therefore that "the
Recovery Statement's Sinsemilla must use complete additions". The imported
`hashToPoint` is the deployed, incomplete-addition Sinsemilla (`⸭`, with `⊥`
propagation). It is the right function for stating what the *current* Orchard
functions compute, and the wrong one for the recovery circuit the ZIP proposes.
See `Zip2005.Divergences`.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq Point)
open Zcash.Circuits.Specs.Sinsemilla
  (orchardGenerators hashToPoint commitIvkChunks noteCommitChunks merkleChunks)
open Zcash.Circuits.Action (orchardBases)

/-! ## Scalar multiplication -/

/-- `[s] P` for a scalar `s ⦂ 𝔽_{r_P}` and a Pallas point `P`.

Routed through `s.val` and `ℕ`-scalar multiplication, which is well-defined
because the group has order `r_P`. -/
def smul (s : Fq) (P : Point Fp) : Point Fp := s.val • P

/-- `smul` agrees with `zcash/ironwood`'s fixed-base scalar multiplication on
every fixed base, by definition rather than by a proof about window tables. -/
theorem smul_fixedBase (s : Fq) (B : Zcash.Circuits.Ecc.MulFixed.FixedBase) :
    smul s B.point = s • B := rfl

/-! ## The fixed bases (§ 5.4.7.1, § 5.4.8.4, § 4.16)

Each is `GroupHash^ℙ` of a fixed personalisation in the specification, and a
certified constant here; see the module docstring.
-/

/-- `𝒢^Orchard = GroupHash^ℙ("z.cash:Orchard", "G")` (§ 5.4.7.1), the
`SpendAuthSig^Orchard` generator. -/
def GOrchard : Point Fp := orchardBases.spendAuthG.point

/-- `𝒦^Orchard` (§ 4.16), the base of the nullifier's scalar multiplication. -/
def KOrchard : Point Fp := orchardBases.nullifierK.point

/-- `𝒮 = GroupHash^ℙ("z.cash:Orchard-CommitIvk-r", "")` (§ 5.4.8.4), the
`Commit^ivk` blinding base. ZIP 2005's key-binding argument is written in terms
of this point. -/
def SCommitIvk : Point Fp := orchardBases.commitIvkR.point

/-- `ℛ = GroupHash^ℙ("z.cash:Orchard-NoteCommit-r", "")` (§ 5.4.8.4), the
`NoteCommit^Orchard` blinding base. ZIP 2005's Spendability argument writes
`K_ℛ = log_ℛ(𝒦)`. -/
def RNoteCommit : Point Fp := orchardBases.noteCommitR.point

/-- `Q("z.cash:Orchard-CommitIvk-M")`, the Sinsemilla domain point of
`Commit^ivk`. -/
def QCommitIvk : Point Fp := orchardBases.ivkQ

/-- `Q("z.cash:Orchard-NoteCommit-M")`, the Sinsemilla domain point of
`NoteCommit^Orchard`. -/
def QNoteCommit : Point Fp := orchardBases.noteQ

/-- `Q("z.cash:Orchard-MerkleCRH")`, the Sinsemilla domain point of `MerkleCRH`. -/
def QMerkle : Point Fp := orchardBases.merkleQ

/-! ## `SpendAuthSig^Orchard` (§ 5.4.7.1) -/

/-- `SpendAuthSig^Orchard.DerivePublic(ask) = [ask] 𝒢^Orchard`. -/
def spendAuthDerivePublic (ask : Fq) : Point Fp := smul ask GOrchard

/-- `SpendAuthSig^Orchard.RandomizePublic(α, ak^ℙ) = ak^ℙ + [α] 𝒢^Orchard`.

This is RedDSA public-key re-randomisation, and the first conjunct of the
Recovery Statement. -/
def spendAuthRandomizePublic (α : Fq) (akP : Point Fp) : Point Fp :=
  smul α GOrchard + akP

/-! ## `PRF^nfOrchard` (§ 5.4.2) -/

/-- `PRF^nfOrchard(nk, ρ) := Poseidon(nk, ρ)` (§ 5.4.2), the Orchard `P128Pow5T3`
instance at `ConstantLength<2>`. -/
def prfNfOrchard (nk ρ : Fp) : Fp :=
  Zcash.Circuits.Poseidon.Hash.ConstantLength.value #v[nk, ρ]

/-! ## Sinsemilla commitments (§ 5.4.8.4) -/

/-- `Commit^ivk_rivk(ak, nk) = Extract_ℙ(M' + [rivk] 𝒮)`, where
`M' = SinsemillaHashToPoint("z.cash:Orchard-CommitIvk-M",
I2LEBSP_255(ak) ‖ I2LEBSP_255(nk))` — that is, `SinsemillaShortCommit` at the
`CommitIvk` domain (§ 5.4.8.4).

`⊥` exactly when the Sinsemilla chain is `⊥`. The trailing addition is the
*complete* group operation, as the specification requires of `SinsemillaCommit`'s
blinding step. -/
def commitIvk (rivk : Fq) (ak nk : Fp) : Option Fp :=
  (hashToPoint orchardGenerators.S QCommitIvk (commitIvkChunks ak.val nk.val)).map
    (fun M => (M + smul rivk SCommitIvk).x)

/-- `NoteCommit^Orchard_rcm(g★_d, pk★_d, v, ρ, ψ)`, i.e. `SinsemillaCommit` at the
`NoteCommit` domain (§ 5.4.8.4).

The message is `g★_d ‖ pk★_d ‖ I2LEBSP_64(v) ‖ I2LEBSP_255(ρ) ‖ I2LEBSP_255(ψ)`,
1090 bits. The `g★_d` and `pk★_d` inputs enter as an x-coordinate together with a
`ỹ` sign bit — which is precisely what `repr_ℙ` is — so `Zip2005.ytilde` supplies
the sign bits and no byte encoding is involved.

Returns the commitment *point*: the ZIP's statement needs `cm ≠ ⊥` and then
`cm_x = Extract_ℙ(cm)`, and `DeriveNullifier` consumes the point. -/
def noteCommit (rcm : Fq) (gd pkd : Point Fp) (v : ℕ) (ρ ψ : Fp) :
    Option (Point Fp) :=
  (hashToPoint orchardGenerators.S QNoteCommit
      (noteCommitChunks gd.x.val (ytilde gd) pkd.x.val (ytilde pkd) v ρ.val ψ.val)).map
    (fun M => M + smul rcm RNoteCommit)

/-! ## `MerkleCRH^Orchard` (§ 5.4.1.3) -/

/-- `MerkleCRH^Orchard(l, left, right) =
SinsemillaHash("z.cash:Orchard-MerkleCRH", l★ ‖ left★ ‖ right★)` (§ 5.4.1.3),
where `l` is the layer index. `⊥` when the Sinsemilla chain is `⊥`. -/
def merkleCRH (l : ℕ) (left right : Fp) : Option Fp :=
  (hashToPoint orchardGenerators.S QMerkle (merkleChunks l left.val right.val)).map
    (fun P => P.x)

/-- A Merkle authentication path of depth `d` from `start` to `root`, in
`zcash/ironwood`'s encoding-level form. `left`/`right` are the 255-bit
representatives at each layer and `side` says which of the two the current node
is.

Used for the Recovery Statement's "`path` is a path to `leaf`" conjunct. Note
this is a path in the *deployed* Sinsemilla tree; the ZIP requires the recovery
circuit to work over the **rehashed** tree, under a collapsing hash, because
`MerkleCRH`'s collision resistance rests on the Pallas discrete-log relation
problem and so is not post-quantum. That rehashed tree is not specified in
ZIP 2005 and does not exist here. See `Zip2005.Divergences`. -/
def merklePath (d : ℕ) (start root : Fp)
    (left right : ℕ → ℕ) (side : ℕ → Bool) : Prop :=
  Zcash.Circuits.Sinsemilla.Merkle.ExactMerklePathData
    orchardGenerators QMerkle 0 d start root left right side

/-! ## `DeriveNullifier` (§ 4.16) -/

/-- `DeriveNullifier_nk(ρ, ψ, cm) :=
Extract_ℙ([(PRF^nfOrchard_nk(ρ) + ψ) mod q_P] 𝒦^Orchard + cm)` (§ 4.16).

The `mod q_P` of the specification is the reinterpretation `Zip2005.modRP` of a
base-field element as a scalar, which is well-defined because `q_P < r_P`
(`Zip2005.qP_lt_rP`). -/
def deriveNullifier (nk ρ ψ : Fp) (cm : Point Fp) : Fp :=
  extractP (smul (modRP (prfNfOrchard nk ρ + ψ)) KOrchard + cm)

end Zip2005
