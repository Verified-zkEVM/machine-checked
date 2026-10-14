import Cases.Zip2005.Spec.Zip2005.KeyBinding

set_option autoImplicit false

/-!
# Divergences: where the SP1 guest departs from this specification

The premise of this repository is that `zip-2005/program/src/main.rs` implements
ZIP 2005. It does not, yet — and the gaps belong in the artifact rather than in a
paragraph of prose, so that they are conjuncts visibly dropped and can be
retired one at a time.

`GuestStatement` below is what the guest actually asserts, at the typed level;
`recovery_implies_guest` proves it is a weakening of `RecoveryStatement`. Nothing
here says anything about the compiled RISC-V; the repository's `Proof/` relates the
two (`Proof.guest_elf_run`).

## The gaps, with sources

**1. The Merkle conjunct is absent entirely.** The guest parses the
authentication path and stops:

```rust
// 16.  TODO: requires new merkle path verification method using collapsing hash function
let path = witness.parse_merkle_path().unwrap();
```

The root is never computed and never compared to `instance.anchor`, so
`anchor` is read and unused. Note that the ZIP could not be fully satisfied here
anyway: it requires a **rehashed** tree under a collapsing hash, and does not say
which hash. See `Zip2005.RehashedTree`.

**2. Both `SoK` conjuncts are unenforced, and `SigHash` is unused.** The quantum
branch is `unimplemented!()` — three `unimp` words in the image — so
`SoK^qsk.Validate` never runs. On the classical branch the guest takes
`σ_sk = sk` itself ("the SoK is implemented in the program, so the 'signature' is
the secret key itself", `zip-2005/lib/src/lib.rs`) and checks `BindKeys` directly,
which is a *stronger* thing to do than validating a signature — but neither
branch binds anything to `SigHash`, which the guest reads and ignores. Since a
signature of knowledge is what ties the authorisation to a particular
transaction, dropping the message is not a cosmetic omission.

**3. The `ask` sign is witness-chosen.** The guest checks

```rust
let derived_spend_auth_key = SpendAuthorizingKey::derive_unchecked(&sk, witness.negate());
```

so it accepts `ak^ℙ = [H^ask(sk)] 𝒢` *or* `ak^ℙ = [−H^ask(sk)] 𝒢`, with the sign
supplied by an untrusted witness field. `BindKeys^sk` pins the unnormalised
derivation only. This is recorded as `BindKeysSkNegate` and is **not** folded into
the weakening theorem, because it is not a clean weakening: the two predicates
are incomparable at `negate = true`. It interacts with § 4.2.3's separate
requirement that `ỹ(ak^ℙ) = 0` — which `BindKeys^sk` does not restate — and with
the ZIP's deliberate choice not to constrain that sign in the key-binding
predicate. Worth raising with the ZIP owners rather than resolved here: `rk` is a
public input and *does* depend on the sign of `ak^ℙ`, unlike `ak`.

**4. Nothing is committed as public output.** Every `sp1_zkvm::io::commit*` call
in `main.rs` is commented out, and `artifacts/run-report.txt` records `output 0
bytes`. So the guest's assertions are not bound to the instance in the proof at
all: it proves "there exist an instance and a witness satisfying these checks",
not "*these* public inputs are satisfiable". This is a property of the harness,
not of the statement, so it does not appear in `GuestStatement` — but it is the
gap that most changes what a proof would mean.

**5. Sinsemilla uses incomplete addition.** ZIP 2005's security analysis states
that protocol Theorem 5.4.4's incomplete-addition justification is invalid
against a discrete-log-breaking adversary, and therefore that the Recovery
Statement's Sinsemilla must use **complete** additions. The guest's `sinsemilla`
fork uses incomplete addition with `⊥` propagation, as does the imported
`Zcash.Circuits.Specs.Sinsemilla` that `Zip2005.commitIvk` and
`Zip2005.noteCommit` are built from. So this divergence is inherited by the
specification here too, and is recorded in `Zip2005.Imported` as well: what is
transcribed is what the *deployed* functions compute.

**6. `ivk` is reinterpreted across fields.** `main.rs` carries its own warning:

```rust
// WARNING: Check whether this is ok, ivk is a value in base field, which we are turning into a
// value in the scalar field ([ivk]), make sure this is ok doing it this way
```

This one is fine, and `Zip2005.qP_lt_rP` is why: `q_P < r_P`, so `modRP` is
injective and no information is lost. Recorded because the source flags it.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq Point)

/-! ## The guest's `BindKeys` -/

/-- `BindKeys^sk` as the guest checks it: the sign of the `ask` derivation is
taken from the witness rather than fixed.

At `negate = false` this is `BindKeysSk`. At `negate = true` it is a different
predicate, not a weaker one — which is why divergence 3 above is recorded rather
than absorbed into `recovery_implies_guest`. -/
def BindKeysSkNegate (negate : Bool) (sk : List UInt8) (akP : Point Fp)
    (nk : Fp) (rivkExt : Fq) : Prop :=
  akP = spendAuthDerivePublic (if negate then -hAsk sk else hAsk sk)
    ∧ nk = hNk sk ∧ rivkExt = hRivkLegacy sk

/-- At `negate = false` the guest's check is exactly `BindKeys^sk`. -/
theorem bindKeysSkNegate_false (sk : List UInt8) (akP : Point Fp)
    (nk : Fp) (rivkExt : Fq) :
    BindKeysSkNegate false sk akP nk rivkExt ↔ BindKeysSk sk akP nk rivkExt := by
  simp [BindKeysSkNegate, BindKeysSk]

/-! ## What the guest asserts -/

/-- The guest's conjuncts, at a *named* `ivk` and `cm`.

Split from `GuestStatement` so that the note commitment can be referred to by
name — which is what the Merkle conjunct needs, since it hashes `Extract_ℙ(cm)`.

Numbered to match the guest's own step comments. Step 16 has no conjunct: that is
divergence 1. -/
def GuestChecks (pi : PrimaryInput) (negate : Bool) (sk : List UInt8)
    (α : Fq) (akP : Point Fp) (nk : Fp) (rivkExt rivk : Fq)
    (rseed : List UInt8) (gd : Point Fp) (v : ℕ) (ρ : Fp)
    (ivk : Fp) (cm : Point Fp) : Prop :=
  -- ak = Extract_ℙ(ak^ℙ) and ψ = H^{ψ,Orchard}_rseed(ρ̲), as in the ZIP
  let ak : Fp := extractP akP
  let ψ : Fp := hPsiOrchard rseed ρ
  let pkd : Point Fp := smul (modRP ivk) gd
  let rcm : Fq := hRcmOrchard rseed gd pkd v ρ ψ
  -- 1. rk = SpendAuthSig.RandomizePublic(alpha, ak)
  pi.rk = spendAuthRandomizePublic α akP
  -- 5. SoK^sk.Validate, implemented as the derivation checks themselves
  ∧ BindKeysSkNegate negate sk akP nk rivkExt
  -- 6. rivk ∈ {rivk_ext, H(ak, nk)}
  ∧ (rivk = rivkExt ∨ rivk = hRivkInt (i2leosp 256 rivkExt.val) ak nk)
  -- 7, 8. commit ivk, and ivk is neither 0 nor ⊥
  ∧ commitIvk rivk ak nk = some ivk
  ∧ ivk ≠ 0
  -- 9-13. pk_d, psi, rcm, and the note commitment, which must not be ⊥
  ∧ noteCommit rcm gd pkd v ρ ψ = some cm
  -- 17. the nullifier
  ∧ pi.nf = deriveNullifier nk ρ ψ cm

/-- The statement `zip-2005/program/src/main.rs` actually establishes, at the
typed level: `RecoveryStatement` with the Merkle and `SoK` conjuncts removed, and
`BindKeys` checked directly against a witnessed spending key. -/
def GuestStatement (pi : PrimaryInput) (negate : Bool) (sk : List UInt8)
    (α : Fq) (akP : Point Fp) (nk : Fp) (rivkExt rivk : Fq)
    (rseed : List UInt8) (gd : Point Fp) (v : ℕ) (ρ : Fp) : Prop :=
  ∃ ivk : Fp, ∃ cm : Point Fp,
    GuestChecks pi negate sk α akP nk rivkExt rivk rseed gd v ρ ivk cm

/-- **The guest's statement is a weakening of ZIP 2005's.**

Given the Recovery Statement on its classical branch, everything the guest checks
holds — with `negate = false`, the case in which the guest's authorisation check
coincides with `BindKeys^sk`. The conjuncts that do not survive are exactly the
gaps enumerated in this module's docstring: the two `SoK` validations (replaced
here by the `BindKeys` they imply), `SigHash`, and the Merkle path.

The converse is false, which is the point — `guest_plus_gaps_gives_recovery`
says precisely what has to be added back. -/
theorem recovery_implies_guest
    {SigQsk SigSk : Type} {b3 : Blake3DeriveKey}
    {S : SoKSchemes b3 SigQsk SigSk} {T : RehashedTree merkleDepthOrchard}
    {pi : PrimaryInput} {aux : AuxiliaryInput SigQsk SigSk merkleDepthOrchard}
    {σ : SigSk}
    (h : RecoveryStatement b3 S T pi aux) (hs : aux.sigmaSk = some σ) :
    ∃ sk, GuestStatement pi false sk aux.α aux.akP aux.nk aux.rivkExt aux.rivk
      aux.rseed aux.gd aux.v aux.ρ := by
  obtain ⟨ivk, cm, -, hrk, -, -, hsk, hrivk, hcommit, hne, hnote, -, -, hnf⟩ := h
  obtain ⟨sk, -, hbind⟩ :=
    S.soundSk aux.akP aux.nk aux.rivkExt pi.sighash σ (hsk σ hs)
  exact ⟨sk, ivk, cm, hrk, (bindKeysSkNegate_false _ _ _ _).mpr hbind,
    hrivk, hcommit, hne, hnote, hnf⟩

/-! ## What is missing, as propositions

Naming the dropped conjuncts makes them retirable one at a time: when the guest
grows a Merkle check, `GuestStatement` gains `MerkleConjunct` and this section
loses an entry.
-/

/-- Divergence 1: the conjunct the guest does not have. The anchor is read and
never used. -/
def MerkleConjunct (T : RehashedTree merkleDepthOrchard) (pi : PrimaryInput)
    (path : Fin merkleDepthOrchard → Fp) (pos : ℕ) (cm : Point Fp) (ρ : Fp) : Prop :=
  ∃ leaf : Fp, T.leaf (extractP cm) ρ = some leaf
    ∧ T.PathTo pi.rtOrchard leaf path pos

/-- Divergence 2: the conjunct binding the authorisation to the transaction.
Neither branch of the guest establishes anything about `SigHash`. -/
def SigHashBound {SigQsk SigSk : Type} {b3 : Blake3DeriveKey}
    (S : SoKSchemes b3 SigQsk SigSk) (pi : PrimaryInput)
    (akP : Point Fp) (nk : Fp) (rivkExt : Fq)
    (quantum : Option (List UInt8 × SigQsk)) (sigmaSk : Option SigSk) : Prop :=
  (∀ qk σ, quantum = some (qk, σ) → S.validateQsk qk pi.sighash σ)
    ∧ (∀ σ, sigmaSk = some σ → S.validateSk akP nk rivkExt pi.sighash σ)

/-- Adding the dropped conjuncts back recovers the Recovery Statement exactly.

This is the precise content of "what is missing": given the guest's own checks at
some `ivk` and `cm`, the Recovery Statement follows from exactly three further
things — the authorisation exclusivity, the `SigHash` binding, and the Merkle
path (plus, on the quantum branch, the `rivk_ext` derivation the guest cannot
reach because it panics there).

So the gap between the guest and the ZIP is not an informal list; it is these
hypotheses. Retiring a divergence means deleting one. -/
theorem guest_plus_gaps_gives_recovery
    {SigQsk SigSk : Type} {b3 : Blake3DeriveKey}
    {S : SoKSchemes b3 SigQsk SigSk} {T : RehashedTree merkleDepthOrchard}
    {pi : PrimaryInput} {aux : AuxiliaryInput SigQsk SigSk merkleDepthOrchard}
    {sk : List UInt8} {ivk : Fp} {cm : Point Fp}
    (hguest : GuestChecks pi false sk aux.α aux.akP aux.nk aux.rivkExt aux.rivk
      aux.rseed aux.gd aux.v aux.ρ ivk cm)
    (hauth : AuthorisationExclusive aux)
    (hsig : SigHashBound S pi aux.akP aux.nk aux.rivkExt aux.quantum aux.sigmaSk)
    (hqk : ∀ qk σ, aux.quantum = some (qk, σ) →
      aux.rivkExt = hRivkExtQk qk (extractP aux.akP) aux.nk)
    (hmerkle : MerkleConjunct T pi aux.path aux.pos cm aux.ρ) :
    RecoveryStatement b3 S T pi aux := by
  obtain ⟨hrk, -, hrivk, hcommit, hne, hnote, hnf⟩ := hguest
  obtain ⟨leaf, hleaf, hpath⟩ := hmerkle
  exact ⟨ivk, cm, leaf, hrk, hauth, fun qk σ hq => ⟨hsig.1 qk σ hq, hqk qk σ hq⟩,
    hsig.2, hrivk, hcommit, hne, hnote, hleaf, hpath, hnf⟩

end Zip2005
