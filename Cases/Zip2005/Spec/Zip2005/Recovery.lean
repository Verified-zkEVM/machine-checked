import Cases.Zip2005.Spec.Zip2005.Sending

set_option autoImplicit false

/-!
# The Proposed Recovery Statement

ZIP 2005 § Rationale → 'Proposed Recovery Protocol' → 'Proposed Recovery
Statement'. This is the statement a future Recovery Protocol would prove, and the
reason the ZIP changes the `rcm` and `rivk` derivations at all: enforcing those
derivations in-circuit is what makes the note commitment binding on the whole
note tuple post-quantumly.

## What is abstract here, and why

Two things in the statement are not pinned down by the ZIP, so they are
parameters rather than definitions. Making them arguments keeps every use site
honest about what it depends on.

**The signature-of-knowledge schemes.** The ZIP gives the two *statements*
concretely — `{qsk | qk = H^qk(qsk)}` and `{sk | BindKeys^sk(...)}`, both
transcribed below — but names `SoK^qsk.Validate` and `SoK^sk.Validate` without
fixing a scheme. `SoKSchemes` carries the two validation relations together with
the soundness property that makes them signatures *of knowledge*: validation
implies the corresponding statement is satisfiable. The ZIP does not spell that
implication out inline, because it is what "signature of knowledge" means, and
its key-binding and Spendability arguments use it throughout.

**The rehashed commitment tree.** The conjunct "`path` is a path to `leaf` in the
rehashed commitment tree" refers to a tree the ZIP requires but does not specify.
Its security analysis is explicit about why one is needed: `MerkleCRH` is
`SinsemillaHash`, whose collision resistance rests on the Pallas discrete-log
relation problem, so it is not post-quantum collapsing and the public tree "must
be rehashed with a collapsing hash". Which hash is left to a future ZIP. So
`RehashedTree` is a parameter. `Zip2005.merklePath` is the *deployed* Sinsemilla
tree, for contrast — it is what the current protocol uses and what the ZIP says
the recovery circuit may not.

`H^qk` is a parameter for the separate reason given in `Zip2005.KeyComponents`.

## Defects in the source, and the choices made

The ZIP's text is internally inconsistent in a few places. Each is resolved here
in favour of the normative section, and recorded:

1. `H^{rcm,Orchard}_rseed(0x03, noterepr)` here takes a lead byte and a tuple;
   § 4.7.3 defines the function with five positional arguments and no lead byte
   (the lead byte belongs to `Derive_rcm`, and `0x0B` is already inside
   `pre_rcm`); the Rationale writes it a third way, `H^rcm_rseed(noterepr)`.
   **Resolved to § 4.7.3.** Since the statement fixes lead byte `0x03`,
   `Derive_rcm^Orchard` at `0x03` is `H^rcm` (`deriveRcmOrchard_leadByte_three`),
   so all three readings agree on the value.
2. `leaf = MerkleCRH(cm_x, ρ)` here, against "becomes `MerkleCRH(ρ, cm_x)`"
   earlier in the same section. **Left to the parameter**: the rehashed tree's
   leaf function is unspecified anyway, so `RehashedTree.leaf` takes both in a
   fixed order and the ambiguity is confined to one field rather than smeared
   through the statement.
3. `H^rivk_legacy` and `H^rivk` are two names for one function. Both are
   available; see `Zip2005.hRivkLegacy`.
4. `SoK^sk`'s witness domain is `𝔹^[ℓ_sk]` (bits) where `SoK^qsk`'s is
   `𝔹^𝕐[ℓ_qsk/8]` (bytes). **Both taken as bytes**, since `sk` is a byte string
   everywhere else in the protocol and `ℓ_sk = 256` is a multiple of 8.
5. `pos` is in the auxiliary input but appears in no listed conjunct. It is
   retained, and consumed by `RehashedTree.PathTo` — which is where a Merkle
   path check does need it.
6. The primary-input tuple has a stray parenthesis in the source.

Reference: <https://zips.z.cash/zip-2005>.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq Point)

/-! ## `BindKeys^sk` and the two `SoK` statements -/

/-- `BindKeys^sk(sk, ak^ℙ, nk, rivk_ext) := (ak^ℙ = [H^ask(sk)] 𝒢^Orchard
∧ nk = H^nk(sk) ∧ rivk_ext = H^rivk_legacy(sk))`.

Note what this does *not* say: `H^ask`, not `askNormalised`. The ZIP writes the
unnormalised derivation here, so `BindKeys` does not pin the `ỹ` bit of `ak^ℙ`.
That is deliberate and is discussed in the ZIP's key-binding analysis: leaving the
sign unconstrained is what lets `ak` be a single `𝔽_{q_P}` element, at a stated
cost of a factor 2 in concrete security. A transcription that "helpfully"
substituted `askNormalised` would silently strengthen the statement. -/
def BindKeysSk (sk : List UInt8) (akP : Point Fp) (nk : Fp) (rivkExt : Fq) : Prop :=
  akP = spendAuthDerivePublic (hAsk sk) ∧ nk = hNk sk ∧ rivkExt = hRivkLegacy sk

/-- `SoK^qsk.Statement = { qsk ⦂ 𝔹^𝕐[ℓ_qsk/8] | qk = H^qk(qsk) }`. -/
def SoKQskStatement (b3 : Blake3DeriveKey) (qk qsk : List UInt8) : Prop :=
  qsk.length = qskBytes ∧ qk = hQk b3 qsk

/-- `SoK^sk.Statement = { sk | BindKeys^sk(sk, ak^ℙ, nk, rivk_ext) }`. -/
def SoKSkStatement (sk : List UInt8) (akP : Point Fp) (nk : Fp) (rivkExt : Fq) : Prop :=
  sk.length = ellSk / 8 ∧ BindKeysSk sk akP nk rivkExt

/-- The two signature-of-knowledge schemes the statement validates against.

`Sig*` are the signature types, which the ZIP writes as
`SoK^qsk((qk), SigHash)` and `SoK^sk((ak^ℙ, nk, rivk_ext), SigHash)`. The
`sound*` fields are what make these signatures *of knowledge*: a valid signature
implies the corresponding statement is satisfiable. -/
structure SoKSchemes (b3 : Blake3DeriveKey) (SigQsk SigSk : Type) where
  /-- `SoK^qsk.Validate((qk), SigHash, σ_qsk)`. -/
  validateQsk : List UInt8 → List UInt8 → SigQsk → Prop
  /-- `SoK^sk.Validate((ak^ℙ, nk, rivk_ext), SigHash, σ_sk)`. -/
  validateSk : Point Fp → Fp → Fq → List UInt8 → SigSk → Prop
  /-- Knowledge soundness for `SoK^qsk`. -/
  soundQsk : ∀ qk sighash σ, validateQsk qk sighash σ → ∃ qsk, SoKQskStatement b3 qk qsk
  /-- Knowledge soundness for `SoK^sk`. -/
  soundSk : ∀ akP nk rivkExt sighash σ,
    validateSk akP nk rivkExt sighash σ → ∃ sk, SoKSkStatement sk akP nk rivkExt

/-! ## The rehashed commitment tree

Required by ZIP 2005 and specified by it only negatively: the hash must be
collapsing, which `MerkleCRH = SinsemillaHash` is not. See the module docstring.
-/

/-- The note commitment tree after rehashing under a collapsing hash.

`leaf` is the ZIP's `MerkleCRH(cm_x, ρ)` step — the "extra `MerkleCRH` for
`leaf`" its cost analysis counts — and `PathTo root leaf path pos` is the
authentication-path check. Both are abstract because the ZIP defers the hash. -/
structure RehashedTree (depth : ℕ) where
  /-- The leaf label of a note, from `cm_x` and `ρ`. -/
  leaf : Fp → Fp → Option Fp
  /-- `path`, at position `pos`, authenticates `leaf` under `root`. -/
  PathTo : Fp → Fp → (Fin depth → Fp) → ℕ → Prop

/-! ## The statement's inputs -/

/-- The primary (public) input.

`SigHash` is `MessageHash` in the ZIP; it is a byte string here, since the ZIP
does not fix its width at this point and the statement only passes it to the two
`Validate` calls. -/
structure PrimaryInput where
  /-- `rt^Orchard ⦂ {0..q_P−1}`, the anchor. -/
  rtOrchard : Fp
  /-- `rk`, a `SpendAuthSig^Orchard` public key. -/
  rk : Point Fp
  /-- `nf ⦂ 𝔽_{q_P}`, the revealed nullifier. -/
  nf : Fp
  /-- `SigHash ⦂ MessageHash`. -/
  sighash : List UInt8

/-- The auxiliary (witness) input.

The `(qk, σ_qsk) ∪ {(⊥,⊥)}` of the ZIP is one `Option` over the *pair*, not two
independent `Option`s — the two are `⊥` together or present together, and making
that a type-level fact rather than a conjunct removes a way to state the
authorisation exclusivity wrongly. -/
structure AuxiliaryInput (SigQsk SigSk : Type) (depth : ℕ) where
  /-- `path ⦂ {0..q_P−1}^[MerkleDepth^Orchard]`. -/
  path : Fin depth → Fp
  /-- `pos ⦂ {0..2^MerkleDepth^Orchard − 1}`. -/
  pos : ℕ
  /-- `α ⦂ 𝔽_{r_P}`, the spend-authorisation randomiser. -/
  α : Fq
  /-- `ak^ℙ ⦂ ℙ*`. -/
  akP : Point Fp
  /-- `nk ⦂ 𝔽_{q_P}`. -/
  nk : Fp
  /-- `rivk_ext ⦂ 𝔽_{r_P}`. -/
  rivkExt : Fq
  /-- `rivk ⦂ 𝔽_{r_P}`, the randomness actually used. -/
  rivk : Fq
  /-- `(qk, σ_qsk) ⦂ (𝔹^𝕐[ℓ_qk/8] × SoK^qsk((qk), SigHash)) ∪ {(⊥,⊥)}`. -/
  quantum : Option (List UInt8 × SigQsk)
  /-- `σ_sk ⦂ SoK^sk((ak^ℙ, nk, rivk_ext), SigHash) ∪ {⊥}`. -/
  sigmaSk : Option SigSk
  /-- `rseed ⦂ 𝔹^𝕐[32]`. -/
  rseed : List UInt8
  /-- `g_d ⦂ ℙ*`. -/
  gd : Point Fp
  /-- `v ⦂ {0..2^ℓ_value − 1}`. -/
  v : ℕ
  /-- `ρ ⦂ 𝔽_{q_P}`. -/
  ρ : Fp

/-! ## The statement -/

/-- The authorisation exclusivity conjunct:
`((qk, σ_qsk) = (⊥,⊥)) ≠ (σ_sk = ⊥)`.

Exactly one authorisation path is taken. Split out because it is the conjunct
most easily mis-transcribed: it is an *inequality between two propositions*, not
a disjunction, and it forbids both branches as well as neither. -/
def AuthorisationExclusive {SigQsk SigSk : Type} {depth : ℕ}
    (aux : AuxiliaryInput SigQsk SigSk depth) : Prop :=
  (aux.quantum = none) ≠ (aux.sigmaSk = none)

/-- **The Proposed Recovery Statement.**

Transcribed conjunct for conjunct from the ZIP. The `let`-bound quantities of the
source (`ivk`, `pk_d`, `ψ`, `noterepr`, `rcm`, `cm`, `cm_x`, `leaf`) become
existentials with defining equations, so that the partial ones — `Commit^ivk` and
`NoteCommit^Orchard` may be `⊥`, and the ZIP separately forbids it — carry their
definedness rather than being silently total. -/
def RecoveryStatement {SigQsk SigSk : Type} (b3 : Blake3DeriveKey)
    (S : SoKSchemes b3 SigQsk SigSk) (T : RehashedTree merkleDepthOrchard)
    (pi : PrimaryInput)
    (aux : AuxiliaryInput SigQsk SigSk merkleDepthOrchard) : Prop :=
  -- ak = Extract_ℙ(ak^ℙ)
  let ak : Fp := extractP aux.akP
  -- ψ = H^{ψ,Orchard}_rseed(ρ̲)
  let ψ : Fp := hPsiOrchard aux.rseed aux.ρ
  ∃ ivk : Fp, ∃ cm : Point Fp, ∃ leaf : Fp,
    -- rk = SpendAuthSig^Orchard.RandomizePublic(α, ak^ℙ)
    pi.rk = spendAuthRandomizePublic aux.α aux.akP
    -- ((qk, σ_qsk) = (⊥,⊥)) ≠ (σ_sk = ⊥)
    ∧ AuthorisationExclusive aux
    -- (qk, σ_qsk) ≠ (⊥,⊥) ⇒ (SoK^qsk.Validate((qk), SigHash, σ_qsk)
    --                          ∧ rivk_ext = H^rivk_ext_qk(ak, nk))
    ∧ (∀ qk σ, aux.quantum = some (qk, σ) →
        S.validateQsk qk pi.sighash σ ∧ aux.rivkExt = hRivkExtQk qk ak aux.nk)
    -- σ_sk ≠ ⊥ ⇒ SoK^sk.Validate((ak^ℙ, nk, rivk_ext), SigHash, σ_sk)
    ∧ (∀ σ, aux.sigmaSk = some σ →
        S.validateSk aux.akP aux.nk aux.rivkExt pi.sighash σ)
    -- rivk ∈ { rivk_ext, H^rivk_int_rivk_ext(ak, nk) }
    ∧ (aux.rivk = aux.rivkExt
        ∨ aux.rivk = hRivkInt (i2leosp 256 aux.rivkExt.val) ak aux.nk)
    -- let ivk = Commit^ivk_rivk(ak, nk) ∧ ivk ∉ {0, ⊥}
    ∧ commitIvk aux.rivk ak aux.nk = some ivk
    ∧ ivk ≠ 0
    -- let pk_d = [ivk] g_d, and the note representation built from it
    ∧ (let pkd : Point Fp := smul (modRP ivk) aux.gd
       -- let rcm = H^{rcm,Orchard}_rseed(noterepr)
       let rcm : Fq := hRcmOrchard aux.rseed aux.gd pkd aux.v aux.ρ ψ
       -- let cm = NoteCommit^Orchard_rcm(noterepr) ∧ cm ≠ ⊥
       noteCommit rcm aux.gd pkd aux.v aux.ρ ψ = some cm)
    -- let cm_x = Extract_ℙ(cm); let leaf = MerkleCRH(cm_x, ρ)
    ∧ T.leaf (extractP cm) aux.ρ = some leaf
    -- path is a path to leaf in the rehashed commitment tree
    ∧ T.PathTo pi.rtOrchard leaf aux.path aux.pos
    -- nf = DeriveNullifier_nk(ρ, ψ, cm)
    ∧ pi.nf = deriveNullifier aux.nk aux.ρ ψ cm

/-! ## Consequences

Small facts that are worth having as theorems because they are the ones a reader
would otherwise have to re-derive to check the transcription is not vacuous.
-/

variable {SigQsk SigSk : Type} {b3 : Blake3DeriveKey}

/-- Exactly one authorisation path: the quantum pair and `σ_sk` are never both
present. -/
theorem not_both_authorisations {depth : ℕ}
    {aux : AuxiliaryInput SigQsk SigSk depth}
    (h : AuthorisationExclusive aux)
    (hq : aux.quantum ≠ none) (hs : aux.sigmaSk ≠ none) : False := by
  simp only [AuthorisationExclusive, ne_eq, eq_iff_iff] at h
  exact h ⟨fun hn => absurd hn hq, fun hn => absurd hn hs⟩

/-- Nor are they ever both absent. -/
theorem not_neither_authorisation {depth : ℕ}
    {aux : AuxiliaryInput SigQsk SigSk depth}
    (h : AuthorisationExclusive aux)
    (hq : aux.quantum = none) (hs : aux.sigmaSk = none) : False := by
  simp only [AuthorisationExclusive, hq, hs] at h
  exact h rfl

/-- On the quantum branch the statement pins `rivk_ext` to `H^rivk_ext_qk`, and a
`qsk` exists that `qk` is derived from. This is the branch that makes the
key-binding argument's tagged union genuinely two-sided. -/
theorem quantum_branch_binds {S : SoKSchemes b3 SigQsk SigSk}
    {T : RehashedTree merkleDepthOrchard} {pi : PrimaryInput}
    {aux : AuxiliaryInput SigQsk SigSk merkleDepthOrchard}
    {qk : List UInt8} {σ : SigQsk}
    (h : RecoveryStatement b3 S T pi aux) (hq : aux.quantum = some (qk, σ)) :
    aux.rivkExt = hRivkExtQk qk (extractP aux.akP) aux.nk
      ∧ ∃ qsk, SoKQskStatement b3 qk qsk := by
  obtain ⟨-, -, -, -, -, hqk, -⟩ := h
  obtain ⟨hval, hrivk⟩ := hqk qk σ hq
  exact ⟨hrivk, S.soundQsk qk pi.sighash σ hval⟩

/-- On the classical branch a spending key exists that `ak^ℙ`, `nk` and
`rivk_ext` are all derived from — `BindKeys^sk`. -/
theorem classical_branch_binds {S : SoKSchemes b3 SigQsk SigSk}
    {T : RehashedTree merkleDepthOrchard} {pi : PrimaryInput}
    {aux : AuxiliaryInput SigQsk SigSk merkleDepthOrchard} {σ : SigSk}
    (h : RecoveryStatement b3 S T pi aux) (hs : aux.sigmaSk = some σ) :
    ∃ sk, BindKeysSk sk aux.akP aux.nk aux.rivkExt := by
  obtain ⟨-, -, -, -, -, -, hsk, -⟩ := h
  obtain ⟨sk, -, hbind⟩ := S.soundSk aux.akP aux.nk aux.rivkExt pi.sighash σ (hsk σ hs)
  exact ⟨sk, hbind⟩

/-- `ivk` is never `⊥` and never zero, so `pk_d = [ivk] g_d` is a well-defined
non-identity point whenever `g_d` is — the ZIP's `ivk ∉ {0, ⊥}` conjunct doing
its job. -/
theorem ivk_ne_zero {S : SoKSchemes b3 SigQsk SigSk}
    {T : RehashedTree merkleDepthOrchard} {pi : PrimaryInput}
    {aux : AuxiliaryInput SigQsk SigSk merkleDepthOrchard}
    (h : RecoveryStatement b3 S T pi aux) :
    ∃ ivk : Fp, commitIvk aux.rivk (extractP aux.akP) aux.nk = some ivk ∧ ivk ≠ 0 := by
  obtain ⟨ivk, -, -, -, -, -, -, -, hcommit, hne, -⟩ := h
  exact ⟨ivk, hcommit, hne⟩

end Zip2005
