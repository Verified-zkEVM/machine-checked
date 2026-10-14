import Cases.Zip2005.Spec.Zip2005.Imported

set_option autoImplicit false

/-!
# § 4.2.3 Orchard Key Components

ZIP 2005 replaces protocol specification § 4.2.3 wholesale. It introduces a flag
`use_qsk`, two new derivations `H^qsk` and `H^qk`, a new `rivk` derivation
`H^rivk_ext_qk` for the quantum branch, and states the whole key-derivation
procedure as normative: these keys "MUST be derived as follows".

`use_qsk = false` reproduces pre-2026.8.0 behaviour exactly, including the `ỹ`-bit
normalisation of `ask`.

Reference: <https://zips.z.cash/zip-2005>, § 'Changes to the Protocol
Specification' → § 4.2.3.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq Point)

/-! ## BLAKE3 `derive_key`, as a parameter

`H^qk` is the only primitive in ZIP 2005 with no Lean implementation available.
It is BLAKE3's `derive_key` mode (BLAKE3 specification § 2.1.2), and
`Verified-zkEVM/clean`'s `Clean/Specs/BLAKE3.lean` — the closest thing that
exists — has the compression function and the single-chunk layer with `rfl`-pinned
vectors, but stops at `processChunk`: no parent/tree hashing, no root output
extension, and so no `derive_key`.

Rather than hide that behind an `opaque` constant with a made-up default, the
primitive is a **parameter**. Every definition that needs it says so in its
signature, so the dependency is visible at each use site and cannot be mistaken
for something this file establishes. That also matches how the ZIP's own
key-binding argument treats it — as one of five random oracles.

The parameterisation is not merely a placeholder: it is also the right shape,
because the ZIP fixes the *mode and context string* but delegates the function to
the BLAKE3 specification.
-/

/-- BLAKE3's `derive_key` mode: a context string, key material, and an output
length in bytes (BLAKE3 specification § 2.1.2). -/
abbrev Blake3DeriveKey := String → List UInt8 → ℕ → List UInt8

/-! ## The derivations (§ 4.2.3) -/

/-- `H^ask(sk) = ToScalar^Orchard(PRF^expand_sk([0x06]))`. -/
def hAsk (sk : List UInt8) : Fq := toScalarOrchard (prfExpand sk [Sep.ask])

/-- `H^nk(sk) = ToBase^Orchard(PRF^expand_sk([0x07]))`. -/
def hNk (sk : List UInt8) : Fp := toBaseOrchard (prfExpand sk [Sep.nk])

/-- `H^rivk(sk) = ToScalar^Orchard(PRF^expand_sk([0x08]))`.

The Recovery Statement and `BindKeys^sk` call this same function
`H^rivk_legacy`. Two names, one definition — see `hRivkLegacy`. -/
def hRivk (sk : List UInt8) : Fq := toScalarOrchard (prfExpand sk [Sep.rivk])

/-- `H^rivk_legacy`, the name the Recovery Statement and `BindKeys^sk` use for
`H^rivk`.

The ZIP writes both, and defines only one; recording the alias as a definitional
equality is more useful than picking a winner, and makes the redundancy visible
to anyone comparing the two sections. -/
def hRivkLegacy (sk : List UInt8) : Fq := hRivk sk

theorem hRivkLegacy_eq_hRivk (sk : List UInt8) : hRivkLegacy sk = hRivk sk := rfl

/-- `H^qsk(sk) = truncate_32(PRF^expand_sk([0x0C]))`. **Added by ZIP 2005.**

`qsk` is a 32-byte string, not a field element: it is key material for BLAKE3,
not a scalar. -/
def hQsk (sk : List UInt8) : List UInt8 := truncate 32 (prfExpand sk [Sep.qsk])

@[simp] theorem hQsk_length (sk : List UInt8) : (hQsk sk).length = 32 := by
  simp [hQsk, truncate]

/-- `H^qk(qsk) = BLAKE3.derive_key("Zcash ZIP 2005 qk-derivation v1", qsk, 32)`.
**Added by ZIP 2005.** See the section above on why `b3` is a parameter. -/
def hQk (b3 : Blake3DeriveKey) (qsk : List UInt8) : List UInt8 :=
  b3 qkDerivationContext qsk 32

/-- `H^rivk_ext_qk(ak, nk) =
ToScalar^Orchard(PRF^expand_qk([0x0D] ‖ I2LEOSP_256(ak) ‖ I2LEOSP_256(nk)))`.
**Added by ZIP 2005.**

Seeded by `qk`, so this is the quantum branch's `rivk_ext`. The preimage is
`32 + 1 + 32 + 32 = 97` bytes, inside one 128-byte BLAKE2b block — which is what
`Zip2005.ellQk_single_block` is about, and why the ZIP's cost analysis counts one
compression here rather than two. -/
def hRivkExtQk (qk : List UInt8) (ak nk : Fp) : Fq :=
  toScalarOrchard (prfExpand qk ([Sep.rivkExtQk] ++ i2leosp 256 ak.val ++ i2leosp 256 nk.val))

/-- `H^rivk_int_rivk_ext(ak, nk) =
ToScalar^Orchard(PRF^expand_rivk_ext([0x83] ‖ I2LEOSP_256(ak) ‖ I2LEOSP_256(nk)))`.

Defined by ZIP 32 and *imported* by ZIP 2005's Recovery Statement, which is why
it takes the encoded `rivk_ext` as its seed. This is the second branch of the
`rivk ∈ {rivk_ext, H^rivk_int(ak, nk)}` conjunct. -/
def hRivkInt (rivkExt : List UInt8) (ak nk : Fp) : Fq :=
  toScalarOrchard (prfExpand rivkExt ([Sep.rivkInt] ++ i2leosp 256 ak.val ++ i2leosp 256 nk.val))

/-! ## The `ask` sign normalisation

`SpendAuthSig^Orchard` public keys are stored as `ak`, a single `𝔽_{q_P}` element,
so the `ỹ` bit of `ak^ℙ` is not recoverable from `ak`. The specification pins it
by normalising `ask`: if `repr_ℙ([ask] 𝒢)` has its top bit set, negate `ask`.

ZIP 2005's key-binding analysis notes that the predicate deliberately does *not*
constrain that sign, accepting a factor-2 concrete-security loss in exchange for
`ak` being one field element.
-/

/-- `ask` after the `ỹ`-bit normalisation of § 4.2.3: negated when
`repr_ℙ([ask] 𝒢^Orchard)`'s last bit is 1. -/
def askNormalised (sk : List UInt8) : Fq :=
  let ask := hAsk sk
  if ytilde (spendAuthDerivePublic ask) = 1 then -ask else ask

/-! ## The derivation procedure (§ 4.2.3, normative)

The ZIP states this as pseudocode with a `use_qsk` branch. The `use_qsk = true`
branch is deliberately non-constructive — `ak^ℙ` is obtained "by any suitably
secure method", either direct generation or a FROST distributed key generation —
so the faithful rendering is a *relation* on `(sk, use_qsk, ak^ℙ)` and the derived
components, not a function.
-/

/-- The key components § 4.2.3 derives. `qsk` and `qk` are `⊥` on the classical
branch, which is what the `Option`s encode. -/
structure Components where
  /-- `ak = Extract_ℙ(ak^ℙ) ⦂ {1..q_P−1}`. -/
  ak : Fp
  /-- `nk ⦂ 𝔽_{q_P}`. -/
  nk : Fp
  /-- `qsk ⦂ 𝔹^𝕐[ℓ_qsk/8] ∪ {⊥}`. -/
  qsk : Option (List UInt8)
  /-- `qk ⦂ 𝔹^𝕐[ℓ_qk/8] ∪ {⊥}`. -/
  qk : Option (List UInt8)
  /-- `rivk ⦂ 𝔽_{r_P}`. On the classical branch this is `rivk_ext`. -/
  rivk : Fq

/-- § 4.2.3's normative derivation, as a relation between a spending key, the
`use_qsk` flag, a spend-authorisation public key and the derived components.

Both branches guarantee `ỹ(ak^ℙ) = 0`: the quantum branch by fiat ("ensures the
last bit of `repr_ℙ(ak^ℙ)` is 0") and the classical branch by construction, via
`askNormalised`. Stating it once, outside the branch, records that they agree —
which is what makes `ak` alone a faithful representation of `ak^ℙ`.

Note that `ak = Extract_ℙ(ak^ℙ)` is stated against the *unnormalised* `ak^ℙ` in
the ZIP's classical branch, which is harmless: `Extract_ℙ` is the `x`-coordinate,
and negation does not move it. -/
def DerivesComponents (b3 : Blake3DeriveKey) (sk : List UInt8) (useQsk : Bool)
    (akP : Point Fp) (c : Components) : Prop :=
  akP.OnCurve ∧
  ytilde akP = 0 ∧
  c.nk = hNk sk ∧
  c.ak = extractP akP ∧
  if useQsk then
      c.qsk = some (hQsk sk)
    ∧ c.qk = some (hQk b3 (hQsk sk))
    ∧ c.rivk = hRivkExtQk (hQk b3 (hQsk sk)) c.ak c.nk
  else
      akP = spendAuthDerivePublic (askNormalised sk)
    ∧ c.qsk = none
    ∧ c.qk = none
    ∧ c.rivk = hRivk sk

/-- On the classical branch, `qsk` and `qk` are both `⊥` — "there are no quantum
spending/intermediate keys in this case". -/
theorem qsk_qk_bot_of_not_useQsk {b3 : Blake3DeriveKey} {sk : List UInt8}
    {akP : Point Fp} {c : Components}
    (h : DerivesComponents b3 sk false akP c) : c.qsk = none ∧ c.qk = none := by
  obtain ⟨-, -, -, -, h⟩ := h
  simp only [if_false, Bool.false_eq_true] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-- On the quantum branch, neither is: `qsk` and `qk` are both present, and
`qk = H^qk(qsk)`. -/
theorem qk_eq_hQk_qsk_of_useQsk {b3 : Blake3DeriveKey} {sk : List UInt8}
    {akP : Point Fp} {c : Components}
    (h : DerivesComponents b3 sk true akP c) :
    c.qsk = some (hQsk sk) ∧ c.qk = some (hQk b3 (hQsk sk)) := by
  obtain ⟨-, -, -, -, h⟩ := h
  simp only [if_true] at h
  exact ⟨h.1, h.2.1⟩

/-- Either way, `ak^ℙ` has a cleared sign bit — the invariant that lets the
protocol store `ak` as a single base-field element. -/
theorem ytilde_akP_eq_zero {b3 : Blake3DeriveKey} {sk : List UInt8} {useQsk : Bool}
    {akP : Point Fp} {c : Components}
    (h : DerivesComponents b3 sk useQsk akP c) : ytilde akP = 0 := h.2.1

end Zip2005
