import Cases.Zip2005.Spec.Zcash.Circuits.Specs.Pallas

set_option autoImplicit false

/-!
# Constants

ZIP 2005 § 'Changes to the Protocol Specification' adds two constants to
protocol specification § 5.3 'Constants':

```
ℓ_qsk ⦂ ℕ := 256
ℓ_qk  ⦂ ℕ := 256
```

Everything else here is *imported* by ZIP 2005 rather than defined by it, and is
restated so that the transcription of the ZIP reads in the ZIP's own vocabulary.
Each carries the protocol-specification section it comes from.

The field cardinalities `q_P` and `r_P` are taken from `CompElliptic`, where each
has a Lucas/Pratt primality certificate, rather than restated as literals: the
point of naming them here is to fix the ZIP's notation onto the reviewed
definition, not to introduce a second copy of a 255-bit number.

Reference: <https://zips.z.cash/zip-2005>
-/

namespace Zip2005

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)

/-! ## § 5.3 Constants — added by ZIP 2005 -/

/-- `ℓ_qsk`, the bit length of a quantum spending key. Added to § 5.3 by ZIP 2005. -/
def ellQsk : ℕ := 256

/-- `ℓ_qk`, the bit length of a quantum intermediate key. Added to § 5.3 by ZIP 2005. -/
def ellQk : ℕ := 256

/-- The byte length of a quantum spending key, `ℓ_qsk / 8`. The ZIP types `qsk` as
`𝔹^𝕐[ℓ_qsk/8] ∪ {⊥}`, i.e. as *bytes*. -/
def qskBytes : ℕ := ellQsk / 8

/-- The byte length of a quantum intermediate key, `ℓ_qk / 8`. -/
def qkBytes : ℕ := ellQk / 8

/-- ZIP 2005's cost analysis requires `ℓ_qk ≤ 504` so that
`qk ‖ [0x0D] ‖ ak ‖ nk` fits in a single 128-byte BLAKE2b block, making
`H^rivk_ext_qk` one compression rather than two. At `ℓ_qk = 256` it does. -/
theorem ellQk_single_block : ellQk ≤ 504 := by decide

/-! ## § 5.3 Constants — imported -/

/-- `ℓ_sk = 256`, the bit length of an Orchard spending key (§ 5.3). Note the ZIP
types `SoK^sk`'s domain as `𝔹^[ℓ_sk]`, i.e. as *bits*, where `SoK^qsk` uses bytes;
see `Zip2005.Recovery`. -/
def ellSk : ℕ := 256

/-- `ℓ_value = 64`, the bit length of a note value (§ 5.3). -/
def ellValue : ℕ := 64

/-- `ℓ^Orchard_base = 255`, the bit length used for `I2LEBSP` of a Pallas base-field
element in Sinsemilla messages (§ 5.3). -/
def ellOrchardBase : ℕ := 255

/-- `ℓ_PRFexpand = 512`, the output bit length of `PRF^expand` (§ 5.3). BLAKE2b-512. -/
def ellPRFexpand : ℕ := 512

/-- `MerkleDepth^Orchard = 32` (§ 5.3). Agrees with `Zcash.Circuits.Specs.merkleDepth`. -/
def merkleDepthOrchard : ℕ := 32

/-- `q_P`, the order of the Pallas base field. -/
abbrev qP : ℕ := PALLAS_BASE_CARD

/-- `r_P`, the order of the Pallas scalar field (the group order of `ℙ`). -/
abbrev rP : ℕ := PALLAS_SCALAR_CARD

/-! ## `PRF^expand` domain separators

Protocol specification § 4.1.2 keys `PRF^expand` by a leading byte. ZIP 2005 adds
`0x0C` and `0x0D` (§ 4.2.3) and `0x0A`, `0x0B` (§ 4.7.3), and states that `0x0A`
is **reserved** for ZIP 226 split notes rather than used here.
-/

namespace Sep

/-- `[0x06]` — `H^ask` (§ 4.2.3). -/
def ask : UInt8 := 0x06
/-- `[0x07]` — `H^nk` (§ 4.2.3). -/
def nk : UInt8 := 0x07
/-- `[0x08]` — `H^rivk`, also written `H^rivk_legacy` in the Recovery Statement
(§ 4.2.3). -/
def rivk : UInt8 := 0x08
/-- `[0x0C]` — `H^qsk`. **Added by ZIP 2005** (§ 4.2.3). -/
def qsk : UInt8 := 0x0C
/-- `[0x0D]` — `H^rivk_ext_qk`. **Added by ZIP 2005** (§ 4.2.3). -/
def rivkExtQk : UInt8 := 0x0D
/-- `[0x83]` — `H^rivk_int`, the Orchard internal `rivk` separator. Defined by
ZIP 32 and imported by ZIP 2005's Recovery Statement. -/
def rivkInt : UInt8 := 0x83
/-- `[0x04]` — `H^{esk,Orchard}` (§ 4.7.3). Note Sapling swaps `0x04`/`0x05`:
there `0x04` is `rcm` and `0x05` is `esk` (§ 4.7.2). -/
def eskOrchard : UInt8 := 0x04
/-- `[0x05]` — the ZIP 212 (lead byte `0x02`) Orchard `rcm` (§ 4.7.3). -/
def rcmV2Orchard : UInt8 := 0x05
/-- `[0x09]` — `H^{ψ,Orchard}` (§ 4.7.3). -/
def psiOrchard : UInt8 := 0x09
/-- `[0x0A]` — **reserved by ZIP 2005** for ZIP 226 split notes. Not used here;
named so that the reservation is visible rather than an unexplained gap. -/
def reservedSplitNotes : UInt8 := 0x0A
/-- `[0x0B]` — `H^{rcm,Orchard}`, the quantum-recoverable `rcm`.
**Added by ZIP 2005** (§ 4.7.3), and the heart of the change. -/
def rcmOrchard : UInt8 := 0x0B
/-- `[0x04]` — the ZIP 212 Sapling `rcm` (§ 4.7.2). -/
def rcmV2Sapling : UInt8 := 0x04
/-- `[0x05]` — `H^{esk,Sapling}` (§ 4.7.2). -/
def eskSapling : UInt8 := 0x05

end Sep

/-- The BLAKE2b personalisation of `PRF^expand` (§ 4.1.2), as its 16 bytes.
`"Zcash_ExpandSeed"` is exactly 16 bytes, which is BLAKE2b's personalisation
field width, so no padding is involved. -/
def prfExpandPersonalisation : List UInt8 :=
  "Zcash_ExpandSeed".toList.map (fun c => UInt8.ofNat c.toNat)

@[simp] theorem prfExpandPersonalisation_length :
    prfExpandPersonalisation.length = 16 := by decide

/-- The BLAKE3 `derive_key` context string of `H^qk` (§ 4.2.3), verbatim. -/
def qkDerivationContext : String := "Zcash ZIP 2005 qk-derivation v1"

end Zip2005
