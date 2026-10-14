import Cases.Zip2005.Spec.Zip2005.KeyComponents

set_option autoImplicit false

/-!
# § 4.7.2 and § 4.7.3 Sending Notes

This is where ZIP 2005 does its work. `H^{rcm,Orchard}` binds `rcm` to *every*
field of the note rather than to `ρ` alone, so that a future Recovery Protocol
can enforce the derivation in-circuit and thereby make the note commitment
binding on the whole note tuple even against a discrete-log-breaking adversary.

Two structural consequences, both stated by the ZIP:

* the derivation **order** changes to `esk`, then `ψ`, then `rcm`, because
  `Derive_rcm` now consumes `ψ`;
* `pre_rcm` is 137 bytes, so with the 32-byte seed the hash takes **two** BLAKE2b
  blocks where the old one took one. `preRcm_length` pins the first half of that
  claim.

Reference: <https://zips.z.cash/zip-2005>, § 'Changes to the Protocol
Specification' → § 4.7.2, § 4.7.3.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq Point)

/-! ## Encoded field elements

The ZIP writes `ρ̲` for the byte encoding of `ρ` and `ψ` for a base-field element
that `pre_rcm` includes as `I2LEOSP_256(ψ)`. Both are 32 bytes.
-/

/-- `ρ̲ = I2LEOSP_256(ρ)`, the byte encoding the ZIP underlines. -/
def rhoBytes (ρ : Fp) : List UInt8 := i2leosp 256 ρ.val

@[simp] theorem rhoBytes_length (ρ : Fp) : (rhoBytes ρ).length = 32 := by
  simp [rhoBytes]

/-! ## § 4.7.3 Sending Notes (Orchard) -/

/-- `H^{ψ,Orchard}_rseed(ρ̲) = ToBase^Orchard(PRF^expand_rseed([0x09] ‖ ρ̲))`. -/
def hPsiOrchard (rseed : List UInt8) (ρ : Fp) : Fp :=
  toBaseOrchard (prfExpand rseed ([Sep.psiOrchard] ++ rhoBytes ρ))

/-- `H^{esk,Orchard}_rseed(ρ̲) = ToScalar^Orchard(PRF^expand_rseed([0x04] ‖ ρ̲))`.

Note the separator: Orchard uses `0x04` for `esk` and `0x05` for the ZIP 212
`rcm`, where Sapling uses them the other way round (§ 4.7.2). The swap is exactly
the sort of detail a transcription exists to pin down. -/
def hEskOrchard (rseed : List UInt8) (ρ : Fp) : Fq :=
  toScalarOrchard (prfExpand rseed ([Sep.eskOrchard] ++ rhoBytes ρ))

/-- `pre_rcm = [0x0B] ‖ LEBS2OSP_256(g★_d) ‖ LEBS2OSP_256(pk★_d) ‖ I2LEOSP_64(v)
‖ ρ̲ ‖ I2LEOSP_256(ψ)`.

**Introduced by ZIP 2005.** `1 + 32 + 32 + 8 + 32 + 32 = 137` bytes. Split out
from `hRcmOrchard` because the preimage is where a transcription can go wrong in
ways no type will catch: a separator, a field order, an encoding length, or the
order of `g★_d` and `pk★_d`. -/
def preRcm (gd pkd : Point Fp) (v : ℕ) (ρ ψ : Fp) : List UInt8 :=
  [Sep.rcmOrchard] ++ reprP gd ++ reprP pkd ++ i2leosp 64 v ++ rhoBytes ρ
    ++ i2leosp 256 ψ.val

/-- `pre_rcm` is 137 bytes, as the ZIP's cost analysis asserts when it concludes
that `H^rcm` needs two BLAKE2b compressions. -/
@[simp] theorem preRcm_length (gd pkd : Point Fp) (v : ℕ) (ρ ψ : Fp) :
    (preRcm gd pkd v ρ ψ).length = 137 := by
  simp [preRcm, rhoBytes]

/-- With the 32-byte `rseed` prepended by `PRF^expand`, the hashed message is 169
bytes and so spans two 128-byte BLAKE2b blocks — the cost the ZIP accounts for. -/
theorem preRcm_two_blocks (gd pkd : Point Fp) (v : ℕ) (ρ ψ : Fp)
    (rseed : List UInt8) (hseed : rseed.length = 32) :
    Blake2b.blockCount (rseed ++ preRcm gd pkd v ρ ψ).length = 2 := by
  simp [Blake2b.blockCount, Blake2b.blockBytes, hseed]

/-- `H^{rcm,Orchard}_rseed(g★_d, pk★_d, v, ρ̲, ψ)
= ToScalar^Orchard(PRF^expand_rseed(pre_rcm))`.

**The derivation ZIP 2005 exists to introduce.**

Note the signature: § 4.7.3 defines this with five positional arguments and *no*
leadByte — the leadByte lives in `Derive_rcm`, and `0x0B` is already baked into
`pre_rcm`. The Recovery Statement writes it as
`H^{rcm,Orchard}_rseed(0x03, noterepr)` and the Rationale as
`H^rcm_rseed(noterepr)`; all three are the same function, and § 4.7.3 is the
normative spelling. See `Zip2005.Divergences`. -/
def hRcmOrchard (rseed : List UInt8) (gd pkd : Point Fp) (v : ℕ) (ρ ψ : Fp) : Fq :=
  toScalarOrchard (prfExpand rseed (preRcm gd pkd v ρ ψ))

/-- `Derive_rcm^Orchard_rseed(leadByte, g★_d, pk★_d, v, ρ̲, ψ)` (§ 4.7.3).

`0x02` is the ZIP 212 derivation, which binds `rcm` to `ρ` alone; `0x03` is
ZIP 2005's, which binds it to the whole note. Any other lead byte is `⊥` — the
`allowedLeadBytes` of § 3.2.1 is what rules those out, and after the grace period
an Ironwood-pool note may only use `0x03`. -/
def deriveRcmOrchard (rseed : List UInt8) (leadByte : UInt8)
    (gd pkd : Point Fp) (v : ℕ) (ρ ψ : Fp) : Option Fq :=
  if leadByte = 0x02 then
    some (toScalarOrchard (prfExpand rseed ([Sep.rcmV2Orchard] ++ rhoBytes ρ)))
  else if leadByte = 0x03 then
    some (hRcmOrchard rseed gd pkd v ρ ψ)
  else
    none

/-- At the Ironwood-pool lead byte, `Derive_rcm` *is* ZIP 2005's `H^rcm`. -/
theorem deriveRcmOrchard_leadByte_three (rseed : List UInt8)
    (gd pkd : Point Fp) (v : ℕ) (ρ ψ : Fp) :
    deriveRcmOrchard rseed 0x03 gd pkd v ρ ψ = some (hRcmOrchard rseed gd pkd v ρ ψ) := by
  simp [deriveRcmOrchard]

/-- The two branches genuinely differ: the ZIP 212 derivation ignores
`g★_d`, `pk★_d`, `v` and `ψ`, which is precisely the binding weakness ZIP 2005
removes. Stated as the observation that its value does not depend on them. -/
theorem deriveRcmOrchard_leadByte_two_indep (rseed : List UInt8)
    (gd pkd gd' pkd' : Point Fp) (v v' : ℕ) (ρ ψ ψ' : Fp) :
    deriveRcmOrchard rseed 0x02 gd pkd v ρ ψ
      = deriveRcmOrchard rseed 0x02 gd' pkd' v' ρ ψ' := by
  simp [deriveRcmOrchard]

/-! ## § 4.7.2 Sending Notes (Sapling)

ZIP 2005 refactors Sapling's `rcm`/`esk` derivations into the same `Derive_rcm` /
`H^esk` shape, but deliberately gives Sapling **no** quantum recoverability:
Sapling funds are not recoverable and become permanently unspendable once the
protocol is switched off.

The Sapling scalar field is Jubjub's, which is not available — `CompElliptic`
defers Jubjub's Edwards and Montgomery forms — so `ToScalar^Sapling` and the
integer-to-scalar map are parameters. That keeps the section faithful (the
*preimages*, where mistakes live, are concrete) without pretending to a curve we
do not have.
-/

/-- `Derive_rcm^Sapling_rseed(leadByte)` (§ 4.7.2).

At lead byte `0x01` (pre-Canopy) `rcm` is the seed read directly as an integer;
at `0x02` it is a `PRF^expand` output under separator `[0x04]`. § 4.20 then
rejects the note if `rcm ≥ r_G`, which is why the `0x01` branch is an integer
reinterpretation rather than a reduction. -/
def deriveRcmSapling {S : Type} (toScalarSapling : List UInt8 → S)
    (intToScalar : ℕ → S) (rseed : List UInt8) (leadByte : UInt8) : Option S :=
  if leadByte = 0x01 then
    some (intToScalar (leos2ip rseed))
  else if leadByte = 0x02 then
    some (toScalarSapling (prfExpand rseed [Sep.rcmV2Sapling]))
  else
    none

/-- `H^{esk,Sapling}_rseed(_) = ToScalar^Sapling(PRF^expand_rseed([0x05]))`
(§ 4.7.2).

The unused argument is in the ZIP's signature — it exists so that Sapling and
Orchard `H^esk` have the same shape at the call sites in § 4.20 — and is retained
here for the same reason. -/
def hEskSapling {S : Type} (toScalarSapling : List UInt8 → S)
    (rseed : List UInt8) (_unused : Option Fp) : S :=
  toScalarSapling (prfExpand rseed [Sep.eskSapling])

/-- Sapling's separators are the mirror image of Orchard's: `0x04` is `rcm` here
and `esk` there, `0x05` is `esk` here and the ZIP 212 `rcm` there. Recorded as a
theorem so the swap cannot be quietly "fixed" into agreement. -/
theorem sapling_orchard_separators_swapped :
    Sep.rcmV2Sapling = Sep.eskOrchard ∧ Sep.eskSapling = Sep.rcmV2Orchard :=
  ⟨rfl, rfl⟩

end Zip2005
