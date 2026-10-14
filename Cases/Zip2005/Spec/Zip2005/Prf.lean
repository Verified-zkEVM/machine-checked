import Cases.Zip2005.Spec.Zip2005.Blake2b

set_option autoImplicit false

/-!
# `PRF^expand`, `ToBase^Orchard` and `ToScalar^Orchard`

Protocol specification § 4.1.2 and § 4.2.3. ZIP 2005 does not change these; it
adds four new domain separators to `PRF^expand`'s first byte (`0x0A`, `0x0B`,
`0x0C`, `0x0D`) and builds all of its new derivations out of these three
functions.

`PRF^expand` is keyed by its *subscript*: the ZIP writes `PRF^expand_sk`,
`PRF^expand_qk`, `PRF^expand_rivk_ext` and `PRF^expand_rseed` for the same
function seeded differently. This is not BLAKE2b keying — the key material is
prepended to the message and BLAKE2b's `kk` stays `0` — which is why
`Zip2005.Blake2b.blake2b` deliberately offers no key parameter.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq)
open Zip2005.Blake2b (blake2b512)

/-- `PRF^expand_sk(t) := BLAKE2b-512("Zcash_ExpandSeed", sk ‖ t)`
(protocol specification § 4.1.2).

The seed is prepended to the message, not used as a BLAKE2b key. Output is 64
bytes, `ℓ_PRFexpand = 512` bits. -/
def prfExpand (seed : List UInt8) (t : List UInt8) : List UInt8 :=
  blake2b512 prfExpandPersonalisation (seed ++ t)

@[simp] theorem prfExpand_length (seed t : List UInt8) :
    (prfExpand seed t).length = 64 :=
  Blake2b.blake2b512_length _ _

/-- `ToBase^Orchard(x) := LEOS2IP_{ℓ_PRFexpand}(x) (mod q_P)`
(protocol specification § 4.2.3). Wide reduction of a 64-byte string into the
Pallas base field. -/
def toBaseOrchard (x : List UInt8) : Fp := (leos2ip x : Fp)

/-- `ToScalar^Orchard(x) := LEOS2IP_{ℓ_PRFexpand}(x) (mod r_P)`
(protocol specification § 4.2.3). Wide reduction of a 64-byte string into the
Pallas scalar field. -/
def toScalarOrchard (x : List UInt8) : Fq := (leos2ip x : Fq)

/-- `mod_{r_P}` on a base-field element: reinterpret an `𝔽_{q_P}` element as an
`𝔽_{r_P}` element through its integer value.

Well-defined without reduction because `q_P < r_P`; the ZIP relies on this where
`DeriveNullifier` takes `(PRF^nf_nk(ρ) + ψ) mod q_P` as a scalar, and where
`pk_d = [ivk] g_d` uses a base-field `ivk` as a scalar. The SP1 guest carries its
own `WARNING` comment at this step (`zip-2005/program/src/main.rs`); the
inequality is what makes it sound. -/
def modRP (x : Fp) : Fq := (x.val : Fq)

/-- `q_P < r_P`, which is what makes `modRP` injective rather than a reduction.
Decided on the two literals, so it is a kernel fact and not a comment. -/
theorem qP_lt_rP : qP < rP := by decide

/-! ## Conformance

These are the checks the `Zip2005.Blake2b` module docstring defers to: the
*personalised*, *multi-byte-seed* path of `PRF^expand`, against vectors from
outside this tree. Getting the personalisation, the seed-prepend order, the
domain separator or the field order wrong fails them.

`H^ask`, `H^nk` and `H^rivk` themselves live in `Zip2005.KeyComponents`; what is
pinned here is the `PRF^expand`/`ToBase`/`ToScalar` sandwich they are built from,
using vector 0's `sk`.
-/

section Conformance

/-- Vector 0's spending key, `sk`, from `zip-2005/testdata/orchard_key_components.json`. -/
private def sk0 : List UInt8 :=
  i2leosp 256 0x482169eef62efaaf9d9364b1666e4d4c299e04a852e10c5b949e2d9a738f7a5d

-- `ToScalar^Orchard(PRF^expand_sk([0x06]))` is vector 0's `ask`.
#guard i2leosp 256 (toScalarOrchard (prfExpand sk0 [Sep.ask])).val
        == i2leosp 256 0x171ce6f430f6142d60db253585a8e46bd87221d85a342c3ac1a687c201c4b88e

-- `ToBase^Orchard(PRF^expand_sk([0x07]))` is vector 0's `nk`.
#guard i2leosp 256 (toBaseOrchard (prfExpand sk0 [Sep.nk])).val
        == i2leosp 256 0x1bfdfe68a9de398c948355ff610cc246c267c3b00df7471fd05a943867822f9f

-- `ToScalar^Orchard(PRF^expand_sk([0x08]))` is vector 0's `rivk`.
#guard i2leosp 256 (toScalarOrchard (prfExpand sk0 [Sep.rivk])).val
        == i2leosp 256 0x3de4a771cab4568b45e6fe25e3fb19b80889332db334e0c67c5f4f6089cf1c02

-- The seed really is prepended, not appended: swapping the order changes the answer.
#guard prfExpand sk0 [Sep.ask] != prfExpand [Sep.ask] sk0

-- The personalisation really is applied: dropping it changes the answer.
#guard prfExpand sk0 [Sep.ask] != Blake2b.blake2b512 [] (sk0 ++ [Sep.ask])

end Conformance

end Zip2005
