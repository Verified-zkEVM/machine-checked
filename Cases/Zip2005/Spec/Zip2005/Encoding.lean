import Cases.Zip2005.Spec.Zip2005.Constants
import Cases.Zip2005.Spec.CompElliptic.Encodings.Pasta

set_option autoImplicit false

/-!
# Integer, bit-string and byte-string encodings (protocol specification § 5.2)

ZIP 2005's new derivations are byte-oriented: `pre_rcm` is a 137-byte string, and
`H^rivk_ext_qk` hashes `[0x0D] ‖ I2LEOSP_256(ak) ‖ I2LEOSP_256(nk)`. The imported
`zcash/ironwood` layer is bit- and `ℕ`-oriented, because a circuit never handles
bytes. This module is the bridge.

## Relation to `CompElliptic`

`CompElliptic.I2LEOSP` and `CompElliptic.LEOS2IP` already exist, and
`CompElliptic.Encodings.Pasta.toBytes` gives the compressed point encoding. The
definitions here differ from them in exactly one respect: dependent typing.
`CompElliptic.I2LEOSP` takes `Fin (2^ℓ)` and returns `Vector UInt8 ((ℓ+7)/8)`,
which is right for a library that wants the encoding to be a bijection onto its
image — but every call site in a ZIP transcription would then thread a bound proof
through a hash-input concatenation. The versions here are total on `ℕ` and return
`List UInt8`, truncating above `2^ℓ`.

They are also structurally recursive rather than `List.range`-based, so that
induction on the length is available to later proofs.

`reprPNat` is exactly the integer `P.x.val + (P.y.val % 2) * 2^255` that
`CompElliptic.Encodings.Pasta.toBytes` encodes; the `#guard`s at the end of this
file check our `repr_ℙ` against the byte string `CompElliptic`'s own `toBytes`
test pins for the Pallas test point.

## What is *not* here, and why

The **decode** direction (`abst`: range-check `x`, Tonelli–Shanks for `y`, match
the `ỹ` parity) is absent, and that is not an omission. ZIP 2005's Recovery
Statement types its auxiliary input as group and field elements — `ak^ℙ ⦂ ℙ*`,
`g_d ⦂ ℙ*`, `nk ⦂ 𝔽_{q_P}` — never as byte strings. Encodings appear only *inside*
hash preimages, that is, only ever in the encode direction. Decoding is a property
of an implementation that reads serialised witnesses (as the SP1 guest does, on
~40 fields), not of the statement, and it belongs to the phase that relates the
guest to this spec. `CompElliptic` records `abst` as its own open TODO.

`LEBS2OSP` and `I2LEBSP` are likewise flagged as unwritten in `CompElliptic`,
which cites the Sapling testnet bit-ordering bug as the motivating mistake class.
They are defined here because ZIP 2005 § 4.7.3 writes `pre_rcm` in terms of them.

Roundtrip lemmas (`lebs2ip (i2lebsp ℓ n) = n % 2^ℓ` and its byte analogue) are
deliberately *not* stated yet. The `#guard`s below are what actually catch a
wrong encoding, and they are the repo's established posture; the algebraic
roundtrip is worth proving when something needs to consume it.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq Point)

/-! ## Integers to and from little-endian byte strings -/

/-- `k` little-endian bytes of `n`. The engine of `i2leosp`, separated out so the
recursion is on the byte count. -/
def i2leospAux : ℕ → ℕ → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: i2leospAux k (n / 256)

/-- `I2LEOSP_ℓ(n)`: the little-endian byte encoding of `n` in `⌈ℓ/8⌉ = (ℓ+7)/8`
bytes (§ 5.2). Total on `ℕ`, truncating modulo `256^⌈ℓ/8⌉`. -/
def i2leosp (ℓ : ℕ) (n : ℕ) : List UInt8 := i2leospAux ((ℓ + 7) / 8) n

/-- `LEOS2IP(S)`: the integer the byte string `S` represents in little-endian byte
order (§ 5.2). -/
def leos2ip (S : List UInt8) : ℕ :=
  S.foldr (fun b acc => b.toNat + 256 * acc) 0

@[simp] theorem i2leospAux_length (k n : ℕ) : (i2leospAux k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [i2leospAux, ih]

@[simp] theorem i2leosp_length (ℓ n : ℕ) : (i2leosp ℓ n).length = (ℓ + 7) / 8 := by
  simp [i2leosp]

@[simp] theorem leos2ip_nil : leos2ip [] = 0 := rfl

@[simp] theorem leos2ip_cons (b : UInt8) (S : List UInt8) :
    leos2ip (b :: S) = b.toNat + 256 * leos2ip S := rfl

/-- `LEOS2IP` is additive over concatenation, with the high half shifted past the
low half's byte length. This is the property a preimage assembled by concatenation
actually needs, and the reason `pre_rcm`'s field widths matter. -/
theorem leos2ip_append (S T : List UInt8) :
    leos2ip (S ++ T) = leos2ip S + 256 ^ S.length * leos2ip T := by
  induction S with
  | nil => simp
  | cons b S ih =>
    simp only [List.cons_append, leos2ip_cons, ih, List.length_cons, pow_succ]
    ring

/-! ## Integers to and from little-endian bit strings -/

/-- `I2LEBSP_ℓ(n)`: the `ℓ`-bit little-endian bit encoding of `n` (§ 5.2). -/
def i2lebsp : ℕ → ℕ → List Bool
  | 0, _ => []
  | ℓ + 1, n => (n % 2 == 1) :: i2lebsp ℓ (n / 2)

/-- `LEBS2IP(B)`: the integer a little-endian bit string represents (§ 5.2). -/
def lebs2ip (B : List Bool) : ℕ :=
  B.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0

@[simp] theorem i2lebsp_length (ℓ n : ℕ) : (i2lebsp ℓ n).length = ℓ := by
  induction ℓ generalizing n with
  | zero => rfl
  | succ ℓ ih => simp [i2lebsp, ih]

/-- `LEBS2OSP_ℓ(B)`: repack a little-endian bit string as a little-endian byte
string (§ 5.2). The ZIP applies this only at `ℓ = 256`, a multiple of 8, so no
partial trailing byte arises; the definition handles it anyway by routing through
the integer. -/
def lebs2osp (B : List Bool) : List UInt8 :=
  i2leosp B.length (lebs2ip B)

/-! ## `truncate` (§ 4.2.3) -/

/-- `truncate_k(S)`: the first `k` bytes of `S`. ZIP 2005 uses `truncate_32` to cut
the 64-byte `PRF^expand` output down to a 32-byte `qsk`. -/
def truncate (k : ℕ) (S : List UInt8) : List UInt8 := S.take k

/-! ## `Extract_ℙ` and `repr_ℙ` (§ 5.4.9.7, § 5.4.9.8)

`Extract_ℙ` is the `x`-coordinate, with the identity mapped to zero. In the
imported point vocabulary the identity is encoded as `(0, 0)`, and no Pallas point
has `x = 0` (`Zcash.Circuits.Point.no_onCurve_of_x_zero`), so the projection `.x`
*is* `Extract_ℙ` — which is why `Zcash.Circuits.Specs.Sinsemilla.hash` uses it
directly. Naming it here keeps the ZIP's spelling available.
-/

/-- `Extract_ℙ(P)`: the `x`-coordinate of a Pallas point, identity ↦ `0` (§ 5.4.9.7). -/
def extractP (P : Point Fp) : Fp := P.x

/-- `ỹ(P)`, the sign bit of a Pallas point: the low bit of `y`. This occupies the
free top bit of the compressed encoding, `q_P` being below `2^255`. -/
def ytilde (P : Point Fp) : ℕ := P.y.val % 2

/-- The integer underlying `repr_ℙ(P)`: the `x`-coordinate with `ỹ` in bit 255.
This is exactly the integer `CompElliptic.Encodings.Pasta.toBytes` encodes. -/
def reprPNat (P : Point Fp) : ℕ := P.x.val + ytilde P * 2 ^ 255

/-- `repr_ℙ(P) ⦂ 𝔹^[256]`: the compressed *bit* encoding of a Pallas point
(§ 5.4.9.8). The ZIP writes this `P★`, and § 4.7.3 feeds it to `LEBS2OSP_256`. -/
def reprPBits (P : Point Fp) : List Bool := i2lebsp 256 (reprPNat P)

/-- `LEBS2OSP_256(repr_ℙ(P))`: the 32-byte compressed encoding, as it appears in
`pre_rcm` (§ 4.7.3). Written through `lebs2osp ∘ reprPBits` rather than straight to
bytes, so the spelling matches the ZIP's. -/
def reprP (P : Point Fp) : List UInt8 := lebs2osp (reprPBits P)

@[simp] theorem reprP_length (P : Point Fp) : (reprP P).length = 32 := by
  simp [reprP, lebs2osp, reprPBits]

/-! ## Encoding checks

The `#guard`s are the real defence against a wrong bit or byte order. `#guard`
evaluates at elaboration time and emits no proof term, so unlike `native_decide`
it adds nothing to the axiom base — the posture `Zip2005Asm.lean` already takes.
-/

-- Byte order: `I2LEOSP` is little-endian, low byte first.
#guard i2leosp 64 1 == [1, 0, 0, 0, 0, 0, 0, 0]
#guard i2leosp 64 0x0102030405060708
        == [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
#guard (i2leosp 256 0).length == 32
#guard leos2ip (i2leosp 64 0x0102030405060708) == 0x0102030405060708

-- Bit order: `I2LEBSP` is little-endian, low bit first.
#guard i2lebsp 8 1 == [true, false, false, false, false, false, false, false]
#guard i2lebsp 8 0x80 == [false, false, false, false, false, false, false, true]
#guard lebs2ip (i2lebsp 16 0xBEEF) == 0xBEEF

-- `LEBS2OSP` repacks bits to bytes without reordering.
#guard lebs2osp (i2lebsp 16 0xBEEF) == [0xEF, 0xBE]

-- `truncate_32` of a 64-byte string keeps the low 32.
#guard (truncate 32 (i2leosp 512 1)).length == 32
#guard truncate 32 (i2leosp 512 1) == i2leosp 256 1


/-- The Pallas test point `(-1, 2)` in the imported point vocabulary. `CompElliptic`
pins `toBytes` on the same point as an `SWPoint`, so this is a cross-library check
that our `repr_ℙ` -- bits first, then repacked -- agrees with `CompElliptic`'s
direct-to-bytes compressed encoding. `y = 2` is even, so `ỹ = 0` and the top bit
is clear; the trailing `0x40` is `q_P`'s top byte. -/
def testPointG : Point Fp := { x := -1, y := 2 }

#guard reprP testPointG
        == [0, 0, 0, 0, 237, 48, 45, 153, 27, 249, 76, 9, 252, 152, 70, 34,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64]

-- `ỹ = 0` for an even `y`, so `repr_ℙ` is just `I2LEOSP_256` of the x-coordinate.
#guard ytilde testPointG == 0
#guard reprP testPointG == i2leosp 256 (extractP testPointG).val

end Zip2005
