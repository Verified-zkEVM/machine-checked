import Cases.Zip2005.Spec.Zip2005.Divergences

/-!
# The guest's input, decoded

`main` reads its input with `sp1_zkvm::io::read` twice. Each record on the private-input
stream is a little-endian `u64` length and then that many bytes: bincode of
`Zip2005Instance`, then of `Zip2005Witness` (`zip-2005/lib/src/lib.rs`).

This file states what it means for the stream to decode to the typed values
`Zip2005.GuestStatement` takes. It is stated over the input bytes and the spec's types
only and names nothing of the machine. The top-level theorem's conclusion is
`∃ …, Decodes I … ∧ GuestStatement …`.

**Layouts.** The instance is four `Bytes32`: `anchor`, `rk`, `nf`, `sighash`. The witness
starts with `sk: Option<Bytes32>` (tag byte `1` and 32 bytes, or tag `0` alone). Then come
`alpha`, `ak`, `nk`, `rivk_ext`, `rivk`, `g_d`, `rho`, `rseed` (each `Bytes32`),
`value: u64`, `merkle_position: u32` and `auth_path: [Bytes32; 32]`. After those are
`qk`, `sigma_qsk: Option<Bytes32>` and `negate: bool`.

**Decoding.** A scalar or base-field element decodes from its 32 bytes when it is their
little-endian integer, so the encoding is canonical. A point decodes when its `repr_P` is
the bytes. `Decodes` fixes `sk` as present, because every accepting run has it: with `sk`
absent the guest either fails `authorization_is_well_formed` or reaches
`unimplemented!()`. The anchor's bytes are read modulo `q_P`, because the guest never
parses the anchor. `GuestStatement` does not mention the anchor.
-/

namespace Cases.Zip2005.Top

open Zcash.Circuits (Fp Fq Point)
open _root_.Zip2005 (leos2ip reprPNat PrimaryInput)

set_option autoImplicit false

/-- The private input as bytes. -/
def inBytes (I : List (BitVec 8)) : List UInt8 := I.map UInt8.ofBitVec

/-- The first length-prefixed record of a stream, and the stream after it. -/
def record (S : List UInt8) : List UInt8 × List UInt8 :=
  ((S.drop 8).take (leos2ip (S.take 8)), S.drop (8 + leos2ip (S.take 8)))

/-- The instance record. -/
def instRec (I : List (BitVec 8)) : List UInt8 := (record (inBytes I)).1

/-- The witness record. -/
def witRec (I : List (BitVec 8)) : List UInt8 := (record (record (inBytes I)).2).1

/-- `n` bytes at offset `o`. -/
def field (r : List UInt8) (o n : ℕ) : List UInt8 := (r.drop o).take n

/-- The size of an `Option<Bytes32>` with tag byte `t`. -/
def optSize (t : UInt8) : ℕ := if t = 1 then 33 else 1

/-- Offset of `negate` in a witness record whose `sk` is present: after `qk` (tag at 1325)
and `sigma_qsk`. -/
def negOff (w : List UInt8) : ℕ :=
  1325 + optSize w[1325]! + optSize w[1325 + optSize w[1325]!]!

/-- The input stream `I` decodes to the guest's typed inputs. -/
structure Decodes (I : List (BitVec 8)) (pi : PrimaryInput) (negate : Bool) (sk : List UInt8)
    (α : Fq) (akP : Point Fp) (nk : Fp) (rivkExt rivk : Fq) (rseed : List UInt8)
    (gd : Point Fp) (v : ℕ) (ρ : Fp) : Prop where
  inst_len : 128 ≤ (instRec I).length
  anchor : pi.rtOrchard = ((leos2ip (field (instRec I) 0 32) : ℕ) : Fp)
  rk : pi.rk.Valid ∧ reprPNat pi.rk = leos2ip (field (instRec I) 32 32)
  nf : pi.nf.val = leos2ip (field (instRec I) 64 32)
  sighash : pi.sighash = field (instRec I) 96 32
  sk_tag : (witRec I)[0]! = 1
  sk : sk = field (witRec I) 1 32
  alpha : α.val = leos2ip (field (witRec I) 33 32)
  ak : akP.Valid ∧ reprPNat akP = leos2ip (field (witRec I) 65 32)
  nk : nk.val = leos2ip (field (witRec I) 97 32)
  rivk_ext : rivkExt.val = leos2ip (field (witRec I) 129 32)
  rivk : rivk.val = leos2ip (field (witRec I) 161 32)
  gd : gd.Valid ∧ reprPNat gd = leos2ip (field (witRec I) 193 32)
  rho : ρ.val = leos2ip (field (witRec I) 225 32)
  rseed : rseed = field (witRec I) 257 32
  value : v = leos2ip (field (witRec I) 289 8)
  negate_byte : (witRec I)[negOff (witRec I)]!.toNat < 2
  negate : negate = ((witRec I)[negOff (witRec I)]! == 1)
  wit_len : negOff (witRec I) + 1 ≤ (witRec I).length

/-- What an accepting run establishes about its input `I`. -/
def GuestAccepts (I : List (BitVec 8)) : Prop :=
  ∃ (pi : PrimaryInput) (negate : Bool) (sk : List UInt8) (α : Fq) (akP : Point Fp) (nk : Fp)
    (rivkExt rivk : Fq) (rseed : List UInt8) (gd : Point Fp) (v : ℕ) (ρ : Fp),
    Decodes I pi negate sk α akP nk rivkExt rivk rseed gd v ρ ∧
    Zip2005.GuestStatement pi negate sk α akP nk rivkExt rivk rseed gd v ρ

end Cases.Zip2005.Top
