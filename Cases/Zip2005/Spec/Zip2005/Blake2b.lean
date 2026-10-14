import Cases.Zip2005.Spec.Zip2005.Encoding

set_option autoImplicit false

/-!
# BLAKE2b-512 with personalisation (RFC 7693)

`PRF^expand` (protocol specification § 4.1.2) is BLAKE2b-512 personalised
`"Zcash_ExpandSeed"`, and every derivation ZIP 2005 adds or changes goes through
it. Nothing in the Lean ecosystem has BLAKE2b as a *hash*: `zcash/ironwood` has
none at all (its Action circuit takes `ψ`, `rcm` and `rivk` as witnesses — putting
their derivations into the statement is exactly what ZIP 2005 does), and
`CompElliptic`'s `Hashing/` is the SSWU map, not a hash front end.

## Provenance

The compression function — `IV`, `sigma`, `mixTable`, `rotr`, `G`, and the round
structure of `compress` — is ported from `Verified-zkEVM/evm-asm`,
`EvmAsm/Stateless/SpecRef/PrecompilesHash.lean` (MIT). That is this project's
methodological sibling: it also Lean-verifies compiled assembly against a spec,
it sits at the same Lean toolchain lineage, and its `Blake2b` is `#guard`-pinned
to the RFC 7693 Appendix A vector. Reusing it rather than re-deriving the
rotations keeps a reviewed `G` in the chain.

What is added here is everything above the compression function, which the EVM
`BLAKE2F` precompile does not need and so does not have:

* the **parameter block** (RFC 7693 § 2.8) — digest length, key length, fanout,
  depth, and critically the 16-byte **personalisation** at bytes 48..63, i.e.
  state words 6 and 7;
* **block splitting and zero padding** to 128 bytes, including the empty-message
  case, which is one all-zero block rather than none;
* the **counter and final-block flag** discipline of RFC 7693 § 3.3: `t` counts
  bytes compressed *including* the current block, and the last block alone is
  compressed with `f = true`.

## Shape

`compress` here returns the new chaining state as words, where evm-asm's returns
finalised bytes. They compute the same thing — `h'[i] = h[i] ^ v[i] ^ v[i+8]` is
both the chaining update and the finalisation — but words are what a multi-block
fold needs.

Reference: RFC 7693 <https://www.rfc-editor.org/rfc/rfc7693>; protocol
specification § 4.1.2.
-/

namespace Zip2005.Blake2b

/-! ## Constants (RFC 7693 § 2.6, § 2.7) -/

/-- `2^64`, the word modulus. -/
def M64 : ℕ := 2 ^ 64

/-- The BLAKE2b initialisation vector: the first 64 bits of the fractional parts
of the square roots of the first eight primes (RFC 7693 § 2.6). -/
def IV : List ℕ :=
  [0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B,
   0xA54FF53A5F1D36F1, 0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
   0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-- The message-word permutation schedule `SIGMA` (RFC 7693 § 2.7). BLAKE2b runs
12 rounds over these 10 rows, so rounds 10 and 11 reuse rows 0 and 1. -/
def sigma : List (List ℕ) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
   [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
   [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
   [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
   [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
   [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
   [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
   [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
   [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
   [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

/-- The four column mixes then the four diagonal mixes of one round
(RFC 7693 § 3.2). -/
def mixTable : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
   (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]

/-- The number of rounds, `12` for BLAKE2b (RFC 7693 § 2.5). -/
def rounds : ℕ := 12

/-- The block size in bytes, `bb = 128` for BLAKE2b (RFC 7693 § 2.5). -/
def blockBytes : ℕ := 128

/-! ## The compression function (RFC 7693 § 3.1, § 3.2) -/

/-- Rotate a 64-bit word right by `n`. Called only at `n ∈ {32, 24, 16, 63}`. -/
def rotr (n : ℕ) (x : ℕ) : ℕ :=
  ((x >>> n) ||| (x <<< (64 - n))) % M64

/-- The `G` mixing function, rotations 32/24/16/63 (RFC 7693 § 3.1). -/
def G (v : List ℕ) (a b c d : ℕ) (x y : ℕ) : List ℕ := Id.run do
  let mut v := v
  v := v.set a ((v.getD a 0 + v.getD b 0 + x) % M64)
  v := v.set d (rotr 32 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 24 (v.getD b 0 ^^^ v.getD c 0))
  v := v.set a ((v.getD a 0 + v.getD b 0 + y) % M64)
  v := v.set d (rotr 16 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 63 (v.getD b 0 ^^^ v.getD c 0))
  pure v

/-- The sixteen-word local work vector of RFC 7693 § 3.2, after initialisation
from `h ‖ IV`, the counter and final-flag XORs, and all `rounds` rounds of
mixing.

Separated from `compress` so that the output *shape* is visible without unfolding
the mixing: `compress_length` needs only that the result is an eight-element map. -/
def mixRounds (h m : List ℕ) (t0 t1 : ℕ) (f : Bool) : List ℕ := Id.run do
  let mut v := h ++ IV
  v := v.set 12 ((v.getD 12 0) ^^^ t0)
  v := v.set 13 ((v.getD 13 0) ^^^ t1)
  if f then
    v := v.set 14 ((v.getD 14 0) ^^^ (M64 - 1))
  for rnd in [0:rounds] do
    let sch := sigma.getD (rnd % 10) []
    let mut i := 0
    for (a, b, c, d) in mixTable do
      v := G v a b c d (m.getD (sch.getD (2*i) 0) 0) (m.getD (sch.getD (2*i+1) 0) 0)
      i := i + 1
  pure v

/-- `F(h, m, t, f)`, the compression function of RFC 7693 § 3.2, returning the new
chaining state as eight words: `h'[i] = h[i] ^ v[i] ^ v[i+8]`.

`h` is the eight-word state, `m` the sixteen-word message block, `t` the byte
counter (`t0` low, `t1` high) and `f` the final-block flag. The same expression is
both the chaining update and the finalisation, which is why one definition serves
the fold and the last block alike. -/
def compress (h m : List ℕ) (t0 t1 : ℕ) (f : Bool) : List ℕ :=
  let v := mixRounds h m t0 t1 f
  (List.range 8).map (fun i => (h.getD i 0) ^^^ (v.getD i 0) ^^^ (v.getD (i+8) 0))

/-! ## Words and blocks -/

/-- The little-endian 64-bit words of a byte string, `count` of them starting at
`start`. Short reads are zero-extended, which is exactly the zero padding of a
final partial block. -/
def leWords (data : List UInt8) (start count : ℕ) : List ℕ :=
  (List.range count).map (fun i => Zip2005.leos2ip ((data.drop (start + 8*i)).take 8))

/-- The little-endian bytes of a 64-bit word. -/
def wordBytes (w : ℕ) : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat (w >>> (8*i) % 256))

/-- The little-endian byte serialisation of a state vector. -/
def stateBytes (h : List ℕ) : List UInt8 := h.flatMap wordBytes

/-! ## The parameter block (RFC 7693 § 2.8) -/

/-- Word 0 of the parameter block: `digest_length | key_length << 8 |
fanout << 16 | depth << 24`, with `leaf_length = 0` in the high half. Sequential
(non-tree) hashing has `fanout = depth = 1`. -/
def paramWord0 (digestLen keyLen : ℕ) : ℕ :=
  digestLen ||| (keyLen <<< 8) ||| (1 <<< 16) ||| (1 <<< 24)

/-- The initial chaining state: `IV` XORed with the parameter block.

Words 4 and 5 carry the 16-byte salt and words 6 and 7 the 16-byte
personalisation (parameter-block bytes 32..47 and 48..63). Zcash uses no salt, so
only words 0, 6 and 7 are perturbed — but `salt` is an argument rather than
assumed zero, because leaving it implicit is the kind of omission that makes a
"faithful" transcription quietly wrong for the next caller. -/
def initialState (digestLen keyLen : ℕ) (salt personal : List UInt8) : List ℕ :=
  Id.run do
    let mut h := IV
    h := h.set 0 ((h.getD 0 0) ^^^ paramWord0 digestLen keyLen)
    h := h.set 4 ((h.getD 4 0) ^^^ Zip2005.leos2ip (salt.take 8))
    h := h.set 5 ((h.getD 5 0) ^^^ Zip2005.leos2ip ((salt.drop 8).take 8))
    h := h.set 6 ((h.getD 6 0) ^^^ Zip2005.leos2ip (personal.take 8))
    h := h.set 7 ((h.getD 7 0) ^^^ Zip2005.leos2ip ((personal.drop 8).take 8))
    pure h

/-! ## The hash (RFC 7693 § 3.3) -/

/-- The number of 128-byte blocks a message of `ll` bytes occupies, `dd` in
RFC 7693 § 3.3. An empty message still occupies one, all-zero, block. -/
def blockCount (ll : ℕ) : ℕ := max 1 ((ll + blockBytes - 1) / blockBytes)

/-- Fold the compression function over every block but the last, with the counter
at `(i+1) * bb` and `f = false`. Recursion is on the remaining block count, so it
is structural. -/
def absorbAux (msg : List UInt8) (h : List ℕ) (i k : ℕ) : List ℕ :=
  match k with
  | 0 => h
  | k + 1 =>
      let h' := compress h (leWords msg (i * blockBytes) 16) ((i + 1) * blockBytes) 0 false
      absorbAux msg h' (i + 1) k

/-- `BLAKE2b(personal, nn, msg)` — unkeyed BLAKE2b with a 16-byte
personalisation and `nn` output bytes.

`kk = 0`, so the final block's counter is the total message length `ll` rather
than `ll + bb` (RFC 7693 § 3.3). Keying is deliberately not offered: Zcash never
keys BLAKE2b, and an unused code path is an untested one. -/
def blake2b (personal : List UInt8) (nn : ℕ) (msg : List UInt8) : List UInt8 :=
  let ll := msg.length
  let dd := blockCount ll
  let h0 := initialState nn 0 [] personal
  let h1 := absorbAux msg h0 0 (dd - 1)
  let hFinal := compress h1 (leWords msg ((dd - 1) * blockBytes) 16) ll 0 true
  (stateBytes hFinal).take nn

/-- BLAKE2b-512: 64 output bytes. -/
def blake2b512 (personal : List UInt8) (msg : List UInt8) : List UInt8 :=
  blake2b personal 64 msg

/-! ## Output length

`prfExpand` and everything above it depend on BLAKE2b-512 really returning 64
bytes, so that is a theorem rather than a comment: `compress` returns eight words
and each word serialises to eight bytes.
-/

@[simp] theorem wordBytes_length (w : ℕ) : (wordBytes w).length = 8 := by
  simp [wordBytes]

@[simp] theorem compress_length (h m : List ℕ) (t0 t1 : ℕ) (f : Bool) :
    (compress h m t0 t1 f).length = 8 := by
  simp [compress]

@[simp] theorem stateBytes_length (h : List ℕ) :
    (stateBytes h).length = 8 * h.length := by
  simp [stateBytes, List.length_flatMap, Nat.mul_comm]

/-- BLAKE2b returns `nn` bytes for any `nn ≤ 64`. -/
theorem blake2b_length (personal : List UInt8) {nn : ℕ} (hnn : nn ≤ 64)
    (msg : List UInt8) : (blake2b personal nn msg).length = nn := by
  simp only [blake2b, List.length_take, stateBytes_length, compress_length]
  omega

@[simp] theorem blake2b512_length (personal msg : List UInt8) :
    (blake2b512 personal msg).length = 64 :=
  blake2b_length personal (le_refl 64) msg

/-! ## Conformance

RFC 7693 Appendix A pins unpersonalised BLAKE2b-512 of `"abc"`, which exercises
the compression function, the parameter block's word 0, the single-block path and
the final-block flag together. The *personalised* and *multi-block* paths are
pinned in `Zip2005.Prf` against the Orchard key-component vectors — a stronger
check than any self-consistency test, because those come from outside this tree.

`#guard` evaluates at elaboration time and emits no proof term, so unlike
`native_decide` it adds nothing to the axiom base. That is the posture
`Zip2005Asm.lean` already takes, for the same reason.
-/

/-- The bytes of an ASCII string literal. -/
def asciiBytes (s : String) : List UInt8 := s.toList.map (fun c => UInt8.ofNat c.toNat)

/-- Render a byte string as lowercase hex, so published vectors can be compared
as they are actually written down. -/
def toHex (bs : List UInt8) : String :=
  let digit : ℕ → Char := fun d =>
    if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
  String.ofList (bs.flatMap (fun b => [digit (b.toNat / 16), digit (b.toNat % 16)]))

-- RFC 7693 Appendix A: BLAKE2b-512("abc").
#guard toHex (blake2b512 [] (asciiBytes "abc"))
        == "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1"
         ++ "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"

-- BLAKE2b-512(""): the empty message really is one all-zero block, not none.
#guard toHex (blake2b512 [] [])
        == "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419"
         ++ "d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"

-- Exactly one full block: `dd = 1`, so `absorbAux` does nothing and the single
-- block is the final one, with counter `ll = 128`.
#guard toHex (blake2b512 [] (List.replicate 128 (0 : UInt8)))
        == "865939e120e6805438478841afb739ae4250cf372653078a065cdcfffca4caf7"
         ++ "98e6d462b65d658fc165782640eded70963449ae1500fb0f24981d7727e22c41"

-- Two blocks: exercises `absorbAux` and the counter discipline.
#guard (blake2b512 [] (List.replicate 200 (0 : UInt8))).length == 64

end Zip2005.Blake2b
