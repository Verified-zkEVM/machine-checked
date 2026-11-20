/-
  Examples.Spec

  The functions the examples are specified with. They are about words, numbers and lists, and
  know nothing of any instruction set: a word is a `BitVec 64`, which is what the RISC-V
  machine's `Word` is. What reads a machine state (`bytesAt`, `StrAt`, `WordsAt`) is not here:
  it is in `Examples/Kit.lean` or beside the proof that uses it.

  The functions several modules could use are in `Examples`; the specification of one algorithm
  is in its module's namespace (`Examples.Sha256.round`), where that module's proofs see it.
-/

namespace Examples

/-! ## Words and lists -/

/-- The unsigned maximum. -/
def umax (a b : BitVec 64) : BitVec 64 := if b < a then a else b

/-- The signed maximum: `a > b ? a : b` on `long`. -/
def smax (a b : BitVec 64) : BitVec 64 := if b.slt a then a else b

/-- `x < lo ? lo : (x > hi ? hi : x)`, signed. -/
def clampSpec (x lo hi : BitVec 64) : BitVec 64 :=
  if x.slt lo then lo else if hi.slt x then hi else x

/-- The sum of a list of words, modulo `2^64`. -/
def wsum : List (BitVec 64) → BitVec 64
  | [] => 0
  | x :: xs => x + wsum xs

/-- The greatest common divisor of two words. -/
def wgcd (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (Nat.gcd a.toNat b.toNat)

/-! ## Numbers -/

/-- The sum `n + (n - 1) + … + 1`, as the loop of `sum_to` adds it. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- Twice the sum is `n (n + 1)`. -/
theorem two_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo]; grind

/-- **The closed form** of the sum. -/
theorem sumTo_eq (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  have := two_sumTo n; omega

/-- The number of one bits of a number. -/
def ones : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) % 2 + ones ((n + 1) / 2)

theorem ones_eq (n : Nat) : ones n = n % 2 + ones (n / 2) := by
  cases n with
  | zero => simp [ones]
  | succ n => rw [ones]

/-- The loop `while (n) { n >>= 1; k++; }` on numbers: how many halvings take `n` to zero. -/
def countDown (n : Nat) : Nat := if n = 0 then 0 else countDown (n / 2) + 1
decreasing_by omega

/-- The factorial. -/
def factN : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factN n

/-- The Fibonacci numbers, `fibN 0 = 0`, `fibN 1 = 1`. -/
def fibN : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibN n + fibN (n + 1)

/-- The number a list of 64-bit limbs stands for, least significant first. -/
def limbsVal : List (BitVec 64) → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 ^ 64 * limbsVal xs

theorem limbsVal_append_singleton (xs : List (BitVec 64)) (x : BitVec 64) :
    limbsVal (xs ++ [x]) = limbsVal xs + 2 ^ (64 * xs.length) * x.toNat := by
  induction xs with
  | nil => simp [limbsVal]
  | cons y ys ih =>
    simp only [List.cons_append, limbsVal, ih, List.length_cons, Nat.mul_add, Nat.pow_add,
      Nat.mul_one]
    rw [Nat.mul_comm (2 ^ (64 * ys.length)) (2 ^ 64), Nat.mul_assoc]
    omega

/-! ## Bytes: `equal_bytes` -/

namespace Mem

/-- `equal_bytes`'s result: 1 if the two byte lists are the same, and 0 otherwise. -/
def equalSpec (xs ys : List (BitVec 8)) : BitVec 64 := if xs = ys then 1#64 else 0#64

end Mem

/-! ## CRC-32, four bits at a time -/

namespace Crc32

/-- The table of the reflected polynomial `0xEDB88320`, for four bits at a time. -/
def table : List (BitVec 32) :=
  [0x00000000, 0x1db71064, 0x3b6e20c8, 0x26d930ac, 0x76dc4190, 0x6b6b51f4, 0x4db26158, 0x5005713c,
   0xedb88320, 0xf00f9344, 0xd6d6a3e8, 0xcb61b38c, 0x9b64c2b0, 0x86d3d2d4, 0xa00ae278, 0xbdbdf21c]

/-- The table's entry for a nibble. -/
def tbl (i : BitVec 4) : BitVec 32 := table.getD i.toNat 0

/-- Four bits of the CRC. -/
def nib (c : BitVec 32) : BitVec 32 := (c >>> 4) ^^^ tbl (c.setWidth 4)

/-- One byte of the CRC. -/
def crcStep (c : BitVec 32) (b : BitVec 8) : BitVec 32 := nib (nib (c ^^^ b.zeroExtend 32))

/-- CRC-32 of `bytes`, continuing from `crc`. -/
def crc32Spec (crc : BitVec 32) (bytes : List (BitVec 8)) : BitVec 32 :=
  ~~~ (bytes.foldl crcStep (~~~ crc))

/-- The check value of CRC-32: that of the ASCII digits `123456789`. -/
example : crc32Spec 0 [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xcbf43926 := by
  decide

end Crc32

/-! ## ChaCha20 -/

namespace ChaCha20

/-- ChaCha20's quarter round (RFC 8439, 2.1). -/
def qr (a b c d : BitVec 32) : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a := a + b
  let d := (d ^^^ a).rotateLeft 16
  let c := c + d
  let b := (b ^^^ c).rotateLeft 12
  let a := a + b
  let d := (d ^^^ a).rotateLeft 8
  let c := c + d
  let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- The test vector of RFC 8439, 2.1.1. -/
example : qr 0x11111111 0x01020304 0x9b8d6f43 0x01234567 =
    (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb) := by decide

/-- ChaCha20's state: sixteen 32-bit words (RFC 8439, 2.2). -/
abbrev State := Fin 16 → BitVec 32

/-- `QUARTERROUND(a, b, c, d)` on the state (RFC 8439, 2.2): `qr` on the words at `a`, `b`, `c`,
    `d`; the other words are as they were. -/
def quarterRound (a b c d : Fin 16) (s : State) : State :=
  let (a', b', c', d') := qr (s a) (s b) (s c) (s d)
  fun i => if i = a then a' else if i = b then b' else if i = c then c' else if i = d then d'
    else s i

/-- The four quarter rounds on the columns (RFC 8439, 2.3). -/
def columnRound (s : State) : State :=
  quarterRound 3 7 11 15 (quarterRound 2 6 10 14 (quarterRound 1 5 9 13 (quarterRound 0 4 8 12 s)))

/-- The four quarter rounds on the diagonals (RFC 8439, 2.3). -/
def diagonalRound (s : State) : State :=
  quarterRound 3 4 9 14 (quarterRound 2 7 8 13 (quarterRound 1 6 11 12 (quarterRound 0 5 10 15 s)))

/-- `inner_block` (RFC 8439, 2.3.1): a column round, then a diagonal round. -/
def doubleRound (s : State) : State := diagonalRound (columnRound s)

/-- The twenty rounds: ten double rounds. -/
def rounds20 (s : State) : State := Nat.repeat doubleRound 10 s

/-- **The ChaCha20 block function** (RFC 8439, 2.3): the state after twenty rounds, added word
    by word to the state it started from. The serialization of the result is not part of it:
    this is the sixteen words before they are written out as bytes. -/
def block (s : State) : State := fun i => rounds20 s i + s i

/-- The test vector of RFC 8439, 2.3.2: the key `00:01:…:1f`, the block count 1 and the nonce
    `00:00:00:09:00:00:00:4a:00:00:00:00`, as the state's sixteen words, and the block function
    of it. -/
example : List.ofFn (block fun i => [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
      0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918,
      0x1f1e1d1c, 0x00000001, 0x09000000, 0x4a000000, 0x00000000].getD i.val 0) =
    [0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3, 0xc7f4d1c7, 0x0368c033, 0x9aaa2204,
      0x4e6cd4c3, 0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9, 0xd19c12b5, 0xb94e16de,
      0xe883d0cb, 0x4e3c50a2] := by decide

end ChaCha20

/-! ## SHA-256, as FIPS 180-4 has it: the round, the message schedule and the compression
  function -/

namespace Sha256

def rotr (x : BitVec 32) (n : Nat) : BitVec 32 := x.rotateRight n
def ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : BitVec 32) : BitVec 32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : BitVec 32) : BitVec 32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- One round of SHA-256 (FIPS 180-4, 6.2.2 step 3) on the working variables `a`..`h`, with the
    round's constant `k` and word `w`. -/
def round (a b c d e f g h k w : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let t1 := h + bsig1 e + ch e f g + k + w
  let t2 := bsig0 a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

def ssig0 (x : BitVec 32) : BitVec 32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ssig1 (x : BitVec 32) : BitVec 32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The message schedule (FIPS 180-4, 6.2.2 step 1): the sixteen words of the block, then each
    word from four before it. -/
def W (init : Nat → BitVec 32) (t : Nat) : BitVec 32 :=
  if t < 16 then init t
  else ssig1 (W init (t - 2)) + W init (t - 7) + ssig0 (W init (t - 15)) + W init (t - 16)
termination_by t
decreasing_by all_goals omega

theorem W_step (init : Nat → BitVec 32) {t : Nat} (h : 16 ≤ t) :
    W init t = ssig1 (W init (t - 2)) + W init (t - 7) + ssig0 (W init (t - 15)) + W init (t - 16) := by
  rw [W, ite_eq_right (by omega)]

/-- The words of the block: the schedule's first sixteen. -/
theorem W_init (init : Nat → BitVec 32) {t : Nat} (h : t < 16) : W init t = init t := by
  rw [W, ite_eq_left h]

/-- The sixty-four constants of SHA-256 (FIPS 180-4, 4.2.2). -/
def K : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Eight 32-bit words: a hash value, or the working variables `a`..`h`. -/
abbrev Words8 :=
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- The working variables after the first `t` rounds over the schedule of the block `M`, from
    the hash value `H` (FIPS 180-4, 6.2.2 steps 2 and 3). -/
def rounds (H : Words8) (M : Nat → BitVec 32) : Nat → Words8
  | 0 => H
  | t + 1 =>
    let (a, b, c, d, e, f, g, h) := rounds H M t
    round a b c d e f g h (K.getD t 0) (W M t)

/-- **The compression function** of SHA-256 (FIPS 180-4, 6.2.2): the hash value `H` and the
    sixteen words `M 0`, …, `M 15` of a block give the next hash value, `H` plus the working
    variables after sixty-four rounds, word by word modulo `2 ^ 32`. -/
def compress (H : Words8) (M : Nat → BitVec 32) : Words8 :=
  let (a, b, c, d, e, f, g, h) := rounds H M 64
  let (h0, h1, h2, h3, h4, h5, h6, h7) := H
  (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e, h5 + f, h6 + g, h7 + h)

end Sha256

end Examples
