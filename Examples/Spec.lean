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

end ChaCha20

/-! ## SHA-256, as FIPS 180-4 has it: the round and the message schedule -/

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

end Sha256

end Examples
