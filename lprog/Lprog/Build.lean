/-
  Lprog.Build

  Expressions and operations as the lifts write them: short names for the shared operations,
  and what those lack, written out in them.

  * Values that are 0 or 1 (`bit`, `isZero`, `nonZero`, `flip`) and the choice between two
    values by one (`choose`): `b ^ ((a ^ b) & -c)`.
  * A reversal of bytes or of bits is masks and shifts in a register the instruction set
    keeps for it; a count of leading zeros is six halving steps in two.

  ## Main definitions

  * `choose`, `reverseBytes`, `reverseBits`, `countLeadingZeros`
-/

import Lprog.Op

namespace Lprog.Build

variable {Reg : Type}

def num (n : Nat) : Expr Reg := .imm (BitVec.ofNat 64 n)
def add (a b : Expr Reg) : Expr Reg := .bin .add a b
def sub (a b : Expr Reg) : Expr Reg := .bin .sub a b
def band (a b : Expr Reg) : Expr Reg := .bin .and a b
def bor (a b : Expr Reg) : Expr Reg := .bin .or a b
def bxor (a b : Expr Reg) : Expr Reg := .bin .xor a b
def shl (a : Expr Reg) (n : Nat) : Expr Reg := if n = 0 then a else .bin .shl a (num n)
def lshr (a : Expr Reg) (n : Nat) : Expr Reg := if n = 0 then a else .bin .lshr a (num n)
def ashr (a : Expr Reg) (n : Nat) : Expr Reg := if n = 0 then a else .bin .ashr a (num n)
def bnot (a : Expr Reg) : Expr Reg := .un .not a
def z32 (a : Expr Reg) : Expr Reg := .un (.zext .b4) a
def s32 (a : Expr Reg) : Expr Reg := .un (.sext .b4) a

/-- Bit `k` of `a`: 0 or 1. -/
def bit (a : Expr Reg) (k : Nat) : Expr Reg := band (lshr a k) (num 1)

/-- 1 if `a` is zero, 0 if not; and the other way round. -/
def isZero (a : Expr Reg) : Expr Reg := .bin .ult a (num 1)
def nonZero (a : Expr Reg) : Expr Reg := .bin .ult (num 0) a

/-- The other of 0 and 1. -/
def flip (c : Expr Reg) : Expr Reg := bxor c (num 1)

/-- `a` if `c` is 1, `b` if it is 0. -/
def choose (c a b : Expr Reg) : Expr Reg := bxor b (band (bxor a b) (.un .neg c))

/-- A mask of the low `n` bits. -/
def ones (n : Nat) : Expr Reg := .imm (BitVec.ofNat 64 (2 ^ n - 1))

/-! ## What the shared operations lack -/

/-- `t`, with each run of `k` bits swapped with the next: `m` masks the lower of each pair. -/
def swap (t : Reg) (k : Nat) (m : Nat) : Op Reg :=
  .set t (bor (shl (band (.reg t) (num m)) k) (band (lshr (.reg t) k) (num m)))

/-- The bytes of `t` reversed within each run of `2 ^ depth` bytes (1, 2 or 3). -/
def reverseBytes (t : Reg) (depth : Nat) : List (Op Reg) :=
  ([(8, 0x00ff00ff00ff00ff), (16, 0x0000ffff0000ffff), (32, 0x00000000ffffffff)].take depth).map
    fun (k, m) => swap t k m

/-- The bits of `t` reversed. -/
def reverseBits (t : Reg) : List (Op Reg) :=
  [swap t 1 0x5555555555555555, swap t 2 0x3333333333333333, swap t 4 0x0f0f0f0f0f0f0f0f] ++ reverseBytes t 3

/-- The number of leading zeros of `t`, into `t`; it uses `u`. Each step moves `t` up
    by `k` if its top `k` bits are zero, and counts `k`. -/
def countLeadingZeros (t u : Reg) : List (Op Reg) :=
  [.set u (num 0)] ++
  ([32, 16, 8, 4, 2, 1].flatMap fun k =>
    -- 1 if the top `k` bits are zero
    let free := isZero (lshr (.reg t) (64 - k))
    [.set u (add (.reg u) (.bin .mul free (num k))),
     .set t (.bin .mul (.reg t) (add (.bin .mul free (num (2 ^ k - 1))) (num 1)))]) ++
  [.set t (add (.reg u) (isZero (lshr (.reg t) 63)))]

end Lprog.Build
