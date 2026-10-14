import Cases.Zip2005.Kit.Bytes

/-!
# The bytes a bincode `[u8; 32]` read leaves

`inBytes W r` are the 32 bytes at byte offset `r` of the aligned words `W`; `arr32W O W r` is the
`Result<[u8; 32], Box<ErrorKind>>` written over the five words `O` on success: tag byte 0, the
bytes at offsets 1..32, the rest of the last word unchanged.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

/-- Byte `k` of the words `W` from byte offset `r`. -/
def inByte (W : List Word) (r k : Nat) : BitVec 8 := extractByte W[(r + k) / 8]! ((r + k) % 8)

/-- The 32 bytes at byte offset `r` of `W`. -/
def inBytes (W : List Word) (r : Nat) : List (BitVec 8) := (List.range 32).map (inByte W r)

/-- A doubleword from its eight bytes, low byte first. -/
def word8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : Word :=
  replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
    (replaceByte 0#64 0 b0) 1 b1) 2 b2) 3 b3) 4 b4) 5 b5) 6 b6) 7 b7

/-- `Ok(bytes)` over `O`: tag byte 0, then the 32 bytes. -/
def arr32W (O W : List Word) (r : Nat) : List Word :=
  [word8 0#8 (inByte W r 0) (inByte W r 1) (inByte W r 2) (inByte W r 3) (inByte W r 4)
     (inByte W r 5) (inByte W r 6),
   word8 (inByte W r 7) (inByte W r 8) (inByte W r 9) (inByte W r 10) (inByte W r 11)
     (inByte W r 12) (inByte W r 13) (inByte W r 14),
   word8 (inByte W r 15) (inByte W r 16) (inByte W r 17) (inByte W r 18) (inByte W r 19)
     (inByte W r 20) (inByte W r 21) (inByte W r 22),
   word8 (inByte W r 23) (inByte W r 24) (inByte W r 25) (inByte W r 26) (inByte W r 27)
     (inByte W r 28) (inByte W r 29) (inByte W r 30),
   replaceByte O[4]! 0 (inByte W r 31)]

@[simp] theorem arr32W_length (O W : List Word) (r : Nat) : (arr32W O W r).length = 5 := rfl

/-- `Ok(Some(bytes))` over the five words `O`: tags 0 and 1, then the 32 bytes at byte offset `r`
of `W` (an `Option<[u8; 32]>`, or a sequence element, read into a `Result`). -/
def someW (O W : List Word) (r : Nat) : List Word :=
  [word8 0#8 1#8 (inByte W r 0) (inByte W r 1) (inByte W r 2) (inByte W r 3) (inByte W r 4)
     (inByte W r 5),
   word8 (inByte W r 6) (inByte W r 7) (inByte W r 8) (inByte W r 9) (inByte W r 10)
     (inByte W r 11) (inByte W r 12) (inByte W r 13),
   word8 (inByte W r 14) (inByte W r 15) (inByte W r 16) (inByte W r 17) (inByte W r 18)
     (inByte W r 19) (inByte W r 20) (inByte W r 21),
   word8 (inByte W r 22) (inByte W r 23) (inByte W r 24) (inByte W r 25) (inByte W r 26)
     (inByte W r 27) (inByte W r 28) (inByte W r 29),
   replaceByte (replaceByte O[4]! 0 (inByte W r 30)) 1 (inByte W r 31)]

@[simp] theorem someW_length (O W : List Word) (r : Nat) : (someW O W r).length = 5 := rfl

/-- `Ok`'s tag byte. -/
theorem arr32W_tag (O W : List Word) (r : Nat) : extractByte (arr32W O W r)[0]! 0 = 0#8 := by
  simp only [arr32W, List.getElem!_cons_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [word8, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, Nat.zero_mul, Nat.zero_add,
    getLsbD_replaceByte _ _ _ _ (show i < 64 by omega)]
  interval_cases i <;> simp

end Cases.Zip2005
