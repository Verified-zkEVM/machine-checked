import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Sinsemilla.PadKit
import Cases.Zip2005.Sinsemilla.PadNoteKit

/-!
# The note-commitment message iterator's block

`Pad<Chain<Chain<Chain<Chain<Chain<Empty, BitValIter<u8>>, BitValIter<u8>>, BitValIter<u8>>,
Take<BitValIter<u64>>>, Take<BitValIter<u64>>>>` as `NoteCommitment::derive` builds it
(`iterW sp J`, `Proof/Orchard/NoteCommitDerive.lean`) in its 18-word block: the pad flag and
count (words 0–1), ρ's `Take` cursor (2–5), the chain state byte and the three packed 9-byte
bit-pointers of `g★_d`, `pk★_d`, `v` (6–12), ψ's cursor (13–16), the yield counter (17).
The message words live in `derive`'s frame `sp`: `g★_d` at `sp - 0xd0`, `pk★_d` at
`sp - 0xb0`, `v` at `sp - 0x90`, ρ at `sp - 0x88`, ψ at `sp - 0x68`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

/-- `g★_d`'s 32 bytes (`sp - 0xd0`). -/
@[reducible] def gdP (sp : Word) : Word := sp + 18446744073709551408#64
/-- `pk★_d`'s 32 bytes (`sp - 0xb0`), the end of `g★_d`'s. -/
@[reducible] def pkdP (sp : Word) : Word := sp + 18446744073709551440#64
/-- `v`'s 8 bytes (`sp - 0x90`), the end of `pk★_d`'s. -/
@[reducible] def vP (sp : Word) : Word := sp + 18446744073709551472#64
/-- ρ's words (`sp - 0x88`), the end of `v`'s bytes. -/
@[reducible] def rhoP (sp : Word) : Word := sp + 18446744073709551480#64
/-- ψ's words (`sp - 0x68`), ρ's end. -/
@[reducible] def psiP (sp : Word) : Word := sp + 18446744073709551512#64
/-- ψ's end (`sp - 0x48`). -/
@[reducible] def psiE (sp : Word) : Word := sp + 18446744073709551544#64

/-- The block before the first call: pad off, the counter 0. -/
@[reducible] def noteBlk0 (sp : Word) (J : List Word) (j : Word) : List Word :=
  [0#64, j] ++ iterW sp J ++ [0#64]


/-- Block word 6 during `g★_d`'s phase: the chain state byte `st` (1 before the first call, 0
after) and the byte pointer `pG`'s low seven bytes. -/
@[reducible] def noteW6 (J : List Word) (st : BitVec 8) (pG : Word) : Word :=
  replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 0 st) 1 (BitVec.truncate 8 pG)) 2 (BitVec.truncate 8 (pG >>> 8))) 3 (BitVec.truncate 8 (pG >>> 16))) 4 (BitVec.truncate 8 (pG >>> 24))) 5 (BitVec.truncate 8 (pG >>> 32))) 6 (BitVec.truncate 8 (pG >>> 40))) 7 (BitVec.truncate 8 (pG >>> 48))

/-- Word 7: the pointer's top byte, its head `hG`, and `g★_d`'s end (= `pk★_d`'s start,
`sp - 0xb0`) low six bytes. -/
@[reducible] def noteW7 (sp : Word) (J : List Word) (pG : Word) (hG : BitVec 8) : Word :=
  replaceHalfword (replaceHalfword (replaceHalfword (replaceByte (replaceByte J[5]! 0 (BitVec.truncate 8 (pG >>> 56))) 1 hG) 1 (BitVec.truncate 16 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 16))) 3 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 32))

/-- The block while `g★_d`'s cursor is live, at byte pointer `pG` with head `hG`, `len` items
yielded; the other cursors as `derive` built them. -/
@[reducible] def noteBlkA (sp : Word) (J : List Word) (j : Word) (st : BitVec 8) (pG : Word)
    (hG : BitVec 8) (len : Word) : List Word :=
  [0#64, j, 255#64,
   sp + 18446744073709551480#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))),
   (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   noteW6 J st pG, noteW7 sp J pG hG,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceHalfword J[6]! 0 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 48))) 2 (BitVec.truncate 8 0#64)) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 3 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))),
   (replaceWord32 (replaceByte (replaceByte (replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 1 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 56))) 3 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 32 (sp + 18446744073709551472#64))),
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 (BitVec.truncate 8 0#64)) 5 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16))),
   (replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 3 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 5 (BitVec.truncate 8 0#64)) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64))),
   (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))),
   255#64,
   sp + 18446744073709551512#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))),
   (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   len]

/-- Word 8 during `pk★_d`'s phase: `g★_d`'s end top halfword and end head, then the byte
pointer `pK`'s low five bytes. -/
@[reducible] def noteW8 (sp : Word) (J : List Word) (pK : Word) : Word :=
  replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceHalfword J[6]! 0 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 48))) 2 0#8) 3 (BitVec.truncate 8 pK)) 4 (BitVec.truncate 8 (pK >>> 8))) 5 (BitVec.truncate 8 (pK >>> 16))) 6 (BitVec.truncate 8 (pK >>> 24))) 7 (BitVec.truncate 8 (pK >>> 32))

/-- Word 9: `pK`'s top three bytes, its head `hK`, and `pk★_d`'s end (`sp - 0x90`) low word. -/
@[reducible] def noteW9 (sp : Word) (J : List Word) (pK : Word) (hK : BitVec 8) : Word :=
  replaceWord32 (replaceByte (replaceByte (replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 (pK >>> 40))) 1 (BitVec.truncate 8 (pK >>> 48))) 2 (BitVec.truncate 8 (pK >>> 56))) 3 hK) 1 (BitVec.truncate 32 (sp + 18446744073709551472#64))

/-- The block while `pk★_d`'s cursor is live (state `2`, `g★_d`'s cursor parked at its end), at
byte pointer `pK` with head `hK`, `len` items yielded. -/
@[reducible] def noteBlkB (sp : Word) (J : List Word) (j : Word) (pK : Word) (hK : BitVec 8)
    (len : Word) : List Word :=
  [0#64, j, 255#64,
   sp + 18446744073709551480#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))),
   (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   noteW6 J 2#8 (sp + 18446744073709551440#64), noteW7 sp J (sp + 18446744073709551440#64) 0#8,
   noteW8 sp J pK, noteW9 sp J pK hK,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 (BitVec.truncate 8 0#64)) 5 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16))),
   (replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 3 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 5 (BitVec.truncate 8 0#64)) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64))),
   (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))),
   255#64,
   sp + 18446744073709551512#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))),
   (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   len]

/-- Word 10 during `v`'s phase: `pk★_d`'s end top word and end head, then the byte pointer
`pV`'s low three bytes. -/
@[reducible] def noteW10 (sp : Word) (J : List Word) (pV : Word) : Word :=
  replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 0#8) 5 (BitVec.truncate 8 pV)) 6 (BitVec.truncate 8 (pV >>> 8))) 7 (BitVec.truncate 8 (pV >>> 16))

/-- Word 11: `pV`'s top five bytes, its head `hV`, and `v`'s end (`sp - 0x88`) low halfword. -/
@[reducible] def noteW11 (sp : Word) (J : List Word) (pV : Word) (hV : BitVec 8) : Word :=
  replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 0 (BitVec.truncate 8 (pV >>> 24))) 1 (BitVec.truncate 8 (pV >>> 32))) 2 (BitVec.truncate 8 (pV >>> 40))) 3 (BitVec.truncate 8 (pV >>> 48))) 4 (BitVec.truncate 8 (pV >>> 56))) 5 hV) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64))

/-- The block while `v`'s cursor is live (state `3`, the two earlier cursors parked at their
ends), at byte pointer `pV` with head `hV`, `len` items yielded. -/
@[reducible] def noteBlkC (sp : Word) (J : List Word) (j : Word) (pV : Word) (hV : BitVec 8)
    (len : Word) : List Word :=
  [0#64, j, 255#64,
   sp + 18446744073709551480#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))),
   (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   noteW6 J 3#8 (sp + 18446744073709551440#64), noteW7 sp J (sp + 18446744073709551440#64) 0#8,
   noteW8 sp J (sp + 18446744073709551472#64), noteW9 sp J (sp + 18446744073709551472#64) 0#8,
   noteW10 sp J pV, noteW11 sp J pV hV,
   (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))),
   255#64,
   sp + 18446744073709551512#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))),
   (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   len]

/-- The block while `ρ`'s cursor (a `Take` of a `u64` bit iterator, block words 2–5) is live
(state `4`, the byte cursors parked at their ends): `nR` bits left, word pointer `pR`, head
`hR`, `len` items yielded. -/
@[reducible] def noteBlkD (sp : Word) (J : List Word) (j nR pR : Word) (hR : BitVec 8)
    (len : Word) : List Word :=
  [0#64, j, nR, pR,
   replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))) 0 hR,
   (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   noteW6 J 4#8 (sp + 18446744073709551440#64), noteW7 sp J (sp + 18446744073709551440#64) 0#8,
   noteW8 sp J (sp + 18446744073709551472#64), noteW9 sp J (sp + 18446744073709551472#64) 0#8,
   noteW10 sp J (sp + 18446744073709551480#64), noteW11 sp J (sp + 18446744073709551480#64) 0#8,
   (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))),
   255#64,
   sp + 18446744073709551512#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))),
   (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   len]

/-- The block while `ψ`'s cursor (words 13–16) is live (state `5`, `ρ`'s cursor exhausted at
bit 255): `nQ` bits left, word pointer `pQ`, head `hQ`, `len` items yielded. -/
@[reducible] def noteBlkE (sp : Word) (J : List Word) (j nQ pQ : Word) (hQ : BitVec 8)
    (len : Word) : List Word :=
  [0#64, j, 0#64, sp + 18446744073709551504#64,
   replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))) 0 63#8,
   (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   noteW6 J 5#8 (sp + 18446744073709551440#64), noteW7 sp J (sp + 18446744073709551440#64) 0#8,
   noteW8 sp J (sp + 18446744073709551472#64), noteW9 sp J (sp + 18446744073709551472#64) 0#8,
   noteW10 sp J (sp + 18446744073709551480#64), noteW11 sp J (sp + 18446744073709551480#64) 0#8,
   (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))),
   nQ, pQ,
   replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))) 0 hQ,
   (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   len]

/-- The block once the message is exhausted and the padding is being emitted: the pad flag
set, `left` zero bits still to yield, every cursor at its end, the counter stuck at 1086. -/
@[reducible] def noteBlkP (sp : Word) (J : List Word) (left : Word) : List Word :=
  [1#64, left, 0#64, sp + 18446744073709551504#64,
   replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))) 0 63#8,
   (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   noteW6 J 5#8 (sp + 18446744073709551440#64), noteW7 sp J (sp + 18446744073709551440#64) 0#8,
   noteW8 sp J (sp + 18446744073709551472#64), noteW9 sp J (sp + 18446744073709551472#64) 0#8,
   noteW10 sp J (sp + 18446744073709551480#64), noteW11 sp J (sp + 18446744073709551480#64) 0#8,
   (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))),
   0#64, sp + 18446744073709551536#64,
   replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))) 0 63#8,
   (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   1086#64]




/-- Before the first call: state `1`, the pointer at `g★_d`'s first byte, head `0`, nothing
yielded. -/
theorem noteBlk0_eq (sp : Word) (J : List Word) (j : Word) :
    noteBlk0 sp J j = noteBlkA sp J j 1#8 (sp + 18446744073709551408#64) 0#8 0#64 := by
  simp only [noteBlk0, noteBlkA, iterW, List.cons_append, List.nil_append, List.cons.injEq, and_true,
    true_and]
  refine ⟨?_, ?_⟩
  · apply word_ext
    intro k hk
    interval_cases k
    all_goals simp (disch := decide) only [noteW6, extractByte_replaceByte, extractByte_replaceByte_ne]
    all_goals rfl
  · apply word_ext
    intro k hk
    interval_cases k
    all_goals simp (disch := decide) only [noteW7, extractByte_replaceByte, extractByte_replaceByte_ne,
      extractByte_replaceHalfword_ne]
    all_goals rfl

end Cases.Zip2005
