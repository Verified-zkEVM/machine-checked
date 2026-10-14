import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Sinsemilla.PadKit

/-!
# The `commit_ivk` message iterator's block

`Pad<Chain<Chain<Empty, Take<BitValIter>>, Take<BitValIter>>>` (K = 10), 96 bytes, as
`commit_ivk` builds it (`iterIvkW`, `Proof/Orchard/CommitIvk.lean`) and `from_iter` copies it
into its own frame: `padding_left` at 0 (tag word, count word), `len` at 0x58, the outer `Take`
of `nk`'s bits (count 0x10, cursor pointer 0x18, head bit 0x20, end cursor packed at
0x21–0x29) and, consumed first, the inner chain's `Take` of `ak`'s bits (count 0x30, pointer
0x38, head 0x40, end 0x41–0x49) with the `Option<Empty>` tag byte at 0x50 (1 = `Some(Empty)`
before the first call, 0 after it, 2 once the inner chain is exhausted).

The message words sit in `commit_ivk`'s frame: `ak`'s four words at `sp - 0xd8` (`ptrA`), `nk`'s
at `sp - 0xb8` (`ptrB`, also the inner cursor's end), the outer cursor's end at `sp - 0x98`
(`endB`). The words of this file are stated as the sub-word stores left them (`replaceByte`
chains over the block's previous contents `J`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

/-- `ak`'s message words (`sp - 0xd8`). -/
@[reducible] def ptrA (sp : Word) : Word := sp + 18446744073709551400#64
/-- `nk`'s message words (`sp - 0xb8`), the inner cursor's end. -/
@[reducible] def ptrB (sp : Word) : Word := sp + 18446744073709551432#64
/-- The outer cursor's end (`sp - 0x98`). -/
@[reducible] def endB (sp : Word) : Word := sp + 18446744073709551464#64

/-- Word 4 of the block: the outer cursor's head byte (0) and its end pointer's low 7 bytes. -/
@[reducible] def ivkEndB (sp : Word) (J : List Word) : Word :=
  replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
     (replaceByte J[2]! 2 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 8))) 3
     (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 16)))
     4 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 24)))
     5 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 32)))
     0 (BitVec.truncate 8 0#64))
     1 (BitVec.truncate 8 (sp + 18446744073709551464#64)))
     6 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 40)))
     7 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 48))

/-- Word 5: the end pointer's top byte and the end head (0). -/
@[reducible] def ivkEndB2 (sp : Word) (J : List Word) : Word :=
  replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 56))) 1
     (BitVec.truncate 8 0#64)

/-- Word 8: the inner cursor's head byte (0) and its end pointer's low 7 bytes. -/
@[reducible] def ivkEndA (sp : Word) (J : List Word) : Word :=
  replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
     (replaceByte J[6]! 3 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 16))) 4
     (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 24)))
     5 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 32)))
     6 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 40)))
     0 (BitVec.truncate 8 0#64))
     1 (BitVec.truncate 8 (sp + 18446744073709551432#64)))
     2 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 8)))
     7 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 48))

/-- Word 9: the inner end pointer's top byte and the end head (0). -/
@[reducible] def ivkEndA2 (sp : Word) (J : List Word) : Word :=
  replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 56))) 1
     (BitVec.truncate 8 0#64)

/-- The block while the inner cursor (`ak`'s bits) is live: its count, pointer and head bit, the
    `Option<Empty>` tag `tg` (1 before the first call, 0 after), the outer cursor untouched. -/
@[reducible] def padIvkA (sp : Word) (J : List Word) (j nA pA : Word) (hA : BitVec 8) (tg len : Word) :
    List Word :=
  [0#64, j, 255#64, ptrB sp, ivkEndB sp J, ivkEndB2 sp J,
   nA, pA, replaceByte (ivkEndA sp J) 0 hA, ivkEndA2 sp J,
   replaceByte J[8]! 0 (BitVec.truncate 8 tg), len]

/-- The block once the inner cursor is exhausted (tag 2, its cursor at bit 255) and the outer
    cursor (`nk`'s bits) is live. -/
@[reducible] def padIvkB (sp : Word) (J : List Word) (j nB pB : Word) (hB : BitVec 8) (len : Word) :
    List Word :=
  [0#64, j, nB, pB, replaceByte (ivkEndB sp J) 0 hB, ivkEndB2 sp J,
   0#64, ptrA sp + 24#64, replaceByte (ivkEndA sp J) 0 63#8, ivkEndA2 sp J,
   replaceByte J[8]! 0 (BitVec.truncate 8 2#64), len]

/-! ## The bytes the block's `lbu`s load, as the executor rewrites them -/

theorem ivkTag_byte0 (J : List Word) :
    BitVec.zeroExtend 64 (extractByte (replaceByte J[8]! 0 0#8) 0) = 0#64 := by
  rw [extractByte_replaceByte _ _ (by decide)]; rfl

theorem ivkTag_byte1 (J : List Word) :
    BitVec.zeroExtend 64 (extractByte (replaceByte J[8]! 0 1#8) 0) = 1#64 := by
  rw [extractByte_replaceByte _ _ (by decide)]; rfl

theorem ivkTag_byte2 (J : List Word) :
    BitVec.zeroExtend 64 (extractByte (replaceByte J[8]! 0 2#8) 0) = 2#64 := by
  rw [extractByte_replaceByte _ _ (by decide)]; rfl

theorem ivkEndA_head (sp : Word) (J : List Word) (hA : BitVec 8) :
    BitVec.zeroExtend 64 (extractByte (replaceByte (ivkEndA sp J) 0 hA) 0) = BitVec.zeroExtend 64 hA := by
  rw [extractByte_replaceByte _ _ (by decide)]

theorem ivkEndA_byte (sp : Word) (J : List Word) (hA : BitVec 8) (i : Nat) (hi : 1 ≤ i ∧ i ≤ 7) :
    extractByte (replaceByte (ivkEndA sp J) 0 hA) i = extractByte (ptrB sp) (i - 1) := by
  obtain ⟨h1, h7⟩ := hi
  interval_cases i <;>
    simp (disch := decide) only [ivkEndA, extractByte_replaceByte_ne, extractByte_replaceByte,
      trunc8_eq_extractByte, extractByte_shr8, extractByte_shr16, extractByte_shr24,
      extractByte_shr32, extractByte_shr40, extractByte_shr48]

theorem ivkEndA2_byte0 (sp : Word) (J : List Word) :
    extractByte (ivkEndA2 sp J) 0 = extractByte (ptrB sp) 7 := by
  simp (disch := decide) only [ivkEndA2, extractByte_replaceByte_ne, extractByte_replaceByte,
    trunc8_eq_extractByte, extractByte_shr56]

theorem ivkEndA2_byte1 (sp : Word) (J : List Word) : extractByte (ivkEndA2 sp J) 1 = 0#8 := by
  simp (disch := decide) only [ivkEndA2, extractByte_replaceByte]
  rfl

theorem ivkEndB_head (sp : Word) (J : List Word) (hB : BitVec 8) :
    BitVec.zeroExtend 64 (extractByte (replaceByte (ivkEndB sp J) 0 hB) 0) = BitVec.zeroExtend 64 hB := by
  rw [extractByte_replaceByte _ _ (by decide)]

theorem ivkEndB_byte (sp : Word) (J : List Word) (hB : BitVec 8) (i : Nat) (hi : 1 ≤ i ∧ i ≤ 7) :
    extractByte (replaceByte (ivkEndB sp J) 0 hB) i = extractByte (endB sp) (i - 1) := by
  obtain ⟨h1, h7⟩ := hi
  interval_cases i <;>
    simp (disch := decide) only [ivkEndB, extractByte_replaceByte_ne, extractByte_replaceByte,
      trunc8_eq_extractByte, extractByte_shr8, extractByte_shr16, extractByte_shr24,
      extractByte_shr32, extractByte_shr40, extractByte_shr48]

/-- The outer cursor's head byte before any step: the block's own `0`. -/
theorem ivkEndB_head0 (sp : Word) (J : List Word) :
    BitVec.zeroExtend 64 (extractByte (ivkEndB sp J) 0) = 0#64 := by
  simp (disch := decide) only [ivkEndB, extractByte_replaceByte_ne, extractByte_replaceByte]
  rfl

theorem ivkEndB_byte0 (sp : Word) (J : List Word) (i : Nat) (hi : 1 ≤ i ∧ i ≤ 7) :
    extractByte (ivkEndB sp J) i = extractByte (endB sp) (i - 1) := by
  obtain ⟨h1, h7⟩ := hi
  interval_cases i <;>
    simp (disch := decide) only [ivkEndB, extractByte_replaceByte_ne, extractByte_replaceByte,
      trunc8_eq_extractByte, extractByte_shr8, extractByte_shr16, extractByte_shr24,
      extractByte_shr32, extractByte_shr40, extractByte_shr48]

theorem ivkEndB2_byte0 (sp : Word) (J : List Word) :
    extractByte (ivkEndB2 sp J) 0 = extractByte (endB sp) 7 := by
  simp (disch := decide) only [ivkEndB2, extractByte_replaceByte_ne, extractByte_replaceByte,
    trunc8_eq_extractByte, extractByte_shr56]

theorem ivkEndB2_byte1 (sp : Word) (J : List Word) : extractByte (ivkEndB2 sp J) 1 = 0#8 := by
  simp (disch := decide) only [ivkEndB2, extractByte_replaceByte]
  rfl

end Cases.Zip2005
