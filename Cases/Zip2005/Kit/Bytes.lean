/-
  Cases.Zip2005.Bytes

  A word stored byte by byte (`sb` of its shifts) and read back whole.
-/

import MachineChecked.RiscV.Sym
import Mathlib.Tactic.IntervalCases

namespace Cases.Zip2005

open RiscvZkvm.Rv64

theorem getLsbD_replaceByte (w : Word) (pos : Nat) (b : BitVec 8) (i : Nat) (hi : i < 64) :
    (replaceByte w pos b).getLsbD i =
      if pos * 8 ≤ i ∧ i < pos * 8 + 8 then b.getLsbD (i - pos * 8) else w.getLsbD i := by
  have ff : ∀ k < 64, (0xFF#64).getLsbD k = decide (k < 8) := by decide
  unfold replaceByte
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases h : pos * 8 ≤ i ∧ i < pos * 8 + 8
  · rw [if_pos h, ff _ (by omega)]
    have h1 : ¬ i < pos * 8 := by omega
    have h2 : i - pos * 8 < 8 := by omega
    have h3 : i - pos * 8 < 64 := by omega
    simp [h1, h2, h3]
  · rw [if_neg h]
    by_cases h1 : i < pos * 8
    · simp [h1]
    · have h2 : ¬ i - pos * 8 < 8 := by omega
      rw [ff _ (by omega), BitVec.getLsbD_of_ge b _ (by omega)]
      simp [h1, h2]

/-- The eight bytes of `w`, stored high half first as the guest does, over any
    old word `o`. -/
theorem replaceBytes_word (o w : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte
      (replaceByte (replaceByte (replaceByte (replaceByte o
        4 ((w >>> 32).truncate 8)) 5 ((w >>> 40).truncate 8))
        6 ((w >>> 48).truncate 8)) 7 ((w >>> 56).truncate 8))
      0 (w.truncate 8)) 1 ((w >>> 8).truncate 8))
      2 ((w >>> 16).truncate 8)) 3 ((w >>> 24).truncate 8) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_replaceByte _ _ _ _ hi, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem extractByte_replaceByte (w : Word) (k : Nat) (hk : k < 8) (b : BitVec 8) :
    extractByte (replaceByte w k b) k = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi,
    decide_true, Bool.true_and]
  rw [getLsbD_replaceByte _ _ _ _ (by omega), if_pos (by omega)]
  congr 1; omega

/-- A byte through `lbu`/`sb`: zero-extended, then truncated. -/
theorem trunc8_zext (f : BitVec 8) : BitVec.truncate 8 (BitVec.zeroExtend 64 f) = f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [decide_eq_true (by omega : i < 64), Bool.true_and]

/-- A doubleword reassembled from its eight bytes, as `from_repr` loads it. -/
theorem bytes_word (w : BitVec 64) :
    ((BitVec.zeroExtend 64 (extractByte w 7) <<< 24 ||| BitVec.zeroExtend 64 (extractByte w 6) <<< 16) |||
        (BitVec.zeroExtend 64 (extractByte w 5) <<< 8 ||| BitVec.zeroExtend 64 (extractByte w 4))) <<< 32 |||
      ((BitVec.zeroExtend 64 (extractByte w 3) <<< 24 ||| BitVec.zeroExtend 64 (extractByte w 2) <<< 16) |||
        (BitVec.zeroExtend 64 (extractByte w 1) <<< 8 ||| BitVec.zeroExtend 64 (extractByte w 0))) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp
