import Cases.Zip2005.Kit.ByteKit

/-! Bytes of a word with a halfword (`sh`) or a 32-bit word (`sw`) stored at any position, and
the two bytes of a sign-extended halfword load (`lh`), at literal positions, for `byte_simp`.
Position 0 of `replaceHalfword` is in `Proof/Kit/ByteKit.lean`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem xb_rh1_0 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 0 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh1_1 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 1 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh1_2 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 2 = extractByte (BitVec.zeroExtend 64 h) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh1_3 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 3 = extractByte (BitVec.zeroExtend 64 h) 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh1_4 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 4 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh1_5 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 5 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh1_6 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 6 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh1_7 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 1 h) 7 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_0 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 0 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_1 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 1 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_2 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 2 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_3 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 3 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_4 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 4 = extractByte (BitVec.zeroExtend 64 h) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_5 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 5 = extractByte (BitVec.zeroExtend 64 h) 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_6 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 6 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh2_7 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 2 h) 7 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_0 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 0 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_1 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 1 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_2 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 2 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_3 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 3 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_4 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 4 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_5 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 5 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_6 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 6 = extractByte (BitVec.zeroExtend 64 h) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rh3_7 (w : Word) (h : BitVec 16) :
    extractByte (replaceHalfword w 3 h) 7 = extractByte (BitVec.zeroExtend 64 h) 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_0 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 0 = extractByte (BitVec.zeroExtend 64 v) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_1 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 1 = extractByte (BitVec.zeroExtend 64 v) 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_2 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 2 = extractByte (BitVec.zeroExtend 64 v) 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_3 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 3 = extractByte (BitVec.zeroExtend 64 v) 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_4 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 4 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_5 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 5 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_6 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 6 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_7 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 0 v) 7 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_0 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 0 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_1 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 1 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_2 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 2 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_3 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 3 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_4 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 4 = extractByte (BitVec.zeroExtend 64 v) 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_5 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 5 = extractByte (BitVec.zeroExtend 64 v) 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_6 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 6 = extractByte (BitVec.zeroExtend 64 v) 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw1_7 (w : Word) (v : BitVec 32) :
    extractByte (replaceWord32 w 1 v) 7 = extractByte (BitVec.zeroExtend 64 v) 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_lh0_0 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 0)) 0 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_lh0_1 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 0)) 1 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_lh1_0 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 1)) 0 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_lh1_1 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 1)) 1 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_lh2_0 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 2)) 0 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_lh2_1 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 2)) 1 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_lh3_0 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 3)) 0 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_lh3_1 (w : Word) :
    extractByte (BitVec.signExtend 64 (extractHalfword w 3)) 1 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

attribute [byte_simp] xb_rh1_0 xb_rh1_1 xb_rh1_2 xb_rh1_3 xb_rh1_4 xb_rh1_5 xb_rh1_6 xb_rh1_7
  xb_rh2_0 xb_rh2_1 xb_rh2_2 xb_rh2_3 xb_rh2_4 xb_rh2_5 xb_rh2_6 xb_rh2_7
  xb_rh3_0 xb_rh3_1 xb_rh3_2 xb_rh3_3 xb_rh3_4 xb_rh3_5 xb_rh3_6 xb_rh3_7
  xb_rw0_0 xb_rw0_1 xb_rw0_2 xb_rw0_3 xb_rw0_4 xb_rw0_5 xb_rw0_6 xb_rw0_7
  xb_rw1_0 xb_rw1_1 xb_rw1_2 xb_rw1_3 xb_rw1_4 xb_rw1_5 xb_rw1_6 xb_rw1_7
  xb_lh0_0 xb_lh0_1 xb_lh1_0 xb_lh1_1 xb_lh2_0 xb_lh2_1 xb_lh3_0 xb_lh3_1

end Cases.Zip2005
