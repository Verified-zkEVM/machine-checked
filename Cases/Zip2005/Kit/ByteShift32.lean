import Cases.Zip2005.Kit.ByteKit

/-! Bytes of a word shifted up by 32 (a `u64` assembled from two `u32` halves), at each literal byte
position, for `byte_simp`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem extractByte_shl32_0 (w : Word) : extractByte (w <<< 32) 0 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl32_1 (w : Word) : extractByte (w <<< 32) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl32_2 (w : Word) : extractByte (w <<< 32) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl32_3 (w : Word) : extractByte (w <<< 32) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl32_4 (w : Word) : extractByte (w <<< 32) 4 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shl32_5 (w : Word) : extractByte (w <<< 32) 5 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shl32_6 (w : Word) : extractByte (w <<< 32) 6 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shl32_7 (w : Word) : extractByte (w <<< 32) 7 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

attribute [byte_simp] extractByte_shl32_0 extractByte_shl32_1 extractByte_shl32_2 extractByte_shl32_3 extractByte_shl32_4 extractByte_shl32_5 extractByte_shl32_6 extractByte_shl32_7

end Cases.Zip2005
