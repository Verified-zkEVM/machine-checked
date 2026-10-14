import Cases.Zip2005.Kit.ByteKit

/-! Bytes of a word shifted by whole bytes (`memcpy`'s shifting loops: `(b <<< 8) ||| (a >>> 56)`),
at each literal byte position, for `byte_simp`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem extractByte_shl8_0 (w : Word) : extractByte (w <<< 8) 0 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl8_1 (w : Word) : extractByte (w <<< 8) 1 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shr56_1 (w : Word) : extractByte (w >>> 56) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl8_2 (w : Word) : extractByte (w <<< 8) 2 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shr56_2 (w : Word) : extractByte (w >>> 56) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl8_3 (w : Word) : extractByte (w <<< 8) 3 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shr56_3 (w : Word) : extractByte (w >>> 56) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl8_4 (w : Word) : extractByte (w <<< 8) 4 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shr56_4 (w : Word) : extractByte (w >>> 56) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl8_5 (w : Word) : extractByte (w <<< 8) 5 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shr56_5 (w : Word) : extractByte (w >>> 56) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl8_6 (w : Word) : extractByte (w <<< 8) 6 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shr56_6 (w : Word) : extractByte (w >>> 56) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem extractByte_shl8_7 (w : Word) : extractByte (w <<< 8) 7 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem extractByte_shr56_7 (w : Word) : extractByte (w >>> 56) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

attribute [byte_simp] extractByte_shl8_0 extractByte_shl8_1 extractByte_shr56_1 extractByte_shl8_2 extractByte_shr56_2 extractByte_shl8_3 extractByte_shr56_3 extractByte_shl8_4 extractByte_shr56_4 extractByte_shl8_5 extractByte_shr56_5 extractByte_shl8_6 extractByte_shr56_6 extractByte_shl8_7 extractByte_shr56_7

end Cases.Zip2005
