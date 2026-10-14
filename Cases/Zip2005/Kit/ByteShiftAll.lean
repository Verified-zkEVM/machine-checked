import Cases.Zip2005.Kit.ByteShift
import Cases.Zip2005.Kit.ByteShift32

/-! Bytes of a word shifted by any whole number of bytes, at each literal byte position (the
shifting loops of `memcpy` for every destination misalignment), for `byte_simp`. The shifts
already in `Proof/Kit/ByteKit.lean`, `Proof/Kit/ByteShift.lean` and `Proof/Kit/ByteShift32.lean` are not
repeated. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem xb_shr8_1 (w : Word) : extractByte (w >>> 8) 1 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr8_2 (w : Word) : extractByte (w >>> 8) 2 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr8_3 (w : Word) : extractByte (w >>> 8) 3 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr8_4 (w : Word) : extractByte (w >>> 8) 4 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr8_5 (w : Word) : extractByte (w >>> 8) 5 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr8_6 (w : Word) : extractByte (w >>> 8) 6 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr8_7 (w : Word) : extractByte (w >>> 8) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl16_0 (w : Word) : extractByte (w <<< 16) 0 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl16_1 (w : Word) : extractByte (w <<< 16) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr16_1 (w : Word) : extractByte (w >>> 16) 1 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl16_2 (w : Word) : extractByte (w <<< 16) 2 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr16_2 (w : Word) : extractByte (w >>> 16) 2 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl16_3 (w : Word) : extractByte (w <<< 16) 3 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr16_3 (w : Word) : extractByte (w >>> 16) 3 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl16_4 (w : Word) : extractByte (w <<< 16) 4 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr16_4 (w : Word) : extractByte (w >>> 16) 4 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl16_5 (w : Word) : extractByte (w <<< 16) 5 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr16_5 (w : Word) : extractByte (w >>> 16) 5 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl16_6 (w : Word) : extractByte (w <<< 16) 6 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr16_6 (w : Word) : extractByte (w >>> 16) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl16_7 (w : Word) : extractByte (w <<< 16) 7 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr16_7 (w : Word) : extractByte (w >>> 16) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl24_0 (w : Word) : extractByte (w <<< 24) 0 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl24_1 (w : Word) : extractByte (w <<< 24) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr24_1 (w : Word) : extractByte (w >>> 24) 1 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl24_2 (w : Word) : extractByte (w <<< 24) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr24_2 (w : Word) : extractByte (w >>> 24) 2 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl24_3 (w : Word) : extractByte (w <<< 24) 3 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr24_3 (w : Word) : extractByte (w >>> 24) 3 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl24_4 (w : Word) : extractByte (w <<< 24) 4 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr24_4 (w : Word) : extractByte (w >>> 24) 4 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl24_5 (w : Word) : extractByte (w <<< 24) 5 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr24_5 (w : Word) : extractByte (w >>> 24) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl24_6 (w : Word) : extractByte (w <<< 24) 6 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr24_6 (w : Word) : extractByte (w >>> 24) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl24_7 (w : Word) : extractByte (w <<< 24) 7 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr24_7 (w : Word) : extractByte (w >>> 24) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr32_1 (w : Word) : extractByte (w >>> 32) 1 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr32_2 (w : Word) : extractByte (w >>> 32) 2 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr32_3 (w : Word) : extractByte (w >>> 32) 3 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shr32_4 (w : Word) : extractByte (w >>> 32) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr32_5 (w : Word) : extractByte (w >>> 32) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr32_6 (w : Word) : extractByte (w >>> 32) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr32_7 (w : Word) : extractByte (w >>> 32) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl40_0 (w : Word) : extractByte (w <<< 40) 0 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl40_1 (w : Word) : extractByte (w <<< 40) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr40_1 (w : Word) : extractByte (w >>> 40) 1 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl40_2 (w : Word) : extractByte (w <<< 40) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr40_2 (w : Word) : extractByte (w >>> 40) 2 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl40_3 (w : Word) : extractByte (w <<< 40) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr40_3 (w : Word) : extractByte (w >>> 40) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl40_4 (w : Word) : extractByte (w <<< 40) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr40_4 (w : Word) : extractByte (w >>> 40) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl40_5 (w : Word) : extractByte (w <<< 40) 5 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr40_5 (w : Word) : extractByte (w >>> 40) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl40_6 (w : Word) : extractByte (w <<< 40) 6 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr40_6 (w : Word) : extractByte (w >>> 40) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl40_7 (w : Word) : extractByte (w <<< 40) 7 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr40_7 (w : Word) : extractByte (w >>> 40) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl48_0 (w : Word) : extractByte (w <<< 48) 0 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl48_1 (w : Word) : extractByte (w <<< 48) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr48_1 (w : Word) : extractByte (w >>> 48) 1 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_shl48_2 (w : Word) : extractByte (w <<< 48) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr48_2 (w : Word) : extractByte (w >>> 48) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl48_3 (w : Word) : extractByte (w <<< 48) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr48_3 (w : Word) : extractByte (w >>> 48) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl48_4 (w : Word) : extractByte (w <<< 48) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr48_4 (w : Word) : extractByte (w >>> 48) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl48_5 (w : Word) : extractByte (w <<< 48) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shr48_5 (w : Word) : extractByte (w >>> 48) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl48_6 (w : Word) : extractByte (w <<< 48) 6 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr48_6 (w : Word) : extractByte (w >>> 48) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl48_7 (w : Word) : extractByte (w <<< 48) 7 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_shr48_7 (w : Word) : extractByte (w >>> 48) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_0 (w : Word) : extractByte (w <<< 56) 0 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_1 (w : Word) : extractByte (w <<< 56) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_2 (w : Word) : extractByte (w <<< 56) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_3 (w : Word) : extractByte (w <<< 56) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_4 (w : Word) : extractByte (w <<< 56) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_5 (w : Word) : extractByte (w <<< 56) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_6 (w : Word) : extractByte (w <<< 56) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  interval_cases i <;> simp

theorem xb_shl56_7 (w : Word) : extractByte (w <<< 56) 7 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

attribute [byte_simp] xb_shr8_1 xb_shr8_2 xb_shr8_3 xb_shr8_4 xb_shr8_5 xb_shr8_6 xb_shr8_7 xb_shl16_0 xb_shl16_1 xb_shr16_1 xb_shl16_2 xb_shr16_2 xb_shl16_3 xb_shr16_3 xb_shl16_4 xb_shr16_4 xb_shl16_5 xb_shr16_5 xb_shl16_6 xb_shr16_6 xb_shl16_7 xb_shr16_7 xb_shl24_0 xb_shl24_1 xb_shr24_1 xb_shl24_2 xb_shr24_2 xb_shl24_3 xb_shr24_3 xb_shl24_4 xb_shr24_4 xb_shl24_5 xb_shr24_5 xb_shl24_6 xb_shr24_6 xb_shl24_7 xb_shr24_7 xb_shr32_1 xb_shr32_2 xb_shr32_3 xb_shr32_4 xb_shr32_5 xb_shr32_6 xb_shr32_7 xb_shl40_0 xb_shl40_1 xb_shr40_1 xb_shl40_2 xb_shr40_2 xb_shl40_3 xb_shr40_3 xb_shl40_4 xb_shr40_4 xb_shl40_5 xb_shr40_5 xb_shl40_6 xb_shr40_6 xb_shl40_7 xb_shr40_7 xb_shl48_0 xb_shl48_1 xb_shr48_1 xb_shl48_2 xb_shr48_2 xb_shl48_3 xb_shr48_3 xb_shl48_4 xb_shr48_4 xb_shl48_5 xb_shr48_5 xb_shl48_6 xb_shr48_6 xb_shl48_7 xb_shr48_7 xb_shl56_0 xb_shl56_1 xb_shl56_2 xb_shl56_3 xb_shl56_4 xb_shl56_5 xb_shl56_6 xb_shl56_7

end Cases.Zip2005
