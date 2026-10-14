import Cases.Zip2005.Witness.NextU64
import Cases.Zip2005.Witness.NextU32
import Cases.Zip2005.Witness.BoolReader
import Cases.Zip2005.Kit.ByteSimpPre

/-! The bytes of the reader results the visitor stores (`u64r1`, a zero-extended `u32r1`, the
`bool` byte), for `byte_simp`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem xb_u32r1_0 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 0 = extractByte W[0]! 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem xb_u32r1_1 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 1 = extractByte W[0]! 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem xb_u32r1_2 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 2 = extractByte W[0]! 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem xb_u32r1_3 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 3 = extractByte W[0]! 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem xb_u32r1_4 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem xb_u32r1_5 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem xb_u32r1_6 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem xb_u32r1_7 (W : List Word) :
    extractByte (BitVec.zeroExtend 64 (u32r1 W)) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [u32r1, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  interval_cases i <;> simp

attribute [byte_simp] u64r1 boolByte xb_u32r1_0 xb_u32r1_1 xb_u32r1_2 xb_u32r1_3 xb_u32r1_4 xb_u32r1_5 xb_u32r1_6 xb_u32r1_7


/-! Bytes of a zero-extended halfword read (`lhu`). -/

theorem xb_zhw0_0 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 0 = extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw0_1 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 1 = extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw0_2 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw0_3 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw0_4 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw0_5 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw0_6 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw0_7 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 0)) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_0 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 0 = extractByte w 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_1 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 1 = extractByte w 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_2 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_3 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_4 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_5 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_6 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw1_7 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 1)) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_0 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 0 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_1 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 1 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_2 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_3 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_4 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_5 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_6 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw2_7 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 2)) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_0 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 0 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_1 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 1 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_2 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_3 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_4 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_5 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_6 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem xb_zhw3_7 (w : Word) :
    extractByte (BitVec.zeroExtend 64 (extractHalfword w 3)) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

attribute [byte_simp] xb_zhw0_0 xb_zhw0_1 xb_zhw0_2 xb_zhw0_3 xb_zhw0_4 xb_zhw0_5 xb_zhw0_6 xb_zhw0_7 xb_zhw1_0 xb_zhw1_1 xb_zhw1_2 xb_zhw1_3 xb_zhw1_4 xb_zhw1_5 xb_zhw1_6 xb_zhw1_7 xb_zhw2_0 xb_zhw2_1 xb_zhw2_2 xb_zhw2_3 xb_zhw2_4 xb_zhw2_5 xb_zhw2_6 xb_zhw2_7 xb_zhw3_0 xb_zhw3_1 xb_zhw3_2 xb_zhw3_3 xb_zhw3_4 xb_zhw3_5 xb_zhw3_6 xb_zhw3_7

end Cases.Zip2005
