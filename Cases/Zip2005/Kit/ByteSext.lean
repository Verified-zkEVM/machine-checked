import Cases.Zip2005.Kit.ByteKit

/-! The low four bytes of a sign-extended 32-bit value (`sext.w`, `addw`): those of the value.
For `byte_simp`; a `sw` stores only these. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem xb_sext32_0 (x : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 32 x)) 0 = extractByte x 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_sext32_1 (x : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 32 x)) 1 = extractByte x 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_sext32_2 (x : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 32 x)) 2 = extractByte x 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_sext32_3 (x : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 32 x)) 3 = extractByte x 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem trunc16_zext64 (h : BitVec 16) : BitVec.truncate 16 (BitVec.zeroExtend 64 h) = h := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
  simp [hi, show i < 64 by omega]

theorem xb_sext16_0 (x : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 16 x)) 0 = extractByte x 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem xb_sext16_1 (x : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 16 x)) 1 = extractByte x 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

attribute [byte_simp] xb_sext32_0 xb_sext32_1 xb_sext32_2 xb_sext32_3 trunc16_zext64 xb_sext16_0 xb_sext16_1


theorem trunc32_sext64 (x : BitVec 32) : BitVec.truncate 32 (BitVec.signExtend 64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 by omega]

theorem trunc16_sext64 (x : BitVec 16) : BitVec.truncate 16 (BitVec.signExtend 64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 by omega]

theorem trunc8_sext64 (x : BitVec 8) : BitVec.truncate 8 (BitVec.signExtend 64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 by omega]

attribute [byte_simp] trunc32_sext64 trunc16_sext64 trunc8_sext64


/-! A 32-bit word moved whole (`lw`/`sw` without sign extension in the model). -/

theorem xb_rw0_xw0_0 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 0 = extractByte v 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_xw0_1 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 1 = extractByte v 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_xw0_2 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 2 = extractByte v 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_xw0_3 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 3 = extractByte v 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_xw0_4 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 4 = extractByte w 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_xw0_5 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 5 = extractByte w 5 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_xw0_6 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 6 = extractByte w 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem xb_rw0_xw0_7 (w v : Word) :
    extractByte (replaceWord32 w 0 (extractWord32 v 0)) 7 = extractByte w 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractWord32, replaceWord32, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

attribute [byte_simp] xb_rw0_xw0_0 xb_rw0_xw0_1 xb_rw0_xw0_2 xb_rw0_xw0_3 xb_rw0_xw0_4 xb_rw0_xw0_5 xb_rw0_xw0_6 xb_rw0_xw0_7

end Cases.Zip2005
