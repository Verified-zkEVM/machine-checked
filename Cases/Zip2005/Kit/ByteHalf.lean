import Cases.Zip2005.Kit.ByteKit

/-! A halfword moved by `lh`/`sh` (`extractHalfword`, sign-extended, truncated and sign-extended
again): its two bytes, for `byte_simp`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem extractByte_lh_sh_0 (w : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 16 (BitVec.signExtend 64 (extractHalfword w 0)))) 0 =
      extractByte w 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem extractByte_lh_sh_1 (w : Word) :
    extractByte (BitVec.signExtend 64 (BitVec.truncate 16 (BitVec.signExtend 64 (extractHalfword w 0)))) 1 =
      extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, extractHalfword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

attribute [byte_simp] extractByte_lh_sh_0 extractByte_lh_sh_1

end Cases.Zip2005
