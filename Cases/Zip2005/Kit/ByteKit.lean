import Cases.Zip2005.Kit.Array32Model
import Cases.Zip2005.Kit.ByteSimpAttr

/-!
# Bytes of words built by byte stores, shifts and masks

Byte-level rewrites for the cells the executor leaves when a function moves bytes around
(`lbu`/`sb`, `srli` + `sb`, `slli` + `or` + `sw`/`sh`): `extractByte` pushed through
`replaceByte`, `|||`, the zero-extensions and truncations, and `word_ext` to compare two words
byte by byte. Each lemma is a bit-level identity.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

/-- Two words with the same eight bytes are equal. -/
theorem word_ext {w v : Word} (h : ∀ k < 8, extractByte w k = extractByte v k) : w = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun b => b.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, show i % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show i / 8 * 8 + i % 8 = i by omega] at this

theorem extractByte_replaceByte_ne (w : Word) (j k : Nat) (b : BitVec 8) (hk : k < 8)
    (h : j ≠ k) : extractByte (replaceByte w j b) k = extractByte w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rw [getLsbD_replaceByte _ _ _ _ (by omega), if_neg (by omega)]

theorem extractByte_zero (k : Nat) : extractByte 0#64 k = 0#8 := by
  simp [extractByte]

theorem extractByte_or (x y : Word) (k : Nat) :
    extractByte (x ||| y) k = extractByte x k ||| extractByte y k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [extractByte, BitVec.getLsbD_or, hi]

theorem extractByte_zext8 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b) k = if k = 0 then b else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  split
  · subst_vars
    simp only [Nat.zero_mul, Nat.zero_add, show i < 64 by omega, decide_true, Bool.true_and]
  · rw [BitVec.getLsbD_of_ge b _ (by omega)]; simp

theorem extractByte_zext8_shl (b : BitVec 8) (m k : Nat) (hm : m < 8) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< (8 * m)) k = if k = m then b else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, hi, decide_true,
    Bool.true_and]
  split
  · subst_vars
    simp [show k * 8 + i < 64 by omega, show ¬ k * 8 + i < 8 * k by omega,
      show k * 8 + i - 8 * k = i by omega, hi]
    intro _; omega
  · by_cases h : k * 8 + i < 8 * m
    · simp [h]
    · rw [BitVec.getLsbD_of_ge b _ (by omega)]; simp

theorem extractByte_zext8_shl8 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< 8) k = if k = 1 then b else 0#8 :=
  extractByte_zext8_shl b 1 k (by decide) hk

theorem extractByte_zext8_shl16 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< 16) k = if k = 2 then b else 0#8 :=
  extractByte_zext8_shl b 2 k (by decide) hk

theorem extractByte_zext8_shl24 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< 24) k = if k = 3 then b else 0#8 :=
  extractByte_zext8_shl b 3 k (by decide) hk

theorem extractByte_zext_trunc32 (w : Word) (k : Nat) (hk : k < 4) :
    extractByte (BitVec.zeroExtend 64 (BitVec.truncate 32 w)) k = extractByte w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  simp [show k * 8 + i < 32 by omega, show k * 8 + i < 64 by omega]

theorem extractByte_zext_trunc16 (w : Word) (k : Nat) (hk : k < 2) :
    extractByte (BitVec.zeroExtend 64 (BitVec.truncate 16 w)) k = extractByte w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  simp [show k * 8 + i < 16 by omega, show k * 8 + i < 64 by omega]

theorem trunc8_eq_extractByte (w : Word) : BitVec.truncate 8 w = extractByte w 0 := by
  simp [extractByte]

theorem trunc8_shr_eq (w : Word) (m : Nat) : BitVec.truncate 8 (w >>> (8 * m)) = extractByte w m := by
  simp [extractByte, Nat.mul_comm]

theorem trunc8_shr8 (w : Word) : BitVec.truncate 8 (w >>> 8) = extractByte w 1 := trunc8_shr_eq w 1
theorem trunc8_shr16 (w : Word) : BitVec.truncate 8 (w >>> 16) = extractByte w 2 := trunc8_shr_eq w 2
theorem trunc8_shr24 (w : Word) : BitVec.truncate 8 (w >>> 24) = extractByte w 3 := trunc8_shr_eq w 3
theorem trunc8_shr32 (w : Word) : BitVec.truncate 8 (w >>> 32) = extractByte w 4 := trunc8_shr_eq w 4
theorem trunc8_shr40 (w : Word) : BitVec.truncate 8 (w >>> 40) = extractByte w 5 := trunc8_shr_eq w 5
theorem trunc8_shr48 (w : Word) : BitVec.truncate 8 (w >>> 48) = extractByte w 6 := trunc8_shr_eq w 6
theorem trunc8_shr56 (w : Word) : BitVec.truncate 8 (w >>> 56) = extractByte w 7 := trunc8_shr_eq w 7

theorem extractByte_shr0 (w : Word) (m : Nat) : extractByte (w >>> (8 * m)) 0 = extractByte w m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  congr 1; omega

theorem extractByte_shr8 (w : Word) : extractByte (w >>> 8) 0 = extractByte w 1 := extractByte_shr0 w 1
theorem extractByte_shr16 (w : Word) : extractByte (w >>> 16) 0 = extractByte w 2 := extractByte_shr0 w 2
theorem extractByte_shr24 (w : Word) : extractByte (w >>> 24) 0 = extractByte w 3 := extractByte_shr0 w 3
theorem extractByte_shr32 (w : Word) : extractByte (w >>> 32) 0 = extractByte w 4 := extractByte_shr0 w 4
theorem extractByte_shr40 (w : Word) : extractByte (w >>> 40) 0 = extractByte w 5 := extractByte_shr0 w 5
theorem extractByte_shr48 (w : Word) : extractByte (w >>> 48) 0 = extractByte w 6 := extractByte_shr0 w 6
theorem extractByte_shr56 (w : Word) : extractByte (w >>> 56) 0 = extractByte w 7 := extractByte_shr0 w 7

theorem extractByte_one0 : extractByte (1#64) 0 = 1#8 := by decide
theorem extractByte_256_0 : extractByte (256#64) 0 = 0#8 := by decide
theorem extractByte_256_1 : extractByte (256#64) 1 = 1#8 := by decide

theorem extractByte_replaceHalfword_lo (w : Word) (h : BitVec 16) (k : Nat) (hk : k < 2) :
    extractByte (replaceHalfword w 0 h) k = extractByte (BitVec.zeroExtend 64 h) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, Nat.zero_mul]
  have h16 : ∀ j < 64, (0xFFFF#64).getLsbD j = decide (j < 16) := by decide
  rw [h16 _ (by omega)]
  simp [show k * 8 + i < 16 by omega, show k * 8 + i < 64 by omega]

theorem extractByte_replaceHalfword_hi (w : Word) (h : BitVec 16) (k : Nat) (hk2 : 2 ≤ k) (hk : k < 8) :
    extractByte (replaceHalfword w 0 h) k = extractByte w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceHalfword, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, Nat.zero_mul]
  have h16 : ∀ j < 64, (0xFFFF#64).getLsbD j = decide (j < 16) := by decide
  rw [h16 _ (by omega)]
  simp [show ¬ k * 8 + i < 16 by omega, show k * 8 + i < 64 by omega, BitVec.getLsbD_of_ge h _ (show 16 ≤ k * 8 + i by omega)]

attribute [byte_simp] word8 arr32W someW inByte extractByte_replaceByte extractByte_replaceByte_ne
  extractByte_or extractByte_zext8 extractByte_zext8_shl8 extractByte_zext8_shl16
  extractByte_zext8_shl24 extractByte_zext_trunc32 extractByte_zext_trunc16 trunc8_eq_extractByte
  extractByte_zero extractByte_one0 extractByte_256_0 extractByte_256_1
  extractByte_replaceHalfword_lo extractByte_replaceHalfword_hi extractByte_shr8 extractByte_shr16 extractByte_shr24
  extractByte_shr32 extractByte_shr40 extractByte_shr48 extractByte_shr56 List.getElem!_cons_zero
  List.getElem!_cons_succ BitVec.zero_or BitVec.or_zero Nat.reduceAdd Nat.reduceMul Nat.reduceSub
  Nat.reduceDiv Nat.reduceMod Nat.reduceEqDiff Nat.reduceLT
attribute [byte_simp ↓] reduceIte

/-- `Ok(Some(_))`'s two tag bytes. -/
theorem someW_tag0 (O W : List Word) (r : Nat) : extractByte (someW O W r)[0]! 0 = 0#8 := by
  simp (disch := decide) only [byte_simp]

theorem someW_tag1 (O W : List Word) (r : Nat) : extractByte (someW O W r)[0]! 1 = 1#8 := by
  simp (disch := decide) only [byte_simp]

end Cases.Zip2005
