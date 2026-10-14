import Cases.Zip2005.Sinsemilla.PadKit

/-!
# One step of a byte-slice bit cursor (`BitValIter<u8, Lsb0>`)

The head is a byte index `0 … 7`; a step takes `head + 1`, carries `(head + 1) >> 3` into the
byte pointer and keeps `(head + 1) & 7`. The bit is `(byte >> head) & 1`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

/-- The head byte after one step: `(r + 1) % 8`. -/
theorem head8Next (r : Nat) (hr : r < 8) :
    BitVec.truncate 8 ((BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 255#64) + 1#64 &&& 7#64) =
      BitVec.ofNat 8 ((r + 1) % 8) := by
  interval_cases r <;> decide

/-- The byte pointer's step: `1` when the head wraps, else `0`. -/
theorem ptr8Step (r : Nat) (hr : r < 8) :
    ((BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 255#64) + 1#64) >>> 3 =
      if r = 7 then 1#64 else 0#64 := by
  interval_cases r <;> decide

/-- The cursor's byte pointer after one step from bit `k`: `base + (k + 1) / 8`. -/
theorem ptr8Next (sp c : Word) (k : Nat) :
    sp + (c + BitVec.ofNat 64 (k / 8)) + (if k % 8 = 7 then 1#64 else 0#64) =
      sp + c + BitVec.ofNat 64 ((k + 1) / 8) := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]
  congr 2
  by_cases h : k % 8 = 7
  · rw [if_pos h, ← BitVec.ofNat_add, show k / 8 + 1 = (k + 1) / 8 by omega]
  · rw [if_neg h, BitVec.add_zero, show k / 8 = (k + 1) / 8 by omega]

/-- The shift amount `srl` takes from the head byte. -/
theorem shift8Amt (r : Nat) (hr : r < 8) :
    (BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 255#64).toNat % 64 = r := by
  interval_cases r <;> decide

/-- Bit `h` of byte `b` of a word is bit `8 b + h` of the word. -/
theorem byteBit (w : Word) (b h : Nat) (hh : h < 8) :
    (BitVec.zeroExtend 64 (extractByte w b) >>> h) &&& 1#64 = (w >>> (8 * b + h)) &&& 1#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, extractByte, BitVec.getLsbD_one]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp only [Nat.add_zero, decide_true, Bool.and_true, hh,
      show b * 8 + h = 8 * b + h by omega, show h < 64 by omega, Bool.true_and]
  · simp [Nat.pos_iff_ne_zero.mp hpos]

/-- The bit a step yields: byte `k / 8` of the message (word `k / 64`, byte `k / 8 % 8`)
shifted by `k % 8`, as `wordsBit`. -/
theorem bit8Next (A : List Word) (k : Nat) :
    (BitVec.zeroExtend 64 (extractByte A[k / 8 / 8]! (k / 8 % 8)) >>>
        ((BitVec.zeroExtend 64 (BitVec.ofNat 8 (k % 8)) &&& 255#64).toNat % 64)) &&& 1#64 =
      bw (wordsBit A k) := by
  rw [shift8Amt (k % 8) (Nat.mod_lt _ (by decide)), byteBit _ _ _ (Nat.mod_lt _ (by decide)), show k / 8 / 8 = k / 64 by omega,
    show 8 * (k / 8 % 8) + k % 8 = k % 64 by omega, wordsBit]
  exact bitVal _

/-- The shift amount as `next` masks it again (`& 7`). -/
theorem shift8Amt7 (r : Nat) (hr : r < 8) :
    ((BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 255#64) &&& 7#64).toNat % 64 = r := by
  interval_cases r <;> decide

/-- `bit8Next` with the shift amount masked by `7`. -/
theorem bit8Next7 (A : List Word) (k : Nat) :
    (BitVec.zeroExtend 64 (extractByte A[k / 8 / 8]! (k / 8 % 8)) >>>
        (((BitVec.zeroExtend 64 (BitVec.ofNat 8 (k % 8)) &&& 255#64) &&& 7#64).toNat % 64)) &&& 1#64 =
      bw (wordsBit A k) := by
  rw [shift8Amt7 (k % 8) (Nat.mod_lt _ (by decide)), byteBit _ _ _ (Nat.mod_lt _ (by decide)),
    show k / 8 / 8 = k / 64 by omega, show 8 * (k / 8 % 8) + k % 8 = k % 64 by omega, wordsBit]
  exact bitVal _

/-- `head8Next` without the `& 255` (the head reloaded as a byte). -/
theorem head8Next' (r : Nat) (hr : r < 8) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.ofNat 8 r) + 1#64 &&& 7#64) =
      BitVec.ofNat 8 ((r + 1) % 8) := by
  interval_cases r <;> decide

/-- `ptr8Step` without the `& 255`. -/
theorem ptr8Step' (r : Nat) (hr : r < 8) :
    (BitVec.zeroExtend 64 (BitVec.ofNat 8 r) + 1#64) >>> 3 = if r = 7 then 1#64 else 0#64 := by
  interval_cases r <;> decide

/-- `shift8Amt7` without the `& 255`. -/
theorem shift8Amt7' (r : Nat) (hr : r < 8) :
    (BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 7#64).toNat % 64 = r := by
  interval_cases r <;> decide

/-- `bit8Next7` without the `& 255`. -/
theorem bit8Next7' (A : List Word) (k : Nat) :
    (BitVec.zeroExtend 64 (extractByte A[k / 8 / 8]! (k / 8 % 8)) >>>
        ((BitVec.zeroExtend 64 (BitVec.ofNat 8 (k % 8)) &&& 7#64).toNat % 64)) &&& 1#64 =
      bw (wordsBit A k) := by
  rw [shift8Amt7' (k % 8) (Nat.mod_lt _ (by decide)), byteBit _ _ _ (Nat.mod_lt _ (by decide)),
    show k / 8 / 8 = k / 64 by omega, show 8 * (k / 8 % 8) + k % 8 = k % 64 by omega, wordsBit]
  exact bitVal _

/-- The exhaustion test of a cursor at its end, heads equal: `1`. -/
theorem seqz_self (p : Word) :
    (if ((p ^^^ p) ||| 0#64).ult 1#64 = true then 1#64 else 0#64) = 1#64 := by
  simp

/-- The padding countdown. -/
theorem decNext (l : Nat) (hl : 1 ≤ l) (hl' : l < 2 ^ 64) :
    BitVec.ofNat 64 l + 18446744073709551615#64 = BitVec.ofNat 64 (l - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Bn.toNat_ofNat', Bn.toNat_ofNat']
  simp only [BitVec.toNat_ofNat]
  omega

/-- An eighteen-word list by its cells. -/
theorem list18_cells (I : List Word) (h : I.length = 18) :
    I = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!, I[12]!,
      I[13]!, I[14]!, I[15]!, I[16]!, I[17]!] := by
  match I, h with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

/-! ## Pointers reassembled from their stored bytes, halfwords and 32-bit words -/

/-- `bytes_word` over the bytes as the executor folds them out of the stores. -/
theorem bytes_word_trunc (p : Word) :
    ((BitVec.zeroExtend 64 (BitVec.truncate 8 (p >>> 56)) <<< 24 |||
        BitVec.zeroExtend 64 (BitVec.truncate 8 (p >>> 48)) <<< 16) |||
      (BitVec.zeroExtend 64 (BitVec.truncate 8 (p >>> 40)) <<< 8 |||
        BitVec.zeroExtend 64 (BitVec.truncate 8 (p >>> 32)))) <<< 32 |||
    ((BitVec.zeroExtend 64 (BitVec.truncate 8 (p >>> 24)) <<< 24 |||
        BitVec.zeroExtend 64 (BitVec.truncate 8 (p >>> 16)) <<< 16) |||
      (BitVec.zeroExtend 64 (BitVec.truncate 8 (p >>> 8)) <<< 8 |||
        BitVec.zeroExtend 64 (BitVec.truncate 8 p))) = p := by
  rw [trunc8_shr56, trunc8_shr48, trunc8_shr40, trunc8_shr32, trunc8_shr24, trunc8_shr16,
    trunc8_shr8, trunc8_eq_extractByte]
  exact bytes_word p

theorem getLsbD_trunc16_zext (x : Word) (i : Nat) :
    (BitVec.zeroExtend 64 (BitVec.truncate 16 x)).getLsbD i = (decide (i < 16) && x.getLsbD i) := by
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
  by_cases h : i < 16
  · simp [h, show i < 64 by omega]
  · simp [h]

theorem getLsbD_trunc32_zext (x : Word) (i : Nat) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 x)).getLsbD i = (decide (i < 32) && x.getLsbD i) := by
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth]
  by_cases h : i < 32
  · simp [h, show i < 64 by omega]
  · simp [h]

/-- A pointer stored as four halfwords (`sh`) and read back by four `lhu`. -/
theorem halfwords_word_trunc (p : Word) :
    (BitVec.zeroExtend 64 (BitVec.truncate 16 (p >>> 48)) <<< 48 |||
        BitVec.zeroExtend 64 (BitVec.truncate 16 (p >>> 32)) <<< 32) |||
      (BitVec.zeroExtend 64 (BitVec.truncate 16 (p >>> 16)) <<< 16 |||
        BitVec.zeroExtend 64 (BitVec.truncate 16 p)) = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, getLsbD_trunc16_zext,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 16 with h1 | h1
  · have := h1
    simp [h1, show ¬ 48 ≤ i by omega, show ¬ 32 ≤ i by omega]
  rcases Nat.lt_or_ge i 32 with h2 | h2
  · simp [h2, show ¬ 48 ≤ i by omega, show i - 16 < 16 by omega,
      show 16 + (i - 16) = i by omega, show ¬ i < 16 by omega]
  rcases Nat.lt_or_ge i 48 with h3 | h3
  · simp [h3, show i - 32 < 16 by omega, show ¬ i - 16 < 16 by omega,
      show 32 + (i - 32) = i by omega, show ¬ i < 16 by omega, show ¬ i < 32 by omega]
  · simp [show i - 48 < 16 by omega, show ¬ i - 32 < 16 by omega, show ¬ i - 16 < 16 by omega,
      show 48 + (i - 48) = i by omega, show ¬ i < 16 by omega, show ¬ i < 32 by omega,
      show ¬ i < 48 by omega]

/-- A pointer stored as two 32-bit words (`sw`) and read back by two `lwu`. -/
theorem words32_word_trunc (p : Word) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (p >>> 32)) <<< 32 |||
      BitVec.zeroExtend 64 (BitVec.truncate 32 p) = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, getLsbD_trunc32_zext,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h1 : i < 32
  · simp [h1]
  · simp [h1, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]

/-! ## Bytes through halfword and 32-bit stores elsewhere in the word -/

theorem getLsbD_replaceHalfword (w : Word) (pos : Nat) (hw : BitVec 16) (i : Nat) (hi : i < 64) :
    (replaceHalfword w pos hw).getLsbD i =
      if pos * 16 ≤ i ∧ i < pos * 16 + 16 then hw.getLsbD (i - pos * 16) else w.getLsbD i := by
  have ff : ∀ k < 64, (0xFFFF#64).getLsbD k = decide (k < 16) := by decide
  unfold replaceHalfword
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases h : pos * 16 ≤ i ∧ i < pos * 16 + 16
  · rw [if_pos h, ff _ (by omega)]
    have h1 : ¬ i < pos * 16 := by omega
    have h2 : i - pos * 16 < 16 := by omega
    have h3 : i - pos * 16 < 64 := by omega
    simp [h1, h2, h3]
  · rw [if_neg h]
    by_cases h1 : i < pos * 16
    · simp [h1]
    · have h2 : ¬ i - pos * 16 < 16 := by omega
      rw [ff _ (by omega), BitVec.getLsbD_of_ge hw _ (by omega)]
      simp [h1, h2]

theorem getLsbD_replaceWord32 (w : Word) (pos : Nat) (v : BitVec 32) (i : Nat) (hi : i < 64) :
    (replaceWord32 w pos v).getLsbD i =
      if pos * 32 ≤ i ∧ i < pos * 32 + 32 then v.getLsbD (i - pos * 32) else w.getLsbD i := by
  have ff : ∀ k < 64, (0xFFFFFFFF#64).getLsbD k = decide (k < 32) := by decide
  unfold replaceWord32
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases h : pos * 32 ≤ i ∧ i < pos * 32 + 32
  · rw [if_pos h, ff _ (by omega)]
    have h1 : ¬ i < pos * 32 := by omega
    have h2 : i - pos * 32 < 32 := by omega
    have h3 : i - pos * 32 < 64 := by omega
    simp [h1, h2, h3]
  · rw [if_neg h]
    by_cases h1 : i < pos * 32
    · simp [h1]
    · have h2 : ¬ i - pos * 32 < 32 := by omega
      rw [ff _ (by omega), BitVec.getLsbD_of_ge v _ (by omega)]
      simp [h1, h2]

theorem extractByte_replaceHalfword_ne (w : Word) (j k : Nat) (h : BitVec 16) (hk : k < 8)
    (hne : k / 2 ≠ j) : extractByte (replaceHalfword w j h) k = extractByte w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rw [getLsbD_replaceHalfword _ _ _ _ (by omega), if_neg (by omega)]

theorem extractByte_replaceWord32_ne (w : Word) (j k : Nat) (h : BitVec 32) (hk : k < 8)
    (hne : k / 4 ≠ j) : extractByte (replaceWord32 w j h) k = extractByte w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rw [getLsbD_replaceWord32 _ _ _ _ (by omega), if_neg (by omega)]

/-! ## Branch refutations -/

/-- Two literal offsets from one base differ. -/
theorem add_lit_ne (sp : Word) (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hab : a ≠ b) :
    sp + BitVec.ofNat 64 a ≠ sp + BitVec.ofNat 64 b := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have hs := sp.isLt
  omega

theorem eq_of_xor_eq_zero {p e : Word} (h : p ^^^ e = 0#64) : p = e := by
  have := congrArg (· ^^^ e) h
  simpa [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] using this

/-- `seqz` of a cursor compared with its end, the heads equal: `0` when the pointers differ. -/
theorem seqz_xor0 (p e : Word) (hpe : p ≠ e) :
    (if ((p ^^^ e) ||| 0#64).ult 1#64 = true then 1#64 else 0#64) = 0#64 := by
  rw [BitVec.or_zero, if_neg]
  intro h
  have h1 := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp h)
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  exact hpe (eq_of_xor_eq_zero (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)))

/-- A byte inside a stored halfword: that byte of the halfword. -/
theorem extractByte_replaceHalfword_in (w : Word) (j k : Nat) (hw : BitVec 16) (hk8 : k < 8)
    (hk : 2 * j ≤ k ∧ k < 2 * j + 2) :
    extractByte (replaceHalfword w j hw) k = extractByte (BitVec.zeroExtend 64 hw) (k - 2 * j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rw [getLsbD_replaceHalfword _ _ _ _ (by omega), if_pos (by omega)]
  simp only [show (k - 2 * j) * 8 + i < 64 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-- A byte inside a stored 32-bit word: that byte of the word. -/
theorem extractByte_replaceWord32_in (w : Word) (j k : Nat) (v : BitVec 32) (hk8 : k < 8)
    (hk : 4 * j ≤ k ∧ k < 4 * j + 4) :
    extractByte (replaceWord32 w j v) k = extractByte (BitVec.zeroExtend 64 v) (k - 4 * j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  rw [getLsbD_replaceWord32 _ _ _ _ (by omega), if_pos (by omega)]
  simp only [show (k - 4 * j) * 8 + i < 64 by omega, decide_true, Bool.true_and]
  congr 1; omega

end Cases.Zip2005
