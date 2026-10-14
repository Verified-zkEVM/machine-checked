import Cases.Zip2005.Sinsemilla.SinsemillaModel
import Cases.Zip2005.Sinsemilla.Lebs2ipK
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Field.Cells4

/-!
# Sinsemilla's loop body against the chunk model

The guest loads ten message bytes (`lbu`), assembles eight of them into a doubleword and two into
a halfword, and calls `lebs2ip_k` on that pair: for `0`/`1` bytes the result is the chunk value
`chunkVal`. It then reads the generator table at `64 · m`: the eight words `T[8 m], …, T[8 m + 7]`
(`sEntryW`). The two `incomplete_add`s step the tagged accumulator as `sinStep`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- Eight bytes as the compiler assembles a little-endian doubleword from `lbu`s. -/
def asm8 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) : Word :=
  ((BitVec.zeroExtend 64 x7 <<< 24 ||| BitVec.zeroExtend 64 x6 <<< 16) |||
      (BitVec.zeroExtend 64 x5 <<< 8 ||| BitVec.zeroExtend 64 x4)) <<< 32 |||
    ((BitVec.zeroExtend 64 x3 <<< 24 ||| BitVec.zeroExtend 64 x2 <<< 16) |||
      (BitVec.zeroExtend 64 x1 <<< 8 ||| BitVec.zeroExtend 64 x0))

/-- Two bytes in the low halfword of a word, the rest of it whatever was there. -/
def asm2 (A : Word) (x8 x9 : BitVec 8) : Word :=
  replaceHalfword A 0 (BitVec.truncate 16 (BitVec.zeroExtend 64 x9 <<< 8 ||| BitVec.zeroExtend 64 x8))

theorem extractByte_asm8 (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 0 = x0 ∧ extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 1 = x1 ∧
    extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 2 = x2 ∧ extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 3 = x3 ∧
    extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 4 = x4 ∧ extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 5 = x5 ∧
    extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 6 = x6 ∧ extractByte (asm8 x0 x1 x2 x3 x4 x5 x6 x7) 7 = x7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [asm8, extractByte, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.truncate_eq_setWidth,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    interval_cases i <;> simp

theorem extractByte_asm2 (A : Word) (x8 x9 : BitVec 8) :
    extractByte (asm2 A x8 x9) 0 = x8 ∧ extractByte (asm2 A x8 x9) 1 = x9 := by
  have ff : ∀ k < 64, (~~~(0xFFFF#64 <<< (0 * 16))).getLsbD k = decide (16 ≤ k) := by decide
  refine ⟨?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [asm2, extractByte, replaceHalfword, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    rw [ff _ (by omega)]
    interval_cases i <;> simp

/-- `lebs2ipK` on the assembled bytes, as a function of the bytes. -/
def lebs2ipBits (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : BitVec 8) : Word :=
  ((BitVec.zeroExtend 64 x9 <<< 9) ||| (BitVec.zeroExtend 64 x8 <<< 8)) |||
    ((((BitVec.zeroExtend 64 x7 <<< 7) + (BitVec.zeroExtend 64 x6 <<< 6)) +
        ((((BitVec.zeroExtend 64 x1 <<< 1) ||| BitVec.zeroExtend 64 x0) |||
            ((BitVec.zeroExtend 64 x2 <<< 2) ||| (BitVec.zeroExtend 64 x3 <<< 3))) |||
          ((BitVec.zeroExtend 64 x4 <<< 4) ||| (BitVec.zeroExtend 64 x5 <<< 5)))) &&&
      255#64)

theorem lebs2ipK_asm (A : Word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : BitVec 8) :
    lebs2ipK (asm8 x0 x1 x2 x3 x4 x5 x6 x7) (asm2 A x8 x9) = lebs2ipBits x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := extractByte_asm8 x0 x1 x2 x3 x4 x5 x6 x7
  obtain ⟨f0, f1⟩ := extractByte_asm2 A x8 x9
  unfold lebs2ipK lebs2ipBits
  rw [e0, e1, e2, e3, e4, e5, e6, e7, f0, f1]

/-- The chunk value of ten bits. -/
def bitsVal (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : BitVec 8) : Nat :=
  x0.toNat + 2 * x1.toNat + 4 * x2.toNat + 8 * x3.toNat + 16 * x4.toNat + 32 * x5.toNat +
    64 * x6.toNat + 128 * x7.toNat + 256 * x8.toNat + 512 * x9.toNat

theorem lebs2ipBits_val (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : BitVec 8)
    (h0 : x0 = 0#8 ∨ x0 = 1#8) (h1 : x1 = 0#8 ∨ x1 = 1#8) (h2 : x2 = 0#8 ∨ x2 = 1#8)
    (h3 : x3 = 0#8 ∨ x3 = 1#8) (h4 : x4 = 0#8 ∨ x4 = 1#8) (h5 : x5 = 0#8 ∨ x5 = 1#8)
    (h6 : x6 = 0#8 ∨ x6 = 1#8) (h7 : x7 = 0#8 ∨ x7 = 1#8) (h8 : x8 = 0#8 ∨ x8 = 1#8)
    (h9 : x9 = 0#8 ∨ x9 = 1#8) :
    (lebs2ipBits x0 x1 x2 x3 x4 x5 x6 x7 x8 x9).toNat = bitsVal x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;> rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl <;>
    rcases h6 with rfl | rfl <;> rcases h7 with rfl | rfl <;> rcases h8 with rfl | rfl <;>
    rcases h9 with rfl | rfl <;> rfl

theorem bitsVal_le (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : BitVec 8)
    (h0 : x0 = 0#8 ∨ x0 = 1#8) (h1 : x1 = 0#8 ∨ x1 = 1#8) (h2 : x2 = 0#8 ∨ x2 = 1#8)
    (h3 : x3 = 0#8 ∨ x3 = 1#8) (h4 : x4 = 0#8 ∨ x4 = 1#8) (h5 : x5 = 0#8 ∨ x5 = 1#8)
    (h6 : x6 = 0#8 ∨ x6 = 1#8) (h7 : x7 = 0#8 ∨ x7 = 1#8) (h8 : x8 = 0#8 ∨ x8 = 1#8)
    (h9 : x9 = 0#8 ∨ x9 = 1#8) : bitsVal x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 ≤ 1023 := by
  have le1 : ∀ x : BitVec 8, x = 0#8 ∨ x = 1#8 → x.toNat ≤ 1 := by
    rintro x (rfl | rfl) <;> decide
  have := le1 _ h0; have := le1 _ h1; have := le1 _ h2; have := le1 _ h3; have := le1 _ h4
  have := le1 _ h5; have := le1 _ h6; have := le1 _ h7; have := le1 _ h8; have := le1 _ h9
  unfold bitsVal; omega

/-- A `0`/`1` byte word is a `0`/`1` byte. -/
theorem byte_of_bool (x : BitVec 8) (h : BitVec.zeroExtend 64 x = 0#64 ∨ BitVec.zeroExtend 64 x = 1#64) :
    x = 0#8 ∨ x = 1#8 := by
  rcases h with h | h
  · left; rw [← trunc8_zext x, h]; rfl
  · right; rw [← trunc8_zext x, h]; rfl

/-- `byteAt` in the form the executor's `lbu` at `ofNat (10 i) + k` produces. -/
theorem byteAt_ofNat (ws : List Word) (a k : Nat) (h : a + k < 2 ^ 64) :
    BitVec.zeroExtend 64 (extractByte ws[(BitVec.ofNat 64 a + BitVec.ofNat 64 k).toNat / 8]!
      ((BitVec.ofNat 64 a + BitVec.ofNat 64 k).toNat % 8)) = byteAt ws (a + k) := by
  unfold byteAt
  have : (BitVec.ofNat 64 a + BitVec.ofNat 64 k).toNat = a + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [this]

theorem chunkVal_eq (ws : List Word) (j : Nat) :
    chunkVal ws j = (byteAt ws (10 * j)).toNat + 2 * (byteAt ws (10 * j + 1)).toNat +
      4 * (byteAt ws (10 * j + 2)).toNat + 8 * (byteAt ws (10 * j + 3)).toNat +
      16 * (byteAt ws (10 * j + 4)).toNat + 32 * (byteAt ws (10 * j + 5)).toNat +
      64 * (byteAt ws (10 * j + 6)).toNat + 128 * (byteAt ws (10 * j + 7)).toNat +
      256 * (byteAt ws (10 * j + 8)).toNat + 512 * (byteAt ws (10 * j + 9)).toNat := by
  have hr : List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl
  rw [chunkVal, hr]
  simp only [List.foldl_cons, List.foldl_nil, Nat.reducePow, Nat.add_zero]
  omega

theorem toNat_byteAt (ws : List Word) (o : Nat) :
    (byteAt ws o).toNat = (extractByte ws[o / 8]! (o % 8)).toNat := by
  unfold byteAt
  exact BitVec.toNat_setWidth_of_le (by decide)

/-- The chunk value: `lebs2ip_k` of the assembled `0`/`1` bytes. -/
theorem lebs2ipK_chunk (ws : List Word) (j : Nat) (A : Word)
    (hb : ∀ k, k < 10 → byteAt ws (10 * j + k) = 0#64 ∨ byteAt ws (10 * j + k) = 1#64) :
    (lebs2ipK (asm8 (extractByte ws[(10 * j) / 8]! ((10 * j) % 8)) (extractByte ws[(10 * j + 1) / 8]! ((10 * j + 1) % 8))
        (extractByte ws[(10 * j + 2) / 8]! ((10 * j + 2) % 8)) (extractByte ws[(10 * j + 3) / 8]! ((10 * j + 3) % 8))
        (extractByte ws[(10 * j + 4) / 8]! ((10 * j + 4) % 8)) (extractByte ws[(10 * j + 5) / 8]! ((10 * j + 5) % 8))
        (extractByte ws[(10 * j + 6) / 8]! ((10 * j + 6) % 8)) (extractByte ws[(10 * j + 7) / 8]! ((10 * j + 7) % 8)))
      (asm2 A (extractByte ws[(10 * j + 8) / 8]! ((10 * j + 8) % 8)) (extractByte ws[(10 * j + 9) / 8]! ((10 * j + 9) % 8)))).toNat =
      chunkVal ws j ∧ chunkVal ws j ≤ 1023 := by
  have b := fun k hk => byte_of_bool _ (hb k hk)
  have b0 : extractByte ws[(10 * j) / 8]! ((10 * j) % 8) = 0#8 ∨ extractByte ws[(10 * j) / 8]! ((10 * j) % 8) = 1#8 := by
    simpa using b 0 (by omega)
  rw [lebs2ipK_asm, lebs2ipBits_val _ _ _ _ _ _ _ _ _ _ b0 (b 1 (by omega)) (b 2 (by omega))
    (b 3 (by omega)) (b 4 (by omega)) (b 5 (by omega)) (b 6 (by omega)) (b 7 (by omega)) (b 8 (by omega))
    (b 9 (by omega))]
  have e : chunkVal ws j = bitsVal (extractByte ws[(10 * j) / 8]! ((10 * j) % 8)) (extractByte ws[(10 * j + 1) / 8]! ((10 * j + 1) % 8))
      (extractByte ws[(10 * j + 2) / 8]! ((10 * j + 2) % 8)) (extractByte ws[(10 * j + 3) / 8]! ((10 * j + 3) % 8))
      (extractByte ws[(10 * j + 4) / 8]! ((10 * j + 4) % 8)) (extractByte ws[(10 * j + 5) / 8]! ((10 * j + 5) % 8))
      (extractByte ws[(10 * j + 6) / 8]! ((10 * j + 6) % 8)) (extractByte ws[(10 * j + 7) / 8]! ((10 * j + 7) % 8))
      (extractByte ws[(10 * j + 8) / 8]! ((10 * j + 8) % 8)) (extractByte ws[(10 * j + 9) / 8]! ((10 * j + 9) % 8)) := by
    rw [chunkVal_eq]; unfold bitsVal
    simp only [toNat_byteAt]
  refine ⟨e.symm, ?_⟩
  rw [e]
  exact bitsVal_le _ _ _ _ _ _ _ _ _ _ b0 (b 1 (by omega)) (b 2 (by omega))
    (b 3 (by omega)) (b 4 (by omega)) (b 5 (by omega)) (b 6 (by omega)) (b 7 (by omega)) (b 8 (by omega))
    (b 9 (by omega))

/-- The table slice: cell `c / 8` of the entry at byte offset `64 m` (`c` a multiple of `8` below `64`). -/
theorem tbl_idx (m : Word) (hm : m.toNat ≤ 1023) (c : Nat) (hc : c % 8 = 0) (hc' : c < 64) :
    (m <<< 6 + BitVec.ofNat 64 c).toNat / 8 = 8 * m.toNat + c / 8 := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem tbl_idx0 (m : Word) (hm : m.toNat ≤ 1023) : (m <<< 6).toNat / 8 = 8 * m.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The step: two `incomplete_add`s on the tagged nine-word accumulator realise `sinStep`. -/
theorem AccRep.step (T : List Word) (m : Option (List Word)) (acc : List Word) (c : Nat)
    (hrep : AccRep m acc) (s0 s1 s2 s3 s4 s5 s6 s7 : Word)
    (hS : [s0, s1, s2, s3, s4, s5, s6, s7] = sEntryW T c)
    (t0 : Word) (L1 : List Word) (hL1l : L1.length = 8)
    (ht0 : t0 = if acc[0]! = 0#64 ∨ (1#64 : Word) = 0#64 ∨
      [acc[1]!, acc[2]!, acc[3]!, acc[4]!] = [s0, s1, s2, s3] then 0#64 else 1#64)
    (hL1 : acc[0]! ≠ 0#64 → (1#64 : Word) ≠ 0#64 → [acc[1]!, acc[2]!, acc[3]!, acc[4]!] ≠ [s0, s1, s2, s3] →
      L1 = curveAddL Sp1.pallasP 4 [acc[1]!, acc[2]!, acc[3]!, acc[4]!, acc[5]!, acc[6]!, acc[7]!, acc[8]!]
        [s0, s1, s2, s3, s4, s5, s6, s7])
    (t1 : Word) (L2 : List Word) (hL2l : L2.length = 8)
    (ht1 : t1 = if t0 = 0#64 ∨ acc[0]! = 0#64 ∨
      [L1[0]!, L1[1]!, L1[2]!, L1[3]!] = [acc[1]!, acc[2]!, acc[3]!, acc[4]!] then 0#64 else 1#64)
    (hL2 : t0 ≠ 0#64 → acc[0]! ≠ 0#64 → [L1[0]!, L1[1]!, L1[2]!, L1[3]!] ≠ [acc[1]!, acc[2]!, acc[3]!, acc[4]!] →
      L2 = curveAddL Sp1.pallasP 4 [L1[0]!, L1[1]!, L1[2]!, L1[3]!, L1[4]!, L1[5]!, L1[6]!, L1[7]!]
        [acc[1]!, acc[2]!, acc[3]!, acc[4]!, acc[5]!, acc[6]!, acc[7]!, acc[8]!]) :
    AccRep (sinStep T m c) (t1 :: [L2[0]!, L2[1]!, L2[2]!, L2[3]!, L2[4]!, L2[5]!, L2[6]!, L2[7]!]) := by
  have h10 : (1#64 : Word) ≠ 0#64 := by decide
  obtain ⟨hl, hnone, hsome⟩ := hrep
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, rfl⟩ : ∃ l0 l1 l2 l3 l4 l5 l6 l7 : Word,
      L1 = [l0, l1, l2, l3, l4, l5, l6, l7] := by
    match L1, hL1l with
    | [l0, l1, l2, l3, l4, l5, l6, l7], _ => exact ⟨l0, l1, l2, l3, l4, l5, l6, l7, rfl⟩
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, rfl⟩ : ∃ m0 m1 m2 m3 m4 m5 m6 m7 : Word,
      L2 = [m0, m1, m2, m3, m4, m5, m6, m7] := by
    match L2, hL2l with
    | [m0, m1, m2, m3, m4, m5, m6, m7], _ => exact ⟨m0, m1, m2, m3, m4, m5, m6, m7, rfl⟩
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at ht1 hL2 ⊢
  cases m with
  | none =>
    have h0 : acc[0]! = 0#64 := hnone.mpr rfl
    have ht0' : t0 = 0#64 := by rw [ht0, if_pos (Or.inl h0)]
    have ht1' : t1 = 0#64 := by rw [ht1, if_pos (Or.inl ht0')]
    refine ⟨rfl, ?_, ?_⟩
    · simp [sinStep, ht1']
    · intro L hL; simp [sinStep] at hL
  | some a =>
    have hacc : acc = 1#64 :: a := hsome a rfl
    subst hacc
    have hal : a.length = 8 := by simpa using hl
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 : Word,
        a = [a0, a1, a2, a3, a4, a5, a6, a7] := by
      match a, hal with
      | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, h10, false_or, ne_eq,
      not_false_eq_true, true_implies] at ht0 hL1 ht1 hL2
    simp only [sinStep, Option.bind_some, sinAdd, ← hS, List.take_succ_cons, List.take_zero]
    by_cases heq : [a0, a1, a2, a3] = [s0, s1, s2, s3]
    · have ht0' : t0 = 0#64 := by rw [ht0, if_pos heq]
      have ht1' : t1 = 0#64 := by rw [ht1, if_pos (Or.inl ht0')]
      simp only [heq, ↓reduceIte, Option.bind_none]
      exact ⟨rfl, by simp [ht1'], fun L hL => by simp at hL⟩
    · have ht0' : t0 = 1#64 := by rw [ht0, if_neg heq]
      have hL1' := hL1 heq
      simp only [heq, ↓reduceIte, Option.bind_some, ← hL1', List.take_succ_cons, List.take_zero]
      simp only [ht0', h10, false_or, not_false_eq_true, true_implies] at ht1 hL2
      by_cases heq2 : [l0, l1, l2, l3] = [a0, a1, a2, a3]
      · have ht1' : t1 = 0#64 := by rw [ht1, if_pos heq2]
        simp only [heq2, ↓reduceIte]
        exact ⟨rfl, by simp [ht1'], fun L hL => by simp at hL⟩
      · have ht1' : t1 = 1#64 := by rw [ht1, if_neg heq2]
        have hL2' := hL2 heq2
        simp only [heq2, ↓reduceIte, ← hL2']
        exact ⟨rfl, by simp [ht1', h10], fun L hL => by cases hL; rw [ht1']⟩

/-- The loop counter `x21 = 10 n` after one chunk. -/
theorem x21_step (n : Nat) (h : 10 * (n + 1) < 2 ^ 64) :
    BitVec.ofNat 64 (10 * (n + 1)) + 18446744073709551606#64 = BitVec.ofNat 64 (10 * n) := by
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 10 * n) (by omega),
    show 10 * (n + 1) + 18446744073709551606 = 10 * n + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- The message pointer `x22 = bp + 10 i` after one chunk. -/
theorem x22_step (bp : Word) (i : Nat) :
    bp + (BitVec.ofNat 64 (10 * i) + 10#64) = bp + BitVec.ofNat 64 (10 * (i + 1)) := by
  rw [BitVec.ofNat_add_ofNat, Nat.mul_succ]

theorem ofNat_ten_eq_zero (n : Nat) (h : 10 * n < 2 ^ 64) (h0 : BitVec.ofNat 64 (10 * n) = 0#64) : n = 0 := by
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  simp at this
  omega

end Cases.Zip2005
