/-
  Examples.Kit

  What the examples share, about a machine state: the bytes of a region, a string, a copied
  region and the sum of doublewords; a byte read after a byte written; 32-bit words in memory
  (a word or a byte read after a word written, the words that may be written); what a machine
  state that agrees with a memory or a register file reads; and the arithmetic on addresses and
  counters that several proofs use.
-/

import MachineChecked.RiscV.Lift.Contract
import MachineChecked.RiscV.Lift.Rules
import LprogRiscV.Lsym

namespace Examples

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine

/-- `j + 1`, as addresses count it. -/
theorem ofNat_succ (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- The `n` bytes from address `a`. -/
def bytesAt (m : MachineState) (a : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m.getByte (a + BitVec.ofNat 64 i)

/-- Byte `q` of a doubleword whose byte `p` was replaced. -/
theorem extractByte_replaceByte (w p q : Word) (b : BitVec 8) (hp : p ≤ 7#64) (hq : q ≤ 7#64) :
    extractByte (replaceByte w p.toNat b) q.toNat = if q = p then b else extractByte w q.toNat := by
  have e : ∀ x : Word, x ≤ 7#64 → x.toNat * 8 = (x * 8#64).toNat := fun x hx => by bv_omega
  simp only [extractByte, replaceByte, e p hp, e q hq, ← BitVec.shiftLeft_eq',
    ← BitVec.ushiftRight_eq']
  split <;> bv_decide

/-- **A byte read after a byte written**: the byte written at that address, the old one elsewhere. -/
theorem getByte_setByte (m : MachineState) (a c : Word) (b : BitVec 8) :
    (m.setByte a b).getByte c = if c = a then b else m.getByte c := by
  simp only [MachineState.getByte, MachineState.setByte, getMem_setMem, byteOffset]
  by_cases h : alignToDword c = alignToDword a
  · have e : (c &&& 7#64 = a &&& 7#64) ↔ c = a := by
      unfold alignToDword at h; constructor <;> intro h' <;> bv_decide
    simp only [h, ↓reduceIte, extractByte_replaceByte _ _ _ _ (show a &&& 7#64 ≤ 7#64 by bv_decide)
      (show c &&& 7#64 ≤ 7#64 by bv_decide), e]
  · have hne : c ≠ a := fun h' => h (by rw [h'])
    simp only [h, hne, ↓reduceIte]

/-! ## 32-bit words in memory -/

/-- Alignment to four bytes, as a fact about the low bits. -/
theorem aligned4_iff (a : Word) : alignedFor 4 a = true ↔ a &&& 3#64 = 0#64 := by
  have e : a.toNat % 4 = (a &&& 3#64).toNat := by
    rw [BitVec.toNat_and]; exact (Nat.and_two_pow_sub_one_eq_mod _ 2).symm
  simp [alignedFor, isAligned4, e, BitVec.toNat_eq]

/-- The shift that selects the 32-bit word of an address in its doubleword. -/
theorem word_shift (a : Word) : (a &&& 7#64).toNat / 4 * 32 = ((a &&& 4#64) * 8#64).toNat := by
  have h : a &&& 7#64 = 0#64 ∨ a &&& 7#64 = 1#64 ∨ a &&& 7#64 = 2#64 ∨ a &&& 7#64 = 3#64 ∨
      a &&& 7#64 = 4#64 ∨ a &&& 7#64 = 5#64 ∨ a &&& 7#64 = 6#64 ∨ a &&& 7#64 = 7#64 := by
    bv_decide
  have h4 : a &&& 4#64 = (a &&& 7#64) &&& 4#64 := by bv_decide
  rw [h4]
  rcases h with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem byte_shift (a : Word) : (a &&& 7#64).toNat * 8 = ((a &&& 7#64) * 8#64).toNat := by
  have : a &&& 7#64 ≤ 7#64 := by bv_decide
  bv_omega

/-- **A word read after a word written**, both aligned. -/
theorem getWord32_setWord32 (m : MachineState) (a c : Word) (v : BitVec 32)
    (ha : alignedFor 4 a = true) (hc : alignedFor 4 c = true) :
    (m.setWord32 a v).getWord32 c = if c = a then v else m.getWord32 c := by
  rw [aligned4_iff] at ha hc
  simp only [MachineState.getWord32, MachineState.setWord32, getMem_setMem, byteOffset,
    extractWord32, replaceWord32, word_shift, ← BitVec.shiftLeft_eq', ← BitVec.ushiftRight_eq',
    alignToDword]
  by_cases h : c &&& ~~~7#64 = a &&& ~~~7#64
  · simp only [h, ↓reduceIte]
    generalize m.getMem _ = w
    split <;> bv_decide
  · have hne : c ≠ a := fun h' => h (by rw [h'])
    simp only [h, hne, ↓reduceIte]

/-- **A byte read after a word written** elsewhere. -/
theorem getByte_setWord32 (m : MachineState) (a x : Word) (v : BitVec 32)
    (ha : alignedFor 4 a = true) (hx : 4 ≤ (x - a).toNat) :
    (m.setWord32 a v).getByte x = m.getByte x := by
  rw [aligned4_iff] at ha
  have hx' : 4#64 ≤ x - a := by bv_omega
  simp only [MachineState.getByte, MachineState.setWord32, getMem_setMem, byteOffset,
    extractByte, replaceWord32, word_shift, byte_shift, ← BitVec.shiftLeft_eq', ← BitVec.ushiftRight_eq',
    alignToDword]
  by_cases h : x &&& ~~~7#64 = a &&& ~~~7#64
  · simp only [h, ↓reduceIte]
    generalize m.getMem _ = w
    bv_decide
  · simp only [h, ↓reduceIte]

/-- A store of a word does not change the code, so not where the code is. -/
theorem noCodeAt_setWord32 (m : MachineState) (a b : Word) (v : BitVec 32) (w : Nat) :
    noCodeAt (m.setWord32 a v) b w = noCodeAt m b w := rfl

theorem aligned4_add {a : Word} (h : alignedFor 4 a = true) (k : Word) (hk : k &&& 3#64 = 0#64) :
    alignedFor 4 (a + k) = true := by
  rw [aligned4_iff] at h ⊢; bv_decide

/-- The `n` 32-bit words at `a` may be written: `a` is aligned, and each word is in SP1's
    memory and not code. -/
def Writable (m : MachineState) (a : Word) (n : Nat) : Prop :=
  alignedFor 4 a = true ∧ ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 (4 * i)) = true ∧
    noCodeAt m (a + BitVec.ofNat 64 (4 * i)) 4 = true

/-- A machine state reads the words of a memory it agrees with. -/
theorem getWord32_of_agree {r' : Reg → BitVec 64} {m' t : MachineState}
    (h : Agree (ofParts r' m') t) (x : Word) : t.getWord32 x = m'.getWord32 x := by
  simp only [MachineState.getWord32, ← h.mem, getMem_ofParts]

/-- A machine state reads the bytes of a memory it agrees with. -/
theorem getByte_of_agree {r' : Reg → BitVec 64} {m' t : MachineState}
    (h : Agree (ofParts r' m') t) (x : Word) : t.getByte x = m'.getByte x := by
  simp only [MachineState.getByte, ← h.mem, getMem_ofParts]

/-- A machine state reads the registers of a register file it agrees with, but `x0`. -/
theorem getReg_of_agree {r' : Reg → BitVec 64} {m' t : MachineState}
    (h : Agree (ofParts r' m') t) {r : Reg} (hr : r ≠ .x0) : t.getReg r = r' r := by
  rw [← h.regs, getReg_ofParts, ite_eq_right hr]

/-! ## Regions of memory -/

/-- Two byte lists of memory are equal when they agree byte by byte. -/
theorem bytesAt_eq_iff (m m' : MachineState) (a b : Word) (n : Nat) :
    bytesAt m a n = bytesAt m' b n ↔
      ∀ i < n, m.getByte (a + BitVec.ofNat 64 i) = m'.getByte (b + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.map_inj_left]

/-- A string of length `n` at `s`: `n` bytes that are not zero, then a zero. -/
def StrAt (m : MachineState) (s : Word) (n : Nat) : Prop :=
  n < 2 ^ 64 ∧ (∀ i < n, m.getByte (s + BitVec.ofNat 64 i) ≠ 0) ∧
    m.getByte (s + BitVec.ofNat 64 n) = 0

/-- A string has one length. -/
theorem StrAt.unique {m : MachineState} {s : Word} {n n' : Nat} (h : StrAt m s n)
    (h' : StrAt m s n') : n' = n := by
  rcases Nat.lt_trichotomy n' n with hlt | heq | hlt
  · exact absurd h'.2.2 (h.2.1 n' hlt)
  · exact heq
  · exact absurd h.2.2 (h'.2.1 n hlt)

/-- What a copy of the `n` bytes at `src` to `dst` leaves in the memory `m'`, from the memory
    `m`: the bytes at `dst` are those that were at `src`, and no other byte or code changed. -/
def Copied (m : MachineState) (dst src : Word) (n : Nat) (m' : MachineState) : Prop :=
  bytesAt m' dst n = bytesAt m src n ∧
  (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → m'.getByte x = m.getByte x) ∧
  m'.code = m.code

/-- The wrapping sum of the first `k` doublewords from `p`: `p[0] + … + p[k - 1]`. -/
def sumMem (m : MachineState) (p : Word) : Nat → Word
  | 0 => 0
  | k + 1 => sumMem m p k + m.getMem (p + BitVec.ofNat 64 (8 * k))

/-! ## Words in doublewords -/

/-- A 32-bit word read after a doubleword written elsewhere. -/
theorem getWord32_setMem (m : MachineState) (c w a : Word) (h : alignToDword a ≠ c) :
    (m.setMem c w).getWord32 a = m.getWord32 a := by
  simp only [MachineState.getWord32, MachineState.getMem_setMem_ne h]

/-- A doubleword read after a word written in another doubleword. -/
theorem getMem_setWord32 (m : MachineState) (a c : Word) (v : BitVec 32) (h : c ≠ alignToDword a) :
    (m.setWord32 a v).getMem c = m.getMem c := by
  simp only [MachineState.setWord32, MachineState.getMem_setMem_ne h]

/-- Word `i` of an aligned array of words is aligned. -/
theorem aligned4_ofNat {w : Word} (h : alignedFor 4 w = true) (i : Nat) :
    alignedFor 4 (w + BitVec.ofNat 64 (4 * i)) = true := by
  refine aligned4_add h _ ?_
  have : BitVec.ofNat 64 (4 * i) = 4#64 * BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_decide

/-- Alignment to eight bytes, as a fact about the low bits. -/
theorem aligned8_iff (a : Word) : alignedFor 8 a = true ↔ a &&& 7#64 = 0#64 := by
  have e : a.toNat % 8 = (a &&& 7#64).toNat := by
    rw [BitVec.toNat_and]; exact (Nat.and_two_pow_sub_one_eq_mod _ 3).symm
  simp [alignedFor, isAligned8, e, BitVec.toNat_eq]

/-- A word-aligned offset from an aligned stack pointer is word-aligned. -/
theorem frame_aligned {top : Word} (ht : top &&& 7#64 = 0#64) (c : Word) (hc : c &&& 3#64 = 0#64) :
    alignedFor 4 (top + c) = true := by
  rw [aligned4_iff]; bv_decide

/-- A 32-bit word sign-extended to 64 bits, then its low half. -/
theorem sext_trunc (x : BitVec 32) : (BitVec.signExtend 64 x).setWidth 32 = x := by bv_decide

/-! ### A loop over sixteen words, by a byte offset `4 t` -/

theorem copy_more {t : Nat} (ht : t < 16) (h : ¬BitVec.ofNat 64 (4 * t) + 4#64 = 64#64) :
    t + 1 < 16 := by bv_omega

theorem copy_last {t : Nat} (ht : t < 16) (h : BitVec.ofNat 64 (4 * t) + 4#64 = 64#64) :
    t = 15 := by bv_omega

theorem next_addr (b : Word) (t : Nat) :
    b + (BitVec.ofNat 64 (4 * t) + 4#64) = b + BitVec.ofNat 64 (4 * (t + 1)) := by bv_omega

/-! ## Arithmetic on addresses and counters -/

theorem add_one_add (p : Word) (i : Nat) :
    p + 1#64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, BitVec.add_comm 1#64, ofNat_succ]

theorem ne_add_succ (p : Word) {i : Nat} (hi : i + 1 < 2 ^ 64) :
    p ≠ p + BitVec.ofNat 64 (i + 1) := by bv_omega

theorem end_next {k : Nat} (hk : k + 1 < 2 ^ 64) (h : 1#64 = BitVec.ofNat 64 (k + 1)) : k = 0 := by
  bv_omega

theorem add_ofNat_inj (a : Word) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 j) : i = j := by
  bv_omega

theorem ofNat_inj {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : BitVec.ofNat 64 i = BitVec.ofNat 64 j) : i = j := by
  bv_omega

theorem ofNat_eq_zero {x : Nat} (hx : x < 2 ^ 64) (h : BitVec.ofNat 64 x = 0#64) : x = 0 := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this

theorem ofNat_add_neg_one {x : Nat} (h : 0 < x) :
    BitVec.ofNat 64 x + 18446744073709551615#64 = BitVec.ofNat 64 (x - 1) := by
  bv_omega

/-- The shift that scales an index to a byte offset, as a multiplication. -/
theorem shl3 (x : Word) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

/-! ## Bytes in registers -/

theorem zext_byte_eq_zero (b : BitVec 8) : BitVec.setWidth 64 b = 0#64 ↔ b = 0#8 := by
  constructor <;> intro h <;> bv_decide

theorem zeroExtend_byte_inj (x y : BitVec 8) (h : BitVec.zeroExtend 64 x = BitVec.zeroExtend 64 y) :
    x = y := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have hx := x.isLt; have hy := y.isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

end Examples
