/-
  Examples.Kit

  What the examples share, about a machine state: the bytes of a region, a byte read after a
  byte written, and 32-bit words in memory (a word or a byte read after a word written, the
  words that may be written, and what a machine state that agrees with a memory reads).
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

end Examples
