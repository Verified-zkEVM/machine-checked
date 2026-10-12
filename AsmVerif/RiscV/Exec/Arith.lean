/-
  AsmVerif.RiscV.Exec.Arith

  Word facts hand proofs keep needing: footprint hits of a store's doubleword, and the bit
  tests compilers use on lengths (`andi a4, a2, 16; beqz a4, …`).
-/

import AsmVerif.RiscV.Check.Arith

namespace AsmVerif.RiscV.Exec

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame AsmVerif.RiscV.Check

theorem toNat_ofNat_lt {r : Nat} (h : r < 2 ^ 64) : (BitVec.ofNat 64 r).toNat = r := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A byte at offset `< l` from `b` puts its doubleword in the range's keys. -/
theorem hits_align {b x : Word} {l : Nat} (h : (x - b).toNat < l) :
    Hits b l (alignToDword x) := by
  have h8 := sub_alignToDword_lt x
  generalize alignToDword x = k at *
  unfold Hits
  by_cases hc : (k - b).toNat < l
  · exact Or.inl hc
  · right; refine ⟨by omega, ?_⟩; bv_omega

theorem nat_and_two_pow (r b : Nat) : r &&& 2 ^ b = 2 ^ b * (r / 2 ^ b % 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  rcases Nat.mod_two_eq_zero_or_one (r / 2 ^ b) with h | h
  · rw [h, Nat.mul_zero, Nat.zero_testBit]
    by_cases hi : b = i
    · subst hi; rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
    · simp [hi]
  · rw [h, Nat.mul_one, Nat.testBit_two_pow]
    by_cases hi : b = i
    · subst hi; rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
    · simp [hi]

/-- Bit `b` of a word, as a test against `2^b`. -/
theorem and_bit {x : Word} {b : Nat} (hb : b < 64) :
    (x &&& BitVec.ofNat 64 (2 ^ b)).toNat = 2 ^ b * (x.toNat / 2 ^ b % 2) := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb), nat_and_two_pow]

theorem bit_set {x : Word} {b : Nat} (hb : b < 64)
    (h : (x &&& BitVec.ofNat 64 (2 ^ b) != 0) = true) : x.toNat / 2 ^ b % 2 = 1 := by
  have := and_bit (x := x) hb
  simp only [bne_iff_ne, ne_eq] at h
  have h2 : (x &&& BitVec.ofNat 64 (2 ^ b)).toNat ≠ 0 := fun h0 =>
    h (BitVec.eq_of_toNat_eq (by simpa using h0))
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ b) with h' | h'
  · rw [h', Nat.mul_zero] at this; exact absurd this h2
  · exact h'

theorem bit_clear {x : Word} {b : Nat} (hb : b < 64)
    (h : ¬ (x &&& BitVec.ofNat 64 (2 ^ b) != 0) = true) : x.toNat / 2 ^ b % 2 = 0 := by
  have := and_bit (x := x) hb
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
  rw [h] at this
  rcases Nat.mod_two_eq_zero_or_one (x.toNat / 2 ^ b) with h' | h'
  · exact h'
  · rw [h'] at this; simp at this; exact absurd this.symm (Nat.ne_of_gt (Nat.two_pow_pos b))

theorem bit_set' {x : Word} {b : Nat} (hb : b < 64)
    (h : ¬ (x &&& BitVec.ofNat 64 (2 ^ b) == 0) = true) : x.toNat / 2 ^ b % 2 = 1 :=
  bit_set hb (by simpa [bne_iff_ne] using h)

theorem bit_clear' {x : Word} {b : Nat} (hb : b < 64)
    (h : (x &&& BitVec.ofNat 64 (2 ^ b) == 0) = true) : x.toNat / 2 ^ b % 2 = 0 :=
  bit_clear hb (by simpa [bne_iff_ne] using h)

end AsmVerif.RiscV.Exec
