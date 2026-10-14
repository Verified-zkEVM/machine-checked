/-
  Cases.Zip2005.Cells4

  Four little-endian cells of a 256-bit value, as the executor writes them
  (`BitVec.ofNat 64 (x >>> 64 k)`), and their decoding.
-/

import Cases.Zip2005.Field.CtLimbs

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

theorem natToLeLimbs_zero (x : Nat) : natToLeLimbs 0 x = [] := rfl

theorem natToLeLimbs_cells4 (x : Nat) : natToLeLimbs 4 x =
    [BitVec.ofNat 64 x, BitVec.ofNat 64 (x >>> 64), BitVec.ofNat 64 (x >>> 128), BitVec.ofNat 64 (x >>> 192)] := by
  simp only [natToLeLimbs_succ, natToLeLimbs_zero, ← Nat.shiftRight_add, Nat.reduceAdd]

/-- Four cells of a value below `2^256` decode to it. -/
theorem cells4_decode (x : Nat) (h : x < 2 ^ 256) :
    leLimbsToNat [BitVec.ofNat 64 x, BitVec.ofNat 64 (x >>> 64), BitVec.ofNat 64 (x >>> 128),
      BitVec.ofNat 64 (x >>> 192)] = x := by
  rw [← natToLeLimbs_cells4]; exact leLimbsToNat_natToLeLimbs 4 x h

theorem leLimbsToNat4_lt (a b c d : Word) : leLimbsToNat [a, b, c, d] < 2 ^ 256 := leLimbsToNat_lt _

/-- The cells of a value below `2^256` are all zero exactly when it is. -/
theorem cells4_eq_zero_iff (x : Nat) (h : x < 2 ^ 256) :
    (BitVec.ofNat 64 x = 0#64 ∧ BitVec.ofNat 64 (x >>> 64) = 0#64 ∧ BitVec.ofNat 64 (x >>> 128) = 0#64 ∧
      BitVec.ofNat 64 (x >>> 192) = 0#64) ↔ x = 0 := by
  constructor
  · intro hz
    have d := cells4_decode x h
    rw [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2] at d
    rw [← d]; rfl
  · rintro rfl
    simp only [Nat.zero_shiftRight, and_self]

end Cases.Zip2005
