import Cases.Zip2005.Runtime.MemcpyMis

/-! A pointer `k` bytes into an aligned doubleword (`memcpy`'s misaligned destinations). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem and7_of_sub3' {p : Word} (h : (p - 3#64).toNat % 8 = 0) : p &&& 7#64 = 3#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

theorem and7_of_sub4' {p : Word} (h : (p - 4#64).toNat % 8 = 0) : p &&& 7#64 = 4#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

theorem and7_of_sub5' {p : Word} (h : (p - 5#64).toNat % 8 = 0) : p &&& 7#64 = 5#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

theorem and7_of_sub6' {p : Word} (h : (p - 6#64).toNat % 8 = 0) : p &&& 7#64 = 6#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

theorem and7_of_sub7' {p : Word} (h : (p - 7#64).toNat % 8 = 0) : p &&& 7#64 = 7#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

end Cases.Zip2005
