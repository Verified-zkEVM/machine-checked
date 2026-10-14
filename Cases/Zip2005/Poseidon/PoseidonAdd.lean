import Cases.Zip2005.Field.MontTail
import Cases.Zip2005.Field.FpAdd
import AsmVerif.RiscV.Sym.Close

/-!
# Poseidon's inline `Fp` addition

`halo2_poseidon`'s MDS closure adds each product into the accumulator with `Fp::add` inlined:
the `adc` chain (`fadd_limbs`), then `D - p` as a borrow chain whose sign mask `M` masks `p`
back in (`padd_reduce`). The stages `padd_s0`..`padd_s4` are one limb each.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

set_option autoImplicit false

theorem and_ones (x : Word) : x &&& 18446744073709551615#64 = x := by
  rw [show (18446744073709551615#64 : Word) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]

theorem and_mask {M c v : Word} (hM : M.toNat = 0 ∨ M.toNat = 2 ^ 64 - 1) (h : M &&& c = v) :
    (M.toNat = 0 ∧ v.toNat = 0) ∨ (M.toNat = 2 ^ 64 - 1 ∧ v.toNat = c.toNat) := by
  subst h
  rcases hM with h0 | h1
  · left; refine ⟨h0, ?_⟩
    have : M = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h0)
    subst this; simp
  · right; refine ⟨h1, ?_⟩
    have : M = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by simp [h1])
    subst this; rw [BitVec.allOnes_and]

theorem leLimbsToNat4 (a b c d : Word) :
    leLimbsToNat [a, b, c, d] = a.toNat + 2 ^ 64 * b.toNat + 2 ^ 128 * c.toNat + 2 ^ 192 * d.toNat := by
  simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring

/-- A comparison flag as arithmetic. -/
theorem ult_flag {a b v : Word} (h : (if a.ult b = true then 1#64 else 0#64) = v) :
    (v.toNat = 1 ∧ a.toNat < b.toNat) ∨ (v.toNat = 0 ∧ b.toNat ≤ a.toNat) := by
  subst h
  by_cases hab : a.ult b = true
  · left; simp only [hab, if_true]; exact ⟨rfl, by simpa [BitVec.ult] using hab⟩
  · right; simp only [hab]
    exact ⟨rfl, by simpa [BitVec.ult] using hab⟩

/-- Limb 0 of `D - p`: the borrow mask `m0`. -/
theorem padd_s0 {P0 N0 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hP0 : 0 < P0 ∧ 0 < N0) {d0 c0 m0 t0 : Word}
    (c0_def : (if (d0 + BitVec.ofNat 64 N0).ult d0 = true then 1#64 else 0#64) = c0)
    (m0_def : (18446744073709551615#64 + c0).sshiftRight 63 = m0)
    (t0_def : d0 + BitVec.ofNat 64 N0 &&& 18446744073709551615#64 = t0) :
    (m0.toNat = 0 ∧ d0.toNat = P0 + t0.toNat) ∨ (m0.toNat = 2 ^ 64 - 1 ∧ d0.toNat + 2 ^ 64 = P0 + t0.toNat) := by
  rw [and_ones] at t0_def
  have s := Bn.sar_fact m0_def
  bn_lin
  rcases (by omega : c0.toNat = 0 ∨ c0.toNat = 1) with h | h <;> omega

/-- Limb 1: borrow in `m0`, out `m1`. -/
theorem padd_s1 {P1 N1 : Nat} (hN1 : N1 + P1 = 2 ^ 64) (hP1 : 0 < P1 ∧ 0 < N1) {d1 m0 c1a u1 t1 c1b w1 m1 : Word}
    (h0 : m0.toNat = 0 ∨ m0.toNat = 2 ^ 64 - 1)
    (c1a_def : (if (m0 + BitVec.ofNat 64 N1).ult m0 = true then 1#64 else 0#64) = c1a)
    (u1_def : m0 + (18446744073709551615#64 + c1a) = u1)
    (t1_def : m0 + (BitVec.ofNat 64 N1 + (d1 &&& 18446744073709551615#64)) = t1)
    (c1b_def : (if t1.ult (m0 + BitVec.ofNat 64 N1) = true then 1#64 else 0#64) = c1b)
    (w1_def : u1 + c1b = w1)
    (m1_def : w1.sshiftRight 63 = m1) :
    (m1.toNat = 0 ∧ d1.toNat = P1 + m0.toNat / 18446744073709551615 + t1.toNat) ∨
      (m1.toNat = 2 ^ 64 - 1 ∧ d1.toNat + 2 ^ 64 = P1 + m0.toNat / 18446744073709551615 + t1.toNat) := by
  rw [and_ones] at t1_def
  have s := Bn.sar_fact m1_def
  have hf : (BitVec.ofNat 64 N1 : Word).toNat = N1 := by rw [BitVec.toNat_ofNat]; omega
  have fb := ult_flag c1b_def
  have e := Bn.add_fact' (show m0 + BitVec.ofNat 64 N1 = m0 + BitVec.ofNat 64 N1 from rfl)
  bn_lin
  rcases h0 with h | h <;>
  rcases (by omega : c1a.toNat = 0 ∨ c1a.toNat = 1) with h2 | h2 <;>
  rcases (by omega : c1b.toNat = 0 ∨ c1b.toNat = 1) with h3 | h3 <;> omega

/-- Limb 2 (`p2 = 0`): borrow in `m1`, out `m2`. -/
theorem padd_s2 {d2 m1 t2 c2 w2 m2 : Word}
    (h1 : m1.toNat = 0 ∨ m1.toNat = 2 ^ 64 - 1)
    (t2_def : m1 + (d2 &&& 18446744073709551615#64) = t2)
    (c2_def : (if t2.ult m1 = true then 1#64 else 0#64) = c2)
    (w2_def : m1 + c2 = w2)
    (m2_def : w2.sshiftRight 63 = m2) :
    (m2.toNat = 0 ∧ d2.toNat = m1.toNat / 18446744073709551615 + t2.toNat) ∨
      (m2.toNat = 2 ^ 64 - 1 ∧ d2.toNat + 2 ^ 64 = m1.toNat / 18446744073709551615 + t2.toNat) := by
  rw [and_ones] at t2_def
  have s := Bn.sar_fact m2_def
  bn_lin
  rcases h1 with h | h <;>
  rcases (by omega : c2.toNat = 0 ∨ c2.toNat = 1) with h2 | h2 <;> omega

/-- Limb 3 (`p3 = 2^62`): borrow in `m2`; the final mask `M`. -/
theorem padd_s3 {d3 m2 c3a u3 t3 c3b M : Word}
    (h2 : m2.toNat = 0 ∨ m2.toNat = 2 ^ 64 - 1)
    (c3a_def : (if ((d3 &&& 18446744073709551615#64) + 13835058055282163712#64).ult (d3 &&& 18446744073709551615#64) = true then 1#64 else 0#64) = c3a)
    (u3_def : 18446744073709551615#64 + (c3a + m2) = u3)
    (t3_def : (d3 &&& 18446744073709551615#64) + (13835058055282163712#64 + m2) = t3)
    (c3b_def : (if t3.ult ((d3 &&& 18446744073709551615#64) + 13835058055282163712#64) = true then 1#64 else 0#64) = c3b)
    (M_def : u3 + c3b = M) :
    (M.toNat = 0 ∧ d3.toNat = 2 ^ 62 + m2.toNat / 18446744073709551615 + t3.toNat) ∨
      (M.toNat = 2 ^ 64 - 1 ∧ d3.toNat + 2 ^ 64 = 2 ^ 62 + m2.toNat / 18446744073709551615 + t3.toNat) := by
  simp only [and_ones] at c3a_def t3_def c3b_def
  have e := Bn.add_fact' (show d3 + 13835058055282163712#64 = d3 + 13835058055282163712#64 from rfl)
  have fb := ult_flag c3b_def
  bn_lin
  rcases h2 with h | h <;>
  rcases (by omega : c3a.toNat = 0 ∨ c3a.toNat = 1) with h3 | h3 <;>
  rcases (by omega : c3b.toNat = 0 ∨ c3b.toNat = 1) with h4 | h4 <;> omega

set_option maxHeartbeats 4000000 in
/-- The add-back: `p` masked by `M` added to the difference `T`. -/
theorem padd_s4 {M t0 t1 t2 t3 k0 r0 c4 t1' k1 s1 c5 r1 c6 c7 t2' r2 c8 k3 q3 : Word}
    (hM : M.toNat = 0 ∨ M.toNat = 2 ^ 64 - 1)
    (k0_def : M &&& 11037532056220336129#64 = k0) (r0_def : k0 + t0 = r0)
    (c4_def : (if r0.ult k0 = true then 1#64 else 0#64) = c4)
    (t1'_def : t1 &&& 18446744073709551615#64 = t1')
    (k1_def : M &&& 2469829653914515739#64 = k1) (s1_def : k1 + t1' = s1)
    (c5_def : (if s1.ult k1 = true then 1#64 else 0#64) = c5)
    (r1_def : s1 + c4 = r1) (c6_def : (if r1.ult s1 = true then 1#64 else 0#64) = c6)
    (c7_def : c5 + c6 = c7)
    (t2'_def : t2 &&& 18446744073709551615#64 = t2') (r2_def : c7 + t2' = r2)
    (c8_def : (if r2.ult c7 = true then 1#64 else 0#64) = c8)
    (k3_def : M &&& 4611686018427387904#64 = k3) (q3_def : k3 + t3 = q3) :
    let T := t0.toNat + 2 ^ 64 * t1.toNat + 2 ^ 128 * t2.toNat + 2 ^ 192 * t3.toNat
    let R := r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * (q3 + c8).toNat
    (M.toNat = 0 → R = T) ∧
      (M.toNat = 2 ^ 64 - 1 → R + 2 ^ 256 * ((T + Fp.p) / 2 ^ 256) = T + Fp.p) := by
  intro T R
  rw [and_ones] at t1'_def t2'_def
  subst t1'_def t2'_def
  have m0 := and_mask hM k0_def
  have m1 := and_mask hM k1_def
  have m3 := and_mask hM k3_def
  simp only [Bn.toNat_ofNat'] at m0 m1 m3
  have e8 := Bn.add_fact' (show q3 + c8 = q3 + c8 from rfl)
  have hp : Fp.p = 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 4611686018427387904 := by
    decide +kernel
  bn_lin
  rw [hp]
  rcases hM with h1 | h1 <;>
  rcases (by omega : c4.toNat = 0 ∨ c4.toNat = 1) with h2 | h2 <;>
  rcases (by omega : c5.toNat = 0 ∨ c5.toNat = 1) with h3 | h3 <;>
  rcases (by omega : c6.toNat = 0 ∨ c6.toNat = 1) with h4 | h4 <;>
  rcases (by omega : c8.toNat = 0 ∨ c8.toNat = 1) with h5 | h5 <;>
  constructor <;> intro h <;> omega

/-- The stages combined: the reduced sum is `D % p` for `D < 2p`. -/
theorem padd_combine {d0 d1 d2 d3 m0 m1 m2 M t0 t1 t2 t3 r0 r1 r2 r3 : Word}
    (hD : d0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * d3.toNat < 2 * Fp.p)
    (h0 : (m0.toNat = 0 ∧ d0.toNat = 11037532056220336129 + t0.toNat) ∨
      (m0.toNat = 2 ^ 64 - 1 ∧ d0.toNat + 2 ^ 64 = 11037532056220336129 + t0.toNat))
    (h1 : (m1.toNat = 0 ∧ d1.toNat = 2469829653914515739 + m0.toNat / 18446744073709551615 + t1.toNat) ∨
      (m1.toNat = 2 ^ 64 - 1 ∧ d1.toNat + 2 ^ 64 = 2469829653914515739 + m0.toNat / 18446744073709551615 + t1.toNat))
    (h2 : (m2.toNat = 0 ∧ d2.toNat = m1.toNat / 18446744073709551615 + t2.toNat) ∨
      (m2.toNat = 2 ^ 64 - 1 ∧ d2.toNat + 2 ^ 64 = m1.toNat / 18446744073709551615 + t2.toNat))
    (h3 : (M.toNat = 0 ∧ d3.toNat = 2 ^ 62 + m2.toNat / 18446744073709551615 + t3.toNat) ∨
      (M.toNat = 2 ^ 64 - 1 ∧ d3.toNat + 2 ^ 64 = 2 ^ 62 + m2.toNat / 18446744073709551615 + t3.toNat))
    (h4 : (M.toNat = 0 → r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat =
        t0.toNat + 2 ^ 64 * t1.toNat + 2 ^ 128 * t2.toNat + 2 ^ 192 * t3.toNat) ∧
      (M.toNat = 2 ^ 64 - 1 → r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat +
        2 ^ 256 * ((t0.toNat + 2 ^ 64 * t1.toNat + 2 ^ 128 * t2.toNat + 2 ^ 192 * t3.toNat + Fp.p) / 2 ^ 256) =
        t0.toNat + 2 ^ 64 * t1.toNat + 2 ^ 128 * t2.toNat + 2 ^ 192 * t3.toNat + Fp.p)) :
    r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat =
      (d0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * d3.toNat) % Fp.p := by
  have hp : Fp.p = 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 4611686018427387904 := by
    decide +kernel
  have b0 := r0.isLt; have b1 := r1.isLt; have b2 := r2.isLt; have b3 := r3.isLt
  have b4 := t0.isLt; have b5 := t1.isLt; have b6 := t2.isLt; have b7 := t3.isLt
  obtain ⟨h4a, h4b⟩ := h4
  rw [hp] at hD h4b ⊢
  rcases h3 with ⟨hM, e3⟩ | ⟨hM, e3⟩
  · have e := h4a hM
    rcases h0 with ⟨z0, e0⟩ | ⟨z0, e0⟩ <;> rw [z0] at h1 <;>
    rcases h1 with ⟨z1, e1⟩ | ⟨z1, e1⟩ <;> rw [z1] at h2 <;>
    rcases h2 with ⟨z2, e2⟩ | ⟨z2, e2⟩ <;> rw [z2] at e3 <;>
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · have e := h4b hM
    rcases h0 with ⟨z0, e0⟩ | ⟨z0, e0⟩ <;> rw [z0] at h1 <;>
    rcases h1 with ⟨z1, e1⟩ | ⟨z1, e1⟩ <;> rw [z1] at h2 <;>
    rcases h2 with ⟨z2, e2⟩ | ⟨z2, e2⟩ <;> rw [z2] at e3 <;>
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- Poseidon's inline `Fp` reduction, in the compiler's schedule: `D - p`, then `p` masked back. -/
theorem padd_reduce {d0 d1 d2 d3 c0 e1 m0 c1a u1 t1 c1b w1 e2 m1 t2 c2 w2 e3 m2 c3a u3 t3 c3b M
      t0 k0 r0 c4 t1' k1 s1 c5 r1 c6 c7 t2' r2 c8 k3 q3 : Word}
    (c0_def : (if (d0 + 7409212017489215487#64).ult d0 = true then 1#64 else 0#64) = c0)
    (e1_def : d1 &&& 18446744073709551615#64 = e1)
    (m0_def : (18446744073709551615#64 + c0).sshiftRight 63 = m0)
    (c1a_def : (if (m0 + 15976914419795035877#64).ult m0 = true then 1#64 else 0#64) = c1a)
    (u1_def : m0 + (18446744073709551615#64 + c1a) = u1)
    (t1_def : m0 + (15976914419795035877#64 + e1) = t1)
    (c1b_def : (if t1.ult (m0 + 15976914419795035877#64) = true then 1#64 else 0#64) = c1b)
    (w1_def : u1 + c1b = w1)
    (e2_def : d2 &&& 18446744073709551615#64 = e2)
    (m1_def : w1.sshiftRight 63 = m1) (t2_def : m1 + e2 = t2)
    (c2_def : (if t2.ult m1 = true then 1#64 else 0#64) = c2) (w2_def : m1 + c2 = w2)
    (e3_def : d3 &&& 18446744073709551615#64 = e3) (m2_def : w2.sshiftRight 63 = m2)
    (c3a_def : (if (e3 + 13835058055282163712#64).ult e3 = true then 1#64 else 0#64) = c3a)
    (u3_def : 18446744073709551615#64 + (c3a + m2) = u3)
    (t3_def : e3 + (13835058055282163712#64 + m2) = t3)
    (c3b_def : (if t3.ult (e3 + 13835058055282163712#64) = true then 1#64 else 0#64) = c3b)
    (M_def : u3 + c3b = M)
    (t0_def : d0 + 7409212017489215487#64 &&& 18446744073709551615#64 = t0)
    (k0_def : M &&& 11037532056220336129#64 = k0) (r0_def : k0 + t0 = r0)
    (c4_def : (if r0.ult k0 = true then 1#64 else 0#64) = c4)
    (t1'_def : t1 &&& 18446744073709551615#64 = t1')
    (k1_def : M &&& 2469829653914515739#64 = k1) (s1_def : k1 + t1' = s1)
    (c5_def : (if s1.ult k1 = true then 1#64 else 0#64) = c5)
    (r1_def : s1 + c4 = r1) (c6_def : (if r1.ult s1 = true then 1#64 else 0#64) = c6)
    (c7_def : c5 + c6 = c7)
    (t2'_def : t2 &&& 18446744073709551615#64 = t2') (r2_def : c7 + t2' = r2)
    (c8_def : (if r2.ult c7 = true then 1#64 else 0#64) = c8)
    (k3_def : M &&& 4611686018427387904#64 = k3) (q3_def : k3 + t3 = q3)
    (hD : leLimbsToNat [d0, d1, d2, d3] < 2 * Fp.p) :
    leLimbsToNat [r0, r1, r2, q3 + c8] = leLimbsToNat [d0, d1, d2, d3] % Fp.p := by
  subst e1_def e2_def e3_def
  have h0 := padd_s0 (P0 := 11037532056220336129) (N0 := 7409212017489215487) (by norm_num)
    (by norm_num) c0_def m0_def t0_def
  have h1 := padd_s1 (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by norm_num)
    (by norm_num) (by rcases h0 with h | h <;> simp [h.1]) c1a_def u1_def t1_def c1b_def w1_def m1_def
  have h2 := padd_s2 (by rcases h1 with h | h <;> simp [h.1]) t2_def c2_def w2_def m2_def
  have h3 := padd_s3 (by rcases h2 with h | h <;> simp [h.1]) c3a_def u3_def t3_def c3b_def M_def
  have h4 := padd_s4 (by rcases h3 with h | h <;> simp [h.1]) k0_def r0_def c4_def t1'_def k1_def
    s1_def c5_def r1_def c6_def c7_def t2'_def r2_def c8_def k3_def q3_def
  rw [leLimbsToNat4, leLimbsToNat4] at *
  exact padd_combine hD h0 h1 h2 h3 h4

/-- A product of two field elements as the MDS closure leaves it: `uint256_mulmod` for `A * B`,
then again with `R⁻¹`, the result read back as four limbs. -/
theorem mds_prod {A B a82 a99 : Nat} {w0 w1 w2 w3 : Word}
    (h82 : A * B % leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64,
      4611686018427387904#64] = a82)
    (h99 : leLimbsToNat [BitVec.ofNat 64 (a82 >>> (64 * 0)), BitVec.ofNat 64 (a82 >>> (64 * 1)),
        BitVec.ofNat 64 (a82 >>> (64 * 2)), BitVec.ofNat 64 (a82 >>> (64 * 3))] *
      leLimbsToNat [14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64,
        2445952672640170197#64] %
      leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64,
        4611686018427387904#64] = a99)
    (w0_def : BitVec.ofNat 64 (a99 >>> 0) = w0) (w1_def : BitVec.ofNat 64 (a99 >>> 64) = w1)
    (w2_def : BitVec.ofNat 64 (a99 >>> 128) = w2) (w3_def : BitVec.ofNat 64 (a99 >>> 192) = w3) :
    leLimbsToNat [w0, w1, w2, w3] = Fp.mul A B ∧ Fp.mul A B < Fp.p := by
  rw [Fp.limbs_p] at h82 h99
  have h82' : a82 < 2 ^ (64 * 4) := by
    rw [← h82]; exact lt_trans (Nat.mod_lt _ Fp.p_pos) Fp.p_lt
  rw [AsmVerif.RiscV.Sym.cells4', leLimbsToNat_natToLeLimbs _ _ h82', Fp.limbs_rInv] at h99
  subst h82 h99 w0_def w1_def w2_def w3_def
  rw [AsmVerif.RiscV.Sym.cells4, leLimbsToNat_natToLeLimbs _ _ (lt_trans (Nat.mod_lt _ Fp.p_pos) Fp.p_lt)]
  exact ⟨rfl, Fp.mul_lt _ _⟩

theorem padd_lt {a b : Nat} (ha : a < Fp.p) (hb : b < Fp.p) : a + b < 2 ^ 256 ∧ a + b < 2 * Fp.p := by
  have := Fp.p_lt
  have : Fp.p < 2 ^ 255 := by decide +kernel
  omega

theorem fadd_lt (a b : Nat) : Fp.add a b < Fp.p := Nat.mod_lt _ Fp.p_pos

/-- An accumulator limb swapped with the product's, as the compiler commutes the first addend. -/
theorem limbs_swap0 (a b c d e f g h : Word) :
    leLimbsToNat [a, b, c, d] + leLimbsToNat [e, f, g, h] =
      leLimbsToNat [e, b, c, d] + leLimbsToNat [a, f, g, h] := by
  rw [leLimbsToNat4, leLimbsToNat4, leLimbsToNat4, leLimbsToNat4]; omega

theorem Fp.add_comm (a b : Nat) : Fp.add a b = Fp.add b a := by
  unfold Fp.add; rw [Nat.add_comm]

theorem Fp.pow5_lt (x : Nat) : Fp.pow5 x < Fp.p := Fp.mul_lt _ _

end Cases.Zip2005
