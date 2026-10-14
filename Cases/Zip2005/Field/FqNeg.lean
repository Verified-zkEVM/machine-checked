import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Field.Fq

/-!
# `Fq::neg`, inline

`derive_unchecked` negates `ask` in place: the borrow chain of `fneg_chain` with `q`'s limbs.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

/-- The field difference on representatives. -/
def Fq.sub (a b : Nat) : Nat := (a + Fq.q - b) % Fq.q

theorem Fq.sub_lt (a b : Nat) : Fq.sub a b < Fq.q := Nat.mod_lt _ Fq.q_pos

/-- The whole inline `Fq::neg` chain (as `derive_unchecked` schedules it) on a canonical operand:
the result is `Fq.sub 0 Y`. -/
theorem fqneg_chain {y0 y1 y2 y3 f0 c0 m1 c1 t1 g1 c2 s1 m2 cc dd g m3 d3
    o1 o2 o3 z r0 r1 r2 r3 : Word}
    (hf0 : 10108024940646105089#64 + -y0 = f0)
    (hc0 : (if (10108024940646105089#64).ult y0 = true then 1#64 else 0#64) = c0)
    (hm1 : -c0 = m1) (hc1 : (if m1.ult y1 = true then 1#64 else 0#64) = c1)
    (ht1 : m1 + -c1 = t1) (hg1 : m1 + -y1 = g1)
    (hc2 : (if (g1 + 2469829653919213789#64).ult g1 = true then 1#64 else 0#64) = c2)
    (hs1 : t1 + c2 = s1) (hm2 : s1.sshiftRight 63 = m2)
    (hcc : (if m2.ult y2 = true then 1#64 else 0#64) = cc) (hdd : m2 + -cc = dd) (hg : m2 + -y2 = g)
    (hm3 : dd.sshiftRight 63 = m3)
    (hd3 : m3 + -(y3 + 13835058055282163712#64) = d3)
    (ho1 : y1 ||| y0 = o1) (ho2 : y2 ||| y3 = o2) (ho3 : o1 ||| o2 = z)
    (hz : (if z.ult 1#64 = true then 1#64 else 0#64) = o3)
    (hr0 : o3 + 18446744073709551615#64 &&& f0 = r0)
    (hr1 : o3 + 18446744073709551615#64 &&& g1 + 2469829653919213789#64 = r1)
    (hr2 : o3 + 18446744073709551615#64 &&& g = r2)
    (hr3 : o3 + 18446744073709551615#64 &&& d3 = r3)
    (hY : leLimbsToNat [y0, y1, y2, y3] < Fq.q) :
    leLimbsToNat [r0, r1, r2, r3] = Fq.sub 0 (leLimbsToNat [y0, y1, y2, y3]) := by
  have e1 := fneg_s1 (by decide) (by decide) hf0 hc0 hm1 hc1 ht1 hg1 hc2 hs1 hm2 rfl
  have hm2' : m2.toNat = 0 ∨ m2.toNat = 2 ^ 64 - 1 := by rcases e1 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have e2 := fneg_s2 hm2' hcc hdd hg hm3
  have hm3' : m3.toNat = 0 ∨ m3.toNat = 2 ^ 64 - 1 := by
    rcases hm2' with h | h
    · rcases e2.1 h with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    · exact Or.inr (e2.2 h).1
  have e3 := fneg_s3 hm3' rfl hd3
  -- the zero test
  have hz' : z = 0#64 ↔ y0 = 0#64 ∧ y1 = 0#64 ∧ y2 = 0#64 ∧ y3 = 0#64 := by
    rw [← ho3, ← ho1, ← ho2, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff]
    constructor
    · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨b, a, c, d⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨⟨b, a⟩, c, d⟩
  have ko := Bn.ult_fact hz
  rw [show (1#64).toNat = 1 from rfl] at ko
  have hp : Fq.q = 10108024940646105089 + 2 ^ 64 * 2469829653919213789 + 2 ^ 192 * 4611686018427387904 := by
    decide +kernel
  have eY : leLimbsToNat [y0, y1, y2, y3] =
      y0.toNat + 2 ^ 64 * y1.toNat + 2 ^ 128 * y2.toNat + 2 ^ 192 * y3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have eR : leLimbsToNat [r0, r1, r2, r3] =
      r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have := y0.isLt; have := y1.isLt; have := y2.isLt; have := y3.isLt
  have := f0.isLt; have := (g1 + 2469829653919213789#64).isLt; have := g.isLt; have := d3.isLt
  rw [eY, hp] at hY
  rw [eR, Fq.sub, eY, hp]
  by_cases h0 : y0 = 0#64 ∧ y1 = 0#64 ∧ y2 = 0#64 ∧ y3 = 0#64
  · -- `y = 0`: the mask clears the result
    have hz0 : z.toNat = 0 := by rw [hz'.mpr h0]; rfl
    have ho3' : o3.toNat = 1 := by rcases ko with ⟨h, _⟩ | ⟨_, h⟩ <;> omega
    have x0 := Bn.mask_and (by omega) hr0
    have x1 := Bn.mask_and (by omega) hr1
    have x2 := Bn.mask_and (by omega) hr2
    have x3 := Bn.mask_and (by omega) hr3
    obtain ⟨a, b, c, d⟩ := h0
    subst a b c d
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at *
    rw [Nat.sub_zero, Nat.mod_self]
    omega
  · -- `y ≠ 0`: the result is `p - y`
    have hz0 : z.toNat ≠ 0 := by
      intro h; exact h0 (hz'.mp (BitVec.eq_of_toNat_eq h))
    have ho3' : o3.toNat = 0 := by rcases ko with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
    have x0 := Bn.mask_and (by omega) hr0
    have x1 := Bn.mask_and (by omega) hr1
    have x2 := Bn.mask_and (by omega) hr2
    have x3 := Bn.mask_and (by omega) hr3
    have hne : 0 < y0.toNat + 2 ^ 64 * y1.toNat + 2 ^ 128 * y2.toNat + 2 ^ 192 * y3.toNat := by
      rcases Nat.eq_zero_or_pos (y0.toNat + 2 ^ 64 * y1.toNat + 2 ^ 128 * y2.toNat + 2 ^ 192 * y3.toNat)
        with h | h
      · exfalso; apply h0
        refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_,
          BitVec.eq_of_toNat_eq ?_⟩ <;> simp only [BitVec.toNat_ofNat, Nat.zero_mod] <;> omega
      · exact h
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rcases e1 with ⟨h1, e1⟩ | ⟨h1, e1⟩
    · rcases e2.1 h1 with ⟨h2, e2a, e2b⟩ | ⟨h2, e2'⟩
      · rcases e3.1 h2 with e3' | e3' <;> omega
      · rcases e3.2 h2 with e3' | e3' <;> omega
    · obtain ⟨h2, e2'⟩ := e2.2 h1
      rcases e3.2 h2 with e3' | e3' <;> omega

end Cases.Zip2005
