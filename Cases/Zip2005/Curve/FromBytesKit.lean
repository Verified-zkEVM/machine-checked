import Cases.Zip2005.Field.Sqrt.Alt
import Cases.Zip2005.Field.FromRaw
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Field.FpAdd
import Cases.Zip2005.Image.F_78025a1c

/-!
# `EpAffine::from_bytes`: the kit

Point decompression: the 255-bit `x` coordinate, the sign bit, `Fp::from_repr`
(inlined), `x³ + 5`, `sqrt_alt`, the sign fix-up by conditional negation, and the
`CtOption` masks. The guest code is branch-free; everything is a boolean word (`bw`)
or a mask (`-bw`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-! ### Boolean words, continued -/

theorem and_allOnes' (x : Word) : x &&& 18446744073709551615#64 = x := by
  have h : (18446744073709551615#64) = BitVec.allOnes 64 := by decide
  rw [h, BitVec.and_allOnes]

theorem zext_if8 (c : Prop) [Decidable c] :
    BitVec.zeroExtend 64 (if c then 1#8 else 0#8) = bw (decide c) := by
  by_cases h : c <;> simp [h, bw]

/-- `x &&& -flag`: `x` under a set flag, `0` under a clear one. -/
theorem and_negbw (x : Word) (a : Bool) : x &&& -(bw a) = if a then x else 0#64 := by
  cases a
  · simp [bw]
  · simp only [bw, if_true]
    rw [show -(1#64) = 18446744073709551615#64 by decide, and_allOnes']

/-- The xor-and-xor conditional select. -/
theorem sel_bw (a b : Word) (c : Bool) : ((a ^^^ b) &&& -(bw c)) ^^^ b = if c then a else b := by
  rw [and_negbw]
  cases c
  · simp
  · simp only [if_true]
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem not1_bw (a : Bool) : (bw a ^^^ 18446744073709551615#64) &&& 1#64 = bw (!a) := by
  cases a <;> decide

theorem and1_bw (a : Bool) : bw a &&& BitVec.zeroExtend 64 (BitVec.truncate 8 1#64) = bw a := by
  cases a <;> decide

theorem sext_neg_bw (a : Bool) :
    BitVec.signExtend 64 (BitVec.truncate 32 0#64 + -BitVec.truncate 32 (bw a)) = -(bw a) := by
  cases a <;> decide

theorem ite_bw (c a b : Bool) : (if c then bw a else bw b) = bw (if c then a else b) := by
  cases c <;> rfl

/-- The low bit of a value's low byte, as `to_repr` reads it. -/
theorem low_bit (n : Nat) :
    BitVec.zeroExtend 64 (extractByte (BitVec.ofNat 64 (n >>> 0)) 0) &&& 1#64 =
      bw (decide (n % 2 = 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.zero_mul]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by decide, Nat.and_one_is_mod]
  by_cases h : n % 2 = 1
  · simp [h, bw]
  · simp [h, bw]; omega

/-! ### The top word of the encoding -/

/-- The high half of a doubleword, reassembled from its bytes 4–7. -/
theorem bytes_word_hi (w : Word) :
    (BitVec.zeroExtend 64 (extractByte w 7) <<< 24 ||| BitVec.zeroExtend 64 (extractByte w 6) <<< 16) |||
      (BitVec.zeroExtend 64 (extractByte w 5) <<< 8 ||| BitVec.zeroExtend 64 (extractByte w 4)) =
      w >>> 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

/-- The sign bit (`tmp[31] >> 7`), as the guest computes it from the high half. -/
theorem sign_word (w : Word) :
    BitVec.signExtend 64 (BitVec.truncate 32 (w >>> 32) >>> 31) = bw w.msb := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.msb_eq_getLsbD_last]
  simp only [BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight,
    BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, bw]
  cases h : w[63] <;> interval_cases i <;> simp [h]

/-- Clearing the top bit (`tmp[31] &= 0x7f`) as the guest does it: shift left, shift right. -/
theorem shl1_shr1 (x : Word) : (x <<< 1) >>> 1 = x &&& 0x7fffffffffffffff#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  interval_cases i <;> simp

/-! ### `Fp::neg`, limb by limb

`p - y` by `sbb` from the constant limbs of `p`, then masked to `0` when `y = 0`. The
compiler folds the constant minuend: the borrow-in arrives as a mask `m` (`0` or all
ones) and each limb is `m - y_i`, corrected by the constant. -/

/-- Limbs 0 and 1. -/
theorem fneg_s1 {P0 P1 : Nat} (hP0 : P0 < 2 ^ 64) (hP1 : P1 < 2 ^ 64)
    {y0 y1 f0 c0 m1 c1 t1 g1 c2 s1 m2 d1 : Word}
    (hf0 : BitVec.ofNat 64 P0 + -y0 = f0)
    (hc0 : (if (BitVec.ofNat 64 P0).ult y0 = true then 1#64 else 0#64) = c0)
    (hm1 : -c0 = m1) (hc1 : (if m1.ult y1 = true then 1#64 else 0#64) = c1)
    (ht1 : m1 + -c1 = t1) (hg1 : m1 + -y1 = g1)
    (hc2 : (if (g1 + BitVec.ofNat 64 P1).ult g1 = true then 1#64 else 0#64) = c2)
    (hs1 : t1 + c2 = s1) (hm2 : s1.sshiftRight 63 = m2) (hd1 : g1 + BitVec.ofNat 64 P1 = d1) :
    (m2.toNat = 0 ∧ P0 + 2 ^ 64 * P1 = y0.toNat + 2 ^ 64 * y1.toNat + f0.toNat + 2 ^ 64 * d1.toNat) ∨
      (m2.toNat = 2 ^ 64 - 1 ∧
        P0 + 2 ^ 64 * P1 + 2 ^ 128 = y0.toNat + 2 ^ 64 * y1.toNat + f0.toNat + 2 ^ 64 * d1.toNat) := by
  have e0 := Bn.sub_fact hf0
  have k0 := Bn.ult_fact hc0
  rw [Bn.toNat_ofNat', Nat.mod_eq_of_lt hP0] at e0 k0
  have em1 : m1.toNat = (2 ^ 64 - c0.toNat) % 2 ^ 64 := by rw [← hm1, BitVec.toNat_neg]
  have k1 := Bn.ult_fact hc1
  have et := Bn.sub_fact ht1
  have eg := Bn.sub_fact hg1
  have ed := Bn.add_fact' hd1
  rw [Bn.toNat_ofNat', Nat.mod_eq_of_lt hP1] at ed
  have k2 := Bn.ult_fact hc2
  rw [hd1] at k2
  have es := Bn.add_fact' hs1
  have sm := Bn.sar_fact hm2
  have := f0.isLt; have := c0.isLt; have := m1.isLt; have := t1.isLt; have := g1.isLt
  have := s1.isLt; have := d1.isLt; have := y0.isLt; have := y1.isLt
  rcases k0 with ⟨k0, _⟩ | ⟨k0, _⟩ <;> rcases k1 with ⟨k1, _⟩ | ⟨k1, _⟩ <;>
    rcases k2 with ⟨k2, _⟩ | ⟨k2, _⟩ <;> omega

/-- Limb 2 (`p`'s limb 2 is `0`): borrow in as the mask `m2`, out as `m3`. -/
theorem fneg_s2 {m2 y2 c d g m3 : Word} (hm : m2.toNat = 0 ∨ m2.toNat = 2 ^ 64 - 1)
    (hc : (if m2.ult y2 = true then 1#64 else 0#64) = c) (hd : m2 + -c = d) (hg : m2 + -y2 = g)
    (hm3 : d.sshiftRight 63 = m3) :
    (m2.toNat = 0 →
      (m3.toNat = 0 ∧ y2.toNat = 0 ∧ g.toNat = 0) ∨ (m3.toNat = 2 ^ 64 - 1 ∧ y2.toNat + g.toNat = 2 ^ 64)) ∧
    (m2.toNat = 2 ^ 64 - 1 → m3.toNat = 2 ^ 64 - 1 ∧ y2.toNat + g.toNat + 1 = 2 ^ 64) := by
  have kc := Bn.ult_fact hc
  have ed := Bn.sub_fact hd
  have eg := Bn.sub_fact hg
  have sm := Bn.sar_fact hm3
  have := c.isLt; have := d.isLt; have := g.isLt; have := y2.isLt
  rcases hm with h | h <;> rcases kc with ⟨kc, _⟩ | ⟨kc, _⟩ <;> constructor <;> intro hh <;> omega

/-- Limb 3 (`p`'s limb 3 is `2^62`, folded as `y3 + (2^64 - 2^62)`). -/
theorem fneg_s3 {m3 y3 e3 d3 : Word} (hm : m3.toNat = 0 ∨ m3.toNat = 2 ^ 64 - 1)
    (he : y3 + 13835058055282163712#64 = e3) (hd : m3 + -e3 = d3) :
    (m3.toNat = 0 → d3.toNat + y3.toNat = 2 ^ 62 ∨ d3.toNat + y3.toNat = 2 ^ 62 + 2 ^ 64) ∧
    (m3.toNat = 2 ^ 64 - 1 →
      d3.toNat + y3.toNat + 1 = 2 ^ 62 ∨ d3.toNat + y3.toNat + 1 = 2 ^ 62 + 2 ^ 64) := by
  have ee := Bn.add_fact' he
  rw [Bn.toNat_ofNat'] at ee
  have ed := Bn.sub_fact hd
  have := e3.isLt; have := d3.isLt; have := y3.isLt
  rcases hm with h | h <;> constructor <;> intro hh <;> omega

/-- The whole `Fp::neg` chain on a canonical operand: the result is `Fp.sub 0 Y`. -/
theorem fneg_chain {y0 y1 y2 y3 f0 c0 m1 c1 t1 g1 c2 s1 m2 d1 cc dd g m3 e3 d3
    o1 o2 o3 z r0 r1 r2 r3 : Word}
    (hf0 : 11037532056220336129#64 + -y0 = f0)
    (hc0 : (if (11037532056220336129#64).ult y0 = true then 1#64 else 0#64) = c0)
    (hm1 : -c0 = m1) (hc1 : (if m1.ult y1 = true then 1#64 else 0#64) = c1)
    (ht1 : m1 + -c1 = t1) (hg1 : m1 + -y1 = g1)
    (hc2 : (if (g1 + 2469829653914515739#64).ult g1 = true then 1#64 else 0#64) = c2)
    (hs1 : t1 + c2 = s1) (hm2 : s1.sshiftRight 63 = m2) (hd1 : g1 + 2469829653914515739#64 = d1)
    (hcc : (if m2.ult y2 = true then 1#64 else 0#64) = cc) (hdd : m2 + -cc = dd) (hg : m2 + -y2 = g)
    (hm3 : dd.sshiftRight 63 = m3)
    (he3 : y3 + 13835058055282163712#64 = e3) (hd3 : m3 + -e3 = d3)
    (ho1 : y1 ||| y0 = o1) (ho2 : y2 ||| y3 = o2) (ho3 : o1 ||| o2 = z)
    (hz : (if z.ult 1#64 = true then 1#64 else 0#64) = o3)
    (hr0 : o3 + 18446744073709551615#64 &&& f0 = r0)
    (hr1 : o3 + 18446744073709551615#64 &&& d1 = r1)
    (hr2 : o3 + 18446744073709551615#64 &&& g = r2)
    (hr3 : o3 + 18446744073709551615#64 &&& d3 = r3)
    (hY : leLimbsToNat [y0, y1, y2, y3] < Fp.p) :
    leLimbsToNat [r0, r1, r2, r3] = Fp.sub 0 (leLimbsToNat [y0, y1, y2, y3]) := by
  have e1 := fneg_s1 (by decide) (by decide) hf0 hc0 hm1 hc1 ht1 hg1 hc2 hs1 hm2 hd1
  have hm2' : m2.toNat = 0 ∨ m2.toNat = 2 ^ 64 - 1 := by rcases e1 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have e2 := fneg_s2 hm2' hcc hdd hg hm3
  have hm3' : m3.toNat = 0 ∨ m3.toNat = 2 ^ 64 - 1 := by
    rcases hm2' with h | h
    · rcases e2.1 h with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
    · exact Or.inr (e2.2 h).1
  have e3 := fneg_s3 hm3' he3 hd3
  -- the zero test
  have hz' : z = 0#64 ↔ y0 = 0#64 ∧ y1 = 0#64 ∧ y2 = 0#64 ∧ y3 = 0#64 := by
    rw [← ho3, ← ho1, ← ho2, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff]
    constructor
    · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨b, a, c, d⟩
    · rintro ⟨a, b, c, d⟩; exact ⟨⟨b, a⟩, c, d⟩
  have ko := Bn.ult_fact hz
  rw [show (1#64).toNat = 1 from rfl] at ko
  have hp : Fp.p = 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 4611686018427387904 := by
    decide +kernel
  have eY : leLimbsToNat [y0, y1, y2, y3] =
      y0.toNat + 2 ^ 64 * y1.toNat + 2 ^ 128 * y2.toNat + 2 ^ 192 * y3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have eR : leLimbsToNat [r0, r1, r2, r3] =
      r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have := y0.isLt; have := y1.isLt; have := y2.isLt; have := y3.isLt
  have := f0.isLt; have := d1.isLt; have := g.isLt; have := d3.isLt
  rw [eY, hp] at hY
  rw [eR, Fp.sub, eY, hp]
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

/-! ### Representatives -/

/-- The canonical representative behind a Montgomery value (`Fp::to_repr`). -/
def Fp.fromMont (a : Nat) : Nat := a * Fp.rInv % Fp.p

theorem Fp.mul_mod_rInv (a : Nat) : a * Fp.rInv % Fp.p * 2 ^ 256 % Fp.p = a % Fp.p := by
  rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, Fp.rInv_spec, Nat.mul_one]

/-- A Montgomery value whose representative is `0` is `0`. -/
theorem Fp.fromMont_eq_zero {y : Nat} (hy : y < Fp.p) (h : Fp.fromMont y = 0) : y = 0 := by
  have h1 := Fp.mul_mod_rInv y
  rw [Fp.fromMont] at h
  rw [h, Nat.zero_mul, Nat.zero_mod, Nat.mod_eq_of_lt hy] at h1
  exact h1.symm

theorem Fp.R2_rInv : Fp.R2 * Fp.rInv % Fp.p = Fp.R := by decide +kernel
theorem Fp.R_rInv : Fp.R * Fp.rInv % Fp.p = 1 := by decide +kernel
theorem Fp.p_odd : Fp.p % 2 = 1 := by decide +kernel

/-- `Fp.mul X R2` is `X·R`; it vanishes only at `X = 0`. -/
theorem Fp.mul_R2_eq_zero {X : Nat} (hX : X < Fp.p) (h : Fp.mul X Fp.R2 = 0) : X = 0 := by
  have e : Fp.mul X Fp.R2 = X * Fp.R % Fp.p := by
    rw [Fp.mul, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, Fp.R2_rInv]
  rw [e] at h
  have h2 : X * Fp.R % Fp.p * Fp.rInv % Fp.p = X % Fp.p := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod, Fp.R_rInv, Nat.mul_one]
  rw [h, Nat.zero_mul, Nat.zero_mod, Nat.mod_eq_of_lt hX] at h2
  exact h2.symm

theorem Fp.sub_zero_lt (y : Nat) : Fp.sub 0 y < Fp.p := Nat.mod_lt _ Fp.p_pos

/-- The representative of `-y`. -/
theorem Fp.fromMont_neg {y : Nat} (hy : y < Fp.p) :
    Fp.fromMont (Fp.sub 0 y) = (Fp.p - Fp.fromMont y) % Fp.p := by
  unfold Fp.fromMont Fp.sub
  have hr := Nat.mod_lt (y * Fp.rInv) Fp.p_pos
  have hA := Nat.mod_lt ((0 + Fp.p - y) % Fp.p * Fp.rInv) Fp.p_pos
  have key : ((0 + Fp.p - y) % Fp.p * Fp.rInv % Fp.p + y * Fp.rInv % Fp.p) % Fp.p = 0 := by
    rw [Nat.mod_mul_mod, ← Nat.add_mod, ← Nat.add_mul, Nat.zero_add, Nat.sub_add_cancel hy.le,
      Nat.mul_mod_right]
  generalize (0 + Fp.p - y) % Fp.p * Fp.rInv % Fp.p = A at hA key ⊢
  generalize y * Fp.rInv % Fp.p = r at hr key ⊢
  have hdm := Nat.div_add_mod (A + r) Fp.p
  rw [key, Nat.add_zero] at hdm
  have hq : (A + r) / Fp.p < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hp := Fp.p_pos
  generalize (A + r) / Fp.p = q at hdm hq
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
  · have : q = 0 := by omega
    subst this
    rw [Nat.mul_zero] at hdm
    have : A = 0 := by omega
    have : r = 0 := by omega
    subst A r
    rw [Nat.sub_zero, Nat.mod_self]
  · subst hq
    rw [Nat.mul_one] at hdm
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `(-y)² = y²`. -/
theorem Fp.mul_neg_neg {y : Nat} (hy : y < Fp.p) : Fp.mul (Fp.sub 0 y) (Fp.sub 0 y) = Fp.mul y y := by
  rcases Nat.eq_zero_or_pos y with h0 | hpos
  · subst h0; rw [Fp.sub, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
  · have e : Fp.sub 0 y = Fp.p - y := by
      rw [Fp.sub, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [e, Fp.mul, Fp.mul]
    obtain ⟨k, hk⟩ : ∃ k, Fp.p = y + k := ⟨Fp.p - y, by omega⟩
    have hk' : Fp.p - y = k := by omega
    rw [hk']
    congr 2
    have : k * k + Fp.p * (2 * y) = Fp.p * Fp.p + y * y := by rw [hk]; ring
    rw [← Nat.add_mul_mod_self_left (k * k) Fp.p (2 * y), this, Nat.mul_comm Fp.p Fp.p,
      Nat.add_comm, Nat.add_mul_mod_self_left]

/-- The sign agrees with the parity: `y` is kept. -/
theorem parity_same {r : Nat} {b : Bool} (hf : decide (r % 2 = 1) = b) :
    r % 2 = if b then 1 else 0 := by
  cases b
  · rw [decide_eq_false_iff_not] at hf; simp only [Bool.false_eq_true, if_false]; omega
  · rw [decide_eq_true_eq] at hf; simp only [if_true]; exact hf

/-- The sign disagrees with the parity: `-y` (representative `p - r`, `p` odd) has the other one. -/
theorem parity_flip {r p : Nat} {b : Bool} (hp : p % 2 = 1) (hr0 : r ≠ 0) (hr : r < p)
    (hf : decide (r % 2 = 1) ≠ b) : (p - r) % p % 2 = if b then 1 else 0 := by
  have hlt : p - r < p := by omega
  rw [Nat.mod_eq_of_lt hlt]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    have : r % 2 = 1 := by by_contra hc; exact hf (decide_eq_false hc)
    omega
  · simp only [if_true]
    have : ¬ r % 2 = 1 := fun hc => hf (decide_eq_true hc)
    omega

/-- The right-hand side `x³ + 5` of the Pallas equation, on Montgomery values. -/
def Fp.rhs (x : Nat) : Nat := Fp.add (Fp.mul 5 Fp.R2) (Fp.mul (Fp.mul x x) x)

/-- `EpAffine::from_bytes` on the 32 bytes `b0 ‖ b1 ‖ b2 ‖ b3` (little-endian words): `X` is
    the low 255 bits, `ysign` the top bit. The output is `x`, `y` (Montgomery values, canonical)
    and the `CtOption` flag `f`. Accepted (`f = 1`): `X` is canonical and either the identity
    encoding (`X = 0`, sign clear; output `(0, 0)`) or a point with `x = X·R`, `y² = x³ + 5`
    and the parity of `y`'s representative equal to `ysign` (unless `y = 0`). Rejected
    (`f = 0`): `X ≥ p`, or `x³ + 5` is `0` or a non-square, witnessed by a square root of
    `ROOT_OF_UNITY · (x³ + 5)`. -/
def FromBytesPost (b0 b1 b2 b3 : Word) (x y : Nat) (f : BitVec 8) : Prop :=
  let X := leLimbsToNat [b0, b1, b2, b3 &&& 0x7fffffffffffffff#64]
  let ysign := b3.msb
  x < Fp.p ∧ y < Fp.p ∧
    ((f = 1#8 ∧ X < Fp.p ∧
        ((X = 0 ∧ ysign = false ∧ x = 0 ∧ y = 0) ∨
          (x = Fp.mul X Fp.R2 ∧ Fp.mul y y = Fp.rhs x ∧
            (y ≠ 0 → Fp.fromMont y % 2 = if ysign then 1 else 0)))) ∨
      (f = 0#8 ∧ (Fp.p ≤ X ∨ Fp.rhs (Fp.mul X Fp.R2) = 0 ∨
        ∃ r, r < Fp.p ∧ Fp.mul r r = Fp.mul Fp.rootOfUnity (Fp.rhs (Fp.mul X Fp.R2)))))

/-- The postcondition from the flags and values the executor leaves: `canon` (the encoding is
    canonical), `xm` (the masked `x`), `zero`/`ident` (the identity test), `R` and `sq` (the
    square root and its flag), `Y` (the `CtOption` value) and `flip` (the sign correction). -/
theorem fb_post {b0 b1 b2 b3 : Word} {X xm R Y : Nat} {canon zero ident sq flip : Bool}
    (hX : leLimbsToNat [b0, b1, b2, b3 &&& 0x7fffffffffffffff#64] = X)
    (hcanon : decide (X < Fp.p) = canon)
    (hxm : (if canon then Fp.mul X Fp.R2 else 0) = xm)
    (hzero : zero = true ↔ xm = 0)
    (hident : (!b3.msb && zero) = ident)
    (hR : R < Fp.p)
    (hsq : decide (Fp.mul R R = Fp.rhs xm) = sq)
    (halt : Fp.rhs xm = 0 ∨
      (Fp.mul R R = Fp.rhs xm ↔ ¬ Fp.mul R R = Fp.mul Fp.rootOfUnity (Fp.rhs xm)))
    (hY : Y = if sq then R else 0)
    (hflip : (decide (Fp.fromMont Y % 2 = 1) != b3.msb) = flip) :
    FromBytesPost b0 b1 b2 b3 (if !ident then xm else 0)
      (if !ident then (if flip then Fp.sub 0 Y else Y) else 0)
      (if (if !ident then sq else ident) && canon then 1#8 else 0#8) := by
  have hxm_lt : xm < Fp.p := by
    rw [← hxm]; cases canon
    · simp only [Bool.false_eq_true, if_false]; exact Fp.p_pos
    · simp only [if_true]; exact Fp.mul_lt _ _
  have hYlt : Y < Fp.p := by
    rw [hY]; cases sq
    · simp only [Bool.false_eq_true, if_false]; exact Fp.p_pos
    · simp only [if_true]; exact hR
  have hYf_lt : (if flip then Fp.sub 0 Y else Y) < Fp.p := by
    cases flip
    · simp only [Bool.false_eq_true, if_false]; exact hYlt
    · simp only [if_true]; exact Fp.sub_zero_lt _
  unfold FromBytesPost
  dsimp only
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · cases ident
    · simp only [Bool.not_false, if_true]; exact hxm_lt
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]; exact Fp.p_pos
  · cases ident
    · simp only [Bool.not_false, if_true]; exact hYf_lt
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]; exact Fp.p_pos
  · cases canon
    · -- `X ≥ p`: rejected
      right
      simp only [Bool.and_false, Bool.false_eq_true, if_false, true_and]
      exact Or.inl (Nat.not_lt.mp (of_decide_eq_false hcanon))
    · have hXlt : X < Fp.p := of_decide_eq_true hcanon
      have hxm' : xm = Fp.mul X Fp.R2 := by rw [← hxm]; exact if_pos rfl
      cases ident
      · -- not the identity encoding: the square-root flag decides
        simp only [Bool.not_false, if_true, Bool.and_true]
        cases sq
        · -- rejected: `x³ + 5` is zero or a non-square
          right
          simp only [Bool.false_eq_true, if_false, true_and]
          right
          rw [← hxm']
          have hne : ¬ Fp.mul R R = Fp.rhs xm := of_decide_eq_false hsq
          rcases halt with h | h
          · exact Or.inl h
          · exact Or.inr ⟨R, hR, by_contra fun hn => hne (h.mpr hn)⟩
        · -- accepted: a point on the curve with the requested sign
          left
          have hYR : Y = R := by rw [hY]; exact if_pos rfl
          have hsqR : Fp.mul R R = Fp.rhs xm := of_decide_eq_true hsq
          refine ⟨rfl, hXlt, Or.inr ⟨hxm', ?_, ?_⟩⟩
          · cases flip
            · simp only [Bool.false_eq_true, if_false]; rw [hYR]; exact hsqR
            · simp only [if_true]; rw [Fp.mul_neg_neg hYlt, hYR]; exact hsqR
          · intro hne
            cases flip
            · simp only [Bool.false_eq_true, if_false] at hne ⊢
              exact parity_same (bne_eq_false_iff_eq.mp hflip)
            · simp only [if_true] at hne ⊢
              rw [Fp.fromMont_neg hYlt]
              have hr0 : Fp.fromMont Y ≠ 0 := by
                intro h0
                apply hne
                rw [Fp.fromMont_eq_zero hYlt h0, Fp.sub, Nat.zero_add, Nat.sub_zero, Nat.mod_self]
              exact parity_flip Fp.p_odd hr0 (Nat.mod_lt _ Fp.p_pos) (bne_iff_ne.mp hflip)
      · -- the identity encoding
        simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_true]
        left
        rw [Bool.and_eq_true] at hident
        obtain ⟨hs, hz⟩ := hident
        have hxm0 : xm = 0 := hzero.mp hz
        refine ⟨trivial, hXlt, Or.inl ⟨Fp.mul_R2_eq_zero hXlt (hxm'.symm.trans hxm0), ?_, trivial, trivial⟩⟩
        simpa using hs

end Cases.Zip2005
