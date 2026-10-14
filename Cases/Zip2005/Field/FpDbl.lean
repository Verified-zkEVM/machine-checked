/-
  Cases.Zip2005.FpDbl

  Field doubling as the guest compiles `Fp::double` (`self + self`, inlined in `Ep::double`):
  the sum's limbs come from shifts (`a_i <<< 1 ||| a_{i-1} >>> 63`) instead of an `adc`
  chain, and the conditional subtraction of `p` is `mont_sub_tail`'s. At most sites the
  top limb's `- p3` is fused into the shift -- `(a2 >>> 63) ||| 0xc000000000000000` added
  to `a3 <<< 1` -- which re-associates limb 3 of the borrow chain (`tail_s3f`).

  The stage-1 shape here is `mont_sub_tail`'s own (`d1 + (v112 - 1)`, carry against `d1`);
  the sites that schedule it rotated (`v112 + (-1 + d1)`, carry against `v112 - 1`) are
  brought to this shape by `ac_rfl` and `Bn.carry_either`.
-/

import Cases.Zip2005.Field.FpAdd

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

namespace Bn

/-- The carry of a sum compares it with either addend. -/
theorem carry_either {x y v w : Word} (hv : x + y = v)
    (h : (if v.ult x = true then 1#64 else 0#64) = w) :
    (if v.ult y = true then 1#64 else 0#64) = w := by
  subst h; subst hv
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq]
  by_cases hc : x.toNat + y.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc, if_neg (by omega), if_neg (by omega)]
  · rw [show (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat - 2 ^ 64 by omega,
      if_pos (by omega), if_pos (by omega)]

/-- `a <<< 1` and `b >>> 63` share no bit. -/
theorem shl1_and_shr63 (a b : Word) : a <<< 1 &&& b >>> 63 = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr; intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_zero]
  by_cases h0 : i = 0
  · subst h0; simp
  · rw [BitVec.getLsbD_of_ge b (63 + i) (by omega)]; simp

/-- `a <<< 1 ||| b >>> 63` is the sum of its two disjoint parts. -/
theorem shl1_or_shr63 {a b s t v : Word} (hs : a <<< 1 = s) (ht : b >>> 63 = t)
    (h : s ||| t = v) : v.toNat = s.toNat + t.toNat := by
  subst hs ht h
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (shl1_and_shr63 a b), BitVec.toNat_add]
  have e1 := shl_fact (a := a) (k := 1) (by decide) rfl
  have e2 := shr_fact (a := b) (k := 63) rfl
  have := (a <<< 1).isLt; have := b.isLt; have := a.isLt
  simp only [Nat.reducePow, Nat.reduceSub] at e1 e2 ⊢
  apply Nat.mod_eq_of_lt
  omega

end Bn

/-- The shifted limbs of `2A`, `A < 2^255`: the top limb is `s3 + t2`, not yet combined. -/
theorem fdbl_limbs {a0 a1 a2 a3 d0 s1 t0 d1 s2 t1 d2 s3 t2 : Word}
    (hd0 : a0 <<< 1 = d0) (hs1 : a1 <<< 1 = s1) (ht0 : a0 >>> 63 = t0) (hd1 : s1 ||| t0 = d1)
    (hs2 : a2 <<< 1 = s2) (ht1 : a1 >>> 63 = t1) (hd2 : s2 ||| t1 = d2)
    (hs3 : a3 <<< 1 = s3) (ht2 : a2 >>> 63 = t2)
    (hA : leLimbsToNat [a0, a1, a2, a3] < 2 ^ 255) :
    d0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * (s3.toNat + t2.toNat) =
      2 * leLimbsToNat [a0, a1, a2, a3] := by
  have e0 := Bn.shl_fact (by decide) hd0
  have e1 := Bn.shl_fact (by decide) hs1
  have e2 := Bn.shl_fact (by decide) hs2
  have e3 := Bn.shl_fact (by decide) hs3
  have f0 := Bn.shr_fact ht0
  have f1 := Bn.shr_fact ht1
  have f2 := Bn.shr_fact ht2
  have g1 := Bn.shl1_or_shr63 hs1 ht0 hd1
  have g2 := Bn.shl1_or_shr63 hs2 ht1 hd2
  simp only [leLimbsToNat_cons, leLimbsToNat_nil] at hA ⊢
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := d0.isLt; have := s1.isLt; have := s2.isLt; have := s3.isLt
  simp only [Nat.reducePow, Nat.reduceSub] at *
  omega

/-- Limb 3 of the borrow chain at a fused site: `(t2 ||| -p3) + s3`, then the borrow. -/
theorem tail_s3f {t2 s3 v362 v364 v365 v366 v367 v368 v369 v370 : Word}
    (h127 : v362.toNat = 0 ∨ v362.toNat = 2 ^ 64 - 1) (ht2 : t2.toNat ≤ 1) (hs3 : s3.toNat % 2 = 0)
    (v364_def : t2 ||| 13835058055282163712#64 = v364)
    (v365_def : v364 + s3 = v365)
    (v366_def : (if v365.ult v364 = true then 1#64 else 0#64) = v366)
    (v367_def : v366 + v362 = v367)
    (v368_def : v365 + v362 = v368)
    (v369_def : (if v368.ult v365 = true then 1#64 else 0#64) = v369)
    (v370_def : v367 + v369 = v370) :
    v370.toNat ≤ 1 ∧
      (v362.toNat = 0 → s3.toNat + t2.toNat + 2 ^ 64 = 2 ^ 62 + v368.toNat + 2 ^ 64 * v370.toNat) ∧
      (v362.toNat = 2 ^ 64 - 1 →
        s3.toNat + t2.toNat + 2 ^ 64 = 2 ^ 62 + v368.toNat + 2 ^ 64 * v370.toNat + 1) := by
  have h364 : v364.toNat = t2.toNat + 13835058055282163712 := by
    rcases (by omega : t2.toNat = 0 ∨ t2.toNat = 1) with h | h
    · have : t2 = 0#64 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      subst this; rw [← v364_def, h]; decide
    · have : t2 = 1#64 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      subst this; rw [← v364_def, h]; decide
  bn_lin
  rcases h127 with h1 | h1 <;>
  rcases (by omega : v366.toNat = 0 ∨ v366.toNat = 1) with h2 | h2 <;>
  rcases (by omega : v369.toNat = 0 ∨ v369.toNat = 1) with h3 | h3 <;>
  omega

/-- `mont_sub_tail` with the fused limb 3: the input `T` has top limb `s3 + t2`. -/
theorem fdbl_sub_tail {d0 d1 d2 s3 t2 : Word}
    {v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127 v364 v365 v366 v367 v368 v369 v370
      v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v150 v151 v152 : Word}
    (ht2 : t2.toNat ≤ 1) (hs3 : s3.toNat % 2 = 0)
    (v112_def : (if (d0 + 7409212017489215487#64).ult d0 = true then 1#64 else 0#64) = v112)
    (v116_def : d1 + (v112 + 18446744073709551615#64) = v116)
    (v117_def : (if v116.ult d1 = true then 1#64 else 0#64) = v117)
    (v118_def : v112 + (18446744073709551615#64 + v117) = v118)
    (v120_def : (if (v116 + 15976914419795035877#64).ult v116 = true then 1#64 else 0#64) = v120)
    (v121_def : v118 + v120 = v121)
    (v123_def : (v121 + 18446744073709551615#64).sshiftRight 63 = v123)
    (v124_def : v123 + d2 = v124)
    (v125_def : (if v124.ult v123 = true then 1#64 else 0#64) = v125)
    (v126_def : v123 + v125 = v126)
    (v127_def : v126.sshiftRight 63 = v127)
    (v364_def : t2 ||| 13835058055282163712#64 = v364)
    (v365_def : v364 + s3 = v365)
    (v366_def : (if v365.ult v364 = true then 1#64 else 0#64) = v366)
    (v367_def : v366 + v127 = v367)
    (v368_def : v365 + v127 = v368)
    (v369_def : (if v368.ult v365 = true then 1#64 else 0#64) = v369)
    (v370_def : v367 + v369 = v370)
    (v137_def : v370 + 18446744073709551615#64 &&& 11037532056220336129#64 = v137)
    (v138_def : v137 + (d0 + 7409212017489215487#64) = v138)
    (v139_def : (if v138.ult v137 = true then 1#64 else 0#64) = v139)
    (v140_def : v370 + 18446744073709551615#64 &&& 2469829653914515739#64 = v140)
    (v141_def : v140 + (v116 + 15976914419795035877#64) = v141)
    (v142_def : (if v141.ult v140 = true then 1#64 else 0#64) = v142)
    (v143_def : v141 + v139 = v143)
    (v144_def : (if v143.ult v141 = true then 1#64 else 0#64) = v144)
    (v145_def : v142 + v144 = v145)
    (v146_def : v145 + v124 = v146)
    (v147_def : (if v146.ult v145 = true then 1#64 else 0#64) = v147)
    (v150_def : v370 + 18446744073709551615#64 &&& 4611686018427387904#64 = v150)
    (v151_def : v150 + v368 = v151)
    (v152_def : v151 + v147 = v152) :
    let T := d0.toNat + 2 ^ 64 * d1.toNat + 2 ^ 128 * d2.toNat + 2 ^ 192 * (s3.toNat + t2.toNat)
    let R := v138.toNat + 2 ^ 64 * v143.toNat + 2 ^ 128 * v146.toNat + 2 ^ 192 * v152.toNat
    (T < (11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62) → R = T) ∧
      ((11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62) ≤ T →
        R + (11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62) = T) := by
  intro T R
  obtain ⟨h121, e1⟩ := tail_s1 (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v112_def v116_def v117_def v118_def v120_def v121_def
  have e2 := tail_s2 h121 v123_def v124_def v125_def v126_def v127_def
  have h127 : v127.toNat = 0 ∨ v127.toNat = 2 ^ 64 - 1 := by omega
  obtain ⟨h135, e3, e3'⟩ := tail_s3f h127 ht2 hs3 v364_def v365_def v366_def v367_def v368_def
    v369_def v370_def
  obtain ⟨e4, e4'⟩ := tail_s4 (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) (v94 := d0) (v116 := v116) (v124 := v124) (d3 := v368) h135
    v137_def v138_def v139_def v140_def v141_def v142_def v143_def v144_def v145_def v146_def
    v147_def v150_def v151_def v152_def
  exact tail_combine (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) rfl rfl rfl rfl e1 e2 h135 e3 e3' e4 e4' v138.isLt
    v143.isLt v146.isLt v152.isLt v124.isLt (d0 + 7409212017489215487#64).isLt
    (v116 + 15976914419795035877#64).isLt v368.isLt

/-- The two halves of a conditional subtraction, as `T mod p` for `T < 2p`. -/
theorem reduce_of_tail {T R : Nat}
    (tl : (T < (11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62) → R = T) ∧
      ((11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62) ≤ T →
        R + (11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62) = T))
    (hT : T < 2 * Fp.p) : R = T % Fp.p := by
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by
    decide +kernel] at tl
  obtain ⟨h1, h2⟩ := tl
  rcases Nat.lt_or_ge T Fp.p with h | h
  · rw [Nat.mod_eq_of_lt h]; exact h1 h
  · have := h2 h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

theorem leLimbsToNat_four_eq (r0 r1 r2 r3 : Word) :
    leLimbsToNat [r0, r1, r2, r3] =
      r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * r2.toNat + 2 ^ 192 * r3.toNat := by
  simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring

/-- `Fp::double` at a fused site: shifted limbs, fused limb 3, conditional subtraction. -/
theorem fdbl_chain_fused {a0 a1 a2 a3 d0 s1 t0 d1 s2 t1 d2 s3 t2 : Word}
    {v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127 v364 v365 v366 v367 v368 v369 v370
      v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v150 v151 v152 : Word}
    (hd0 : a0 <<< 1 = d0) (hs1 : a1 <<< 1 = s1) (ht0 : a0 >>> 63 = t0) (hd1 : s1 ||| t0 = d1)
    (hs2 : a2 <<< 1 = s2) (ht1 : a1 >>> 63 = t1) (hd2 : s2 ||| t1 = d2)
    (hs3 : a3 <<< 1 = s3) (ht2 : a2 >>> 63 = t2)
    (v112_def : (if (d0 + 7409212017489215487#64).ult d0 = true then 1#64 else 0#64) = v112)
    (v116_def : d1 + (v112 + 18446744073709551615#64) = v116)
    (v117_def : (if v116.ult d1 = true then 1#64 else 0#64) = v117)
    (v118_def : v112 + (18446744073709551615#64 + v117) = v118)
    (v120_def : (if (v116 + 15976914419795035877#64).ult v116 = true then 1#64 else 0#64) = v120)
    (v121_def : v118 + v120 = v121)
    (v123_def : (v121 + 18446744073709551615#64).sshiftRight 63 = v123)
    (v124_def : v123 + d2 = v124)
    (v125_def : (if v124.ult v123 = true then 1#64 else 0#64) = v125)
    (v126_def : v123 + v125 = v126)
    (v127_def : v126.sshiftRight 63 = v127)
    (v364_def : t2 ||| 13835058055282163712#64 = v364)
    (v365_def : v364 + s3 = v365)
    (v366_def : (if v365.ult v364 = true then 1#64 else 0#64) = v366)
    (v367_def : v366 + v127 = v367)
    (v368_def : v365 + v127 = v368)
    (v369_def : (if v368.ult v365 = true then 1#64 else 0#64) = v369)
    (v370_def : v367 + v369 = v370)
    (v137_def : v370 + 18446744073709551615#64 &&& 11037532056220336129#64 = v137)
    (v138_def : v137 + (d0 + 7409212017489215487#64) = v138)
    (v139_def : (if v138.ult v137 = true then 1#64 else 0#64) = v139)
    (v140_def : v370 + 18446744073709551615#64 &&& 2469829653914515739#64 = v140)
    (v141_def : v140 + (v116 + 15976914419795035877#64) = v141)
    (v142_def : (if v141.ult v140 = true then 1#64 else 0#64) = v142)
    (v143_def : v141 + v139 = v143)
    (v144_def : (if v143.ult v141 = true then 1#64 else 0#64) = v144)
    (v145_def : v142 + v144 = v145)
    (v146_def : v145 + v124 = v146)
    (v147_def : (if v146.ult v145 = true then 1#64 else 0#64) = v147)
    (v150_def : v370 + 18446744073709551615#64 &&& 4611686018427387904#64 = v150)
    (v151_def : v150 + v368 = v151)
    (v152_def : v151 + v147 = v152)
    (hA : leLimbsToNat [a0, a1, a2, a3] < Fp.p) :
    leLimbsToNat [v138, v143, v146, v152] =
      Fp.add (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [a0, a1, a2, a3]) := by
  have hp : Fp.p < 2 ^ 255 := by decide +kernel
  have hD := fdbl_limbs hd0 hs1 ht0 hd1 hs2 ht1 hd2 hs3 ht2 (by omega)
  have ht2' : t2.toNat ≤ 1 := by
    have := Bn.shr_fact ht2; have := a2.isLt; simp only [Nat.reducePow] at *; omega
  have hs3' : s3.toNat % 2 = 0 := by
    have := Bn.shl_fact (by decide) hs3; simp only [Nat.reducePow, Nat.reduceSub] at this; omega
  have tl := fdbl_sub_tail ht2' hs3' v112_def v116_def v117_def v118_def v120_def v121_def
    v123_def v124_def v125_def v126_def v127_def v364_def v365_def v366_def v367_def v368_def
    v369_def v370_def v137_def v138_def v139_def v140_def v141_def v142_def v143_def v144_def
    v145_def v146_def v147_def v150_def v151_def v152_def
  rw [Fp.add, ← Nat.two_mul, ← hD, leLimbsToNat_four_eq]
  exact reduce_of_tail tl (by omega)

/-- `Fp::double` at a site whose limb 3 is `s3 ||| t2` and whose tail is `mont_sub_tail`'s. -/
theorem fdbl_chain_native {a0 a1 a2 a3 d0 s1 t0 d1 s2 t1 d2 s3 t2 d3 : Word}
    {v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127 v128 v129 v130 v134 v135
      v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v150 v151 v152 : Word}
    (hd0 : a0 <<< 1 = d0) (hs1 : a1 <<< 1 = s1) (ht0 : a0 >>> 63 = t0) (hd1 : s1 ||| t0 = d1)
    (hs2 : a2 <<< 1 = s2) (ht1 : a1 >>> 63 = t1) (hd2 : s2 ||| t1 = d2)
    (hs3 : a3 <<< 1 = s3) (ht2 : a2 >>> 63 = t2) (hd3 : s3 ||| t2 = d3)
    (v112_def : (if (d0 + 7409212017489215487#64).ult d0 = true then 1#64 else 0#64) = v112)
    (v116_def : d1 + (v112 + 18446744073709551615#64) = v116)
    (v117_def : (if v116.ult d1 = true then 1#64 else 0#64) = v117)
    (v118_def : v112 + (18446744073709551615#64 + v117) = v118)
    (v120_def : (if (v116 + 15976914419795035877#64).ult v116 = true then 1#64 else 0#64) = v120)
    (v121_def : v118 + v120 = v121)
    (v123_def : (v121 + 18446744073709551615#64).sshiftRight 63 = v123)
    (v124_def : v123 + d2 = v124)
    (v125_def : (if v124.ult v123 = true then 1#64 else 0#64) = v125)
    (v126_def : v123 + v125 = v126)
    (v127_def : v126.sshiftRight 63 = v127)
    (v128_def : d3 + v127 = v128)
    (v129_def : (if v128.ult d3 = true then 1#64 else 0#64) = v129)
    (v130_def : v127 + v129 = v130)
    (v134_def : (if (v128 + 13835058055282163712#64).ult v128 = true then 1#64 else 0#64) = v134)
    (v135_def : v130 + v134 = v135)
    (v137_def : v135 + 18446744073709551615#64 &&& 11037532056220336129#64 = v137)
    (v138_def : v137 + (d0 + 7409212017489215487#64) = v138)
    (v139_def : (if v138.ult v137 = true then 1#64 else 0#64) = v139)
    (v140_def : v135 + 18446744073709551615#64 &&& 2469829653914515739#64 = v140)
    (v141_def : v140 + (v116 + 15976914419795035877#64) = v141)
    (v142_def : (if v141.ult v140 = true then 1#64 else 0#64) = v142)
    (v143_def : v141 + v139 = v143)
    (v144_def : (if v143.ult v141 = true then 1#64 else 0#64) = v144)
    (v145_def : v142 + v144 = v145)
    (v146_def : v145 + v124 = v146)
    (v147_def : (if v146.ult v145 = true then 1#64 else 0#64) = v147)
    (v150_def : v135 + 18446744073709551615#64 &&& 4611686018427387904#64 = v150)
    (v151_def : v150 + (v128 + 13835058055282163712#64) = v151)
    (v152_def : v151 + v147 = v152)
    (hA : leLimbsToNat [a0, a1, a2, a3] < Fp.p) :
    leLimbsToNat [v138, v143, v146, v152] =
      Fp.add (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [a0, a1, a2, a3]) := by
  have hp : Fp.p < 2 ^ 255 := by decide +kernel
  have hD := fdbl_limbs hd0 hs1 ht0 hd1 hs2 ht1 hd2 hs3 ht2 (by omega)
  have h3 := Bn.shl1_or_shr63 hs3 ht2 hd3
  have tl := mont_sub_tail (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v112_def v116_def v117_def v118_def v120_def v121_def v123_def v124_def v125_def
    v126_def v127_def v128_def v129_def v130_def v134_def v135_def v137_def v138_def v139_def
    v140_def v141_def v142_def v143_def v144_def v145_def v146_def v147_def v150_def v151_def
    v152_def
  rw [Fp.add, ← Nat.two_mul, ← hD, leLimbsToNat_four_eq, ← h3]
  exact reduce_of_tail tl (by omega)

end Cases.Zip2005
