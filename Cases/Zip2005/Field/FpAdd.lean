/-
  Cases.Zip2005.FpAdd

  Field addition as the guest compiles `Fp::add`: `adc` on four limbs (the carry out of the
  top limb dropped -- the operands are below `p < 2^255`), then the conditional subtraction
  of `p` that `to_repr` also ends with (`Cases.Zip2005.mont_sub_tail`), two of whose hypotheses the
  compiler here schedules with the operands commuted.
-/

import Cases.Zip2005.Field.MontTail
import Cases.Zip2005.Field.FpSub

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

/-- The `adc` chain: limbs `d0 d1 d2 d3` of `A + B` (no overflow when `A + B < 2^256`). -/
theorem fadd_limbs {a0 a1 a2 a3 b0 b1 b2 b3 d0 c0 s1 c1 d1 c1' k1 s2 c2 d2 c2' k2 s3 d3 : Word}
    (hd0 : a0 + b0 = d0) (hc0 : (if d0.ult a0 = true then 1#64 else 0#64) = c0)
    (hs1 : a1 + b1 = s1) (hc1 : (if s1.ult a1 = true then 1#64 else 0#64) = c1)
    (hd1 : s1 + c0 = d1) (hc1' : (if d1.ult s1 = true then 1#64 else 0#64) = c1')
    (hk1 : c1 + c1' = k1)
    (hs2 : a2 + b2 = s2) (hc2 : (if s2.ult a2 = true then 1#64 else 0#64) = c2)
    (hd2 : s2 + k1 = d2) (hc2' : (if d2.ult s2 = true then 1#64 else 0#64) = c2')
    (hk2 : c2 + c2' = k2)
    (hs3 : a3 + b3 = s3) (hd3 : s3 + k2 = d3)
    (hlt : leLimbsToNat [a0, a1, a2, a3] + leLimbsToNat [b0, b1, b2, b3] < 2 ^ 256) :
    leLimbsToNat [d0, d1, d2, d3] = leLimbsToNat [a0, a1, a2, a3] + leLimbsToNat [b0, b1, b2, b3] := by
  have e0 := Bn.add_fact' hd0
  have e1 := Bn.add_fact' hs1
  have e2 := Bn.add_fact' hd1
  have e3 := Bn.add_fact' hk1
  have e4 := Bn.add_fact' hs2
  have e5 := Bn.add_fact' hd2
  have e6 := Bn.add_fact' hk2
  have e7 := Bn.add_fact' hs3
  have e8 := Bn.add_fact' hd3
  have f0 := Bn.ult_fact hc0
  have f1 := Bn.ult_fact hc1
  have f2 := Bn.ult_fact hc1'
  have f3 := Bn.ult_fact hc2
  have f4 := Bn.ult_fact hc2'
  simp only [leLimbsToNat_cons, leLimbsToNat_nil] at hlt ⊢
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  have := d0.isLt; have := d1.isLt; have := d2.isLt; have := d3.isLt
  have := s1.isLt; have := s2.isLt; have := s3.isLt; have := k1.isLt; have := k2.isLt
  rcases f0 with ⟨f0, _⟩ | ⟨f0, _⟩ <;> rcases f1 with ⟨f1, _⟩ | ⟨f1, _⟩ <;>
    rcases f2 with ⟨f2, _⟩ | ⟨f2, _⟩ <;> rcases f3 with ⟨f3, _⟩ | ⟨f3, _⟩ <;>
    rcases f4 with ⟨f4, _⟩ | ⟨f4, _⟩ <;> omega

namespace Bn

/-- `x + (c + y)` is `y + (x + c)`. -/
theorem add_rot {x y c v : Word} (h : x + (c + y) = v) : y + (x + c) = v := by
  rw [← h]; ac_rfl

/-- A carry flag compares the sum with either addend. -/
theorem carry_swap {x y c v w : Word} (hv : x + (c + y) = v)
    (h : (if v.ult (x + c) = true then 1#64 else 0#64) = w) :
    (if v.ult y = true then 1#64 else 0#64) = w := by
  subst h
  have e : v = (x + c) + y := by rw [← hv]; ac_rfl
  generalize x + c = z at e ⊢
  subst e
  have hz := z.isLt; have hy := y.isLt
  simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq]
  by_cases hc : z.toNat + y.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc, if_neg (by omega), if_neg (by omega)]
  · rw [show (z.toNat + y.toNat) % 2 ^ 64 = z.toNat + y.toNat - 2 ^ 64 by omega,
      if_pos (by omega), if_pos (by omega)]

end Bn

/-- The conditional subtraction of `p` after an `adc` sum `T < 2p`: the result is `T mod p`.
    `mont_sub_tail`'s hypotheses, with `to_repr`'s limb-1 schedule (`v116`, `v117`) replaced
    by `from_bytes`' (`v116'`, `v117'`). -/
theorem fadd_reduce {v94 v97 v104 v106 v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127
      v128 v129 v130 v134 v135 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v150 v151
      v152 : Word}
    (v112_def : (if (v94 + 7409212017489215487#64).ult v94 = true then 1#64 else 0#64) = v112)
    (v116_def : v112 + (18446744073709551615#64 + v97) = v116)
    (v117_def : (if v116.ult (v112 + 18446744073709551615#64) = true then 1#64 else 0#64) = v117)
    (v118_def : v112 + (18446744073709551615#64 + v117) = v118)
    (v120_def : (if (v116 + 15976914419795035877#64).ult v116 = true then 1#64 else 0#64) = v120)
    (v121_def : v118 + v120 = v121)
    (v123_def : (v121 + 18446744073709551615#64).sshiftRight 63 = v123)
    (v124_def : v123 + v104 = v124)
    (v125_def : (if v124.ult v123 = true then 1#64 else 0#64) = v125)
    (v126_def : v123 + v125 = v126)
    (v127_def : v126.sshiftRight 63 = v127)
    (v128_def : v106 + v127 = v128)
    (v129_def : (if v128.ult v106 = true then 1#64 else 0#64) = v129)
    (v130_def : v127 + v129 = v130)
    (v134_def : (if (v128 + 13835058055282163712#64).ult v128 = true then 1#64 else 0#64) = v134)
    (v135_def : v130 + v134 = v135)
    (v137_def : v135 + 18446744073709551615#64 &&& 11037532056220336129#64 = v137)
    (v138_def : v137 + (v94 + 7409212017489215487#64) = v138)
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
    (hT : leLimbsToNat [v94, v97, v104, v106] < 2 * Fp.p) :
    leLimbsToNat [v138, v143, v146, v152] = leLimbsToNat [v94, v97, v104, v106] % Fp.p := by
  have v116' := Bn.add_rot v116_def
  have v117' := Bn.carry_swap v116_def v117_def
  have tl := mont_sub_tail (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v112_def v116' v117' v118_def v120_def v121_def v123_def v124_def v125_def
    v126_def v127_def v128_def v129_def v130_def v134_def v135_def v137_def v138_def v139_def
    v140_def v141_def v142_def v143_def v144_def v145_def v146_def v147_def v150_def v151_def
    v152_def
  dsimp only at tl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by
    decide +kernel] at tl
  have eT : leLimbsToNat [v94, v97, v104, v106] =
      v94.toNat + 2 ^ 64 * v97.toNat + 2 ^ 128 * v104.toNat + 2 ^ 192 * v106.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have eR : leLimbsToNat [v138, v143, v146, v152] =
      v138.toNat + 2 ^ 64 * v143.toNat + 2 ^ 128 * v146.toNat + 2 ^ 192 * v152.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  rw [eT] at hT ⊢; rw [eR]
  generalize v94.toNat + 2 ^ 64 * v97.toNat + 2 ^ 128 * v104.toNat + 2 ^ 192 * v106.toNat = T at *
  generalize v138.toNat + 2 ^ 64 * v143.toNat + 2 ^ 128 * v146.toNat + 2 ^ 192 * v152.toNat = R at *
  obtain ⟨h1, h2⟩ := tl
  rcases Nat.lt_or_ge T Fp.p with h | h
  · rw [Nat.mod_eq_of_lt h]; exact h1 h
  · have := h2 h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

/-- `Fp::add` on canonical operands: the `adc` chain and the conditional subtraction. -/
theorem fadd_chain {a0 a1 a2 a3 b0 b1 b2 b3 d0 c0 s1 c1 d1 c1' k1 s2 c2 d2 c2' k2 s3 d3 : Word}
    {v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127 v128 v129 v130 v134 v135 v137 v138
      v139 v140 v141 v142 v143 v144 v145 v146 v147 v150 v151 v152 : Word}
    (hd0 : a0 + b0 = d0) (hc0 : (if d0.ult a0 = true then 1#64 else 0#64) = c0)
    (hs1 : a1 + b1 = s1) (hc1 : (if s1.ult a1 = true then 1#64 else 0#64) = c1)
    (hd1 : s1 + c0 = d1) (hc1' : (if d1.ult s1 = true then 1#64 else 0#64) = c1')
    (hk1 : c1 + c1' = k1)
    (hs2 : a2 + b2 = s2) (hc2 : (if s2.ult a2 = true then 1#64 else 0#64) = c2)
    (hd2 : s2 + k1 = d2) (hc2' : (if d2.ult s2 = true then 1#64 else 0#64) = c2')
    (hk2 : c2 + c2' = k2)
    (hs3 : a3 + b3 = s3) (hd3 : s3 + k2 = d3)
    (v112_def : (if (d0 + 7409212017489215487#64).ult d0 = true then 1#64 else 0#64) = v112)
    (v116_def : v112 + (18446744073709551615#64 + d1) = v116)
    (v117_def : (if v116.ult (v112 + 18446744073709551615#64) = true then 1#64 else 0#64) = v117)
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
    (hA : leLimbsToNat [a0, a1, a2, a3] < Fp.p) (hB : leLimbsToNat [b0, b1, b2, b3] < Fp.p) :
    leLimbsToNat [v138, v143, v146, v152] =
      Fp.add (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3]) := by
  have hp : Fp.p < 2 ^ 255 := by decide +kernel
  have hD := fadd_limbs hd0 hc0 hs1 hc1 hd1 hc1' hk1 hs2 hc2 hd2 hc2' hk2 hs3 hd3 (by omega)
  rw [Fp.add, ← hD]
  exact fadd_reduce v112_def v116_def v117_def v118_def v120_def v121_def v123_def v124_def
    v125_def v126_def v127_def v128_def v129_def v130_def v134_def v135_def v137_def v138_def
    v139_def v140_def v141_def v142_def v143_def v144_def v145_def v146_def v147_def v150_def
    v151_def v152_def (by omega)

end Cases.Zip2005
