/-
  Cases.Zip2005.FpAddCf

  `Fp::add` with the compiler's carry-first schedule for limb 1 (`Ep::add`'s `z1 + z2`):
  `t1 = a1 + c0`, then `d1 = t1 + b1`, carries taken against `a1` and `t1`. The conditional
  subtraction is `fadd_reduce`'s.
-/

import Cases.Zip2005.Field.FpAdd

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

/-- The `adc` chain, carry-first at limb 1. -/
theorem fadd_limbs_cf {a0 a1 a2 a3 b0 b1 b2 b3 d0 c0 t1 c1 d1 c1' k1 s2 c2 d2 c2' k2 s3 d3 : Word}
    (hd0 : a0 + b0 = d0) (hc0 : (if d0.ult a0 = true then 1#64 else 0#64) = c0)
    (ht1 : a1 + c0 = t1) (hc1 : (if t1.ult a1 = true then 1#64 else 0#64) = c1)
    (hd1 : t1 + b1 = d1) (hc1' : (if d1.ult t1 = true then 1#64 else 0#64) = c1')
    (hk1 : c1 + c1' = k1)
    (hs2 : a2 + b2 = s2) (hc2 : (if s2.ult a2 = true then 1#64 else 0#64) = c2)
    (hd2 : s2 + k1 = d2) (hc2' : (if d2.ult s2 = true then 1#64 else 0#64) = c2')
    (hk2 : c2 + c2' = k2)
    (hs3 : a3 + b3 = s3) (hd3 : s3 + k2 = d3)
    (hlt : leLimbsToNat [a0, a1, a2, a3] + leLimbsToNat [b0, b1, b2, b3] < 2 ^ 256) :
    leLimbsToNat [d0, d1, d2, d3] = leLimbsToNat [a0, a1, a2, a3] + leLimbsToNat [b0, b1, b2, b3] := by
  have e0 := Bn.add_fact' hd0
  have e1 := Bn.add_fact' ht1
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
  have := t1.isLt; have := s2.isLt; have := s3.isLt; have := k1.isLt; have := k2.isLt
  rcases f0 with ⟨f0, _⟩ | ⟨f0, _⟩ <;> rcases f1 with ⟨f1, _⟩ | ⟨f1, _⟩ <;>
    rcases f2 with ⟨f2, _⟩ | ⟨f2, _⟩ <;> rcases f3 with ⟨f3, _⟩ | ⟨f3, _⟩ <;>
    rcases f4 with ⟨f4, _⟩ | ⟨f4, _⟩ <;> omega

/-- `Fp::add`, carry-first schedule. The operands need only sum below `2p`: `Ep::add`'s
`z1 + z2` takes its carries against limbs of either operand, so the lemma is applied to
pairwise-swapped limb lists (`limbs_add_swap`). -/
theorem fadd_chain_cf {a0 a1 a2 a3 b0 b1 b2 b3 d0 c0 t1 c1 d1 c1' k1 s2 c2 d2 c2' k2 s3 d3 : Word}
    {v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127 v128 v129 v130 v134 v135 v137 v138
      v139 v140 v141 v142 v143 v144 v145 v146 v147 v150 v151 v152 : Word}
    (hd0 : a0 + b0 = d0) (hc0 : (if d0.ult a0 = true then 1#64 else 0#64) = c0)
    (ht1 : a1 + c0 = t1) (hc1 : (if t1.ult a1 = true then 1#64 else 0#64) = c1)
    (hd1 : t1 + b1 = d1) (hc1' : (if d1.ult t1 = true then 1#64 else 0#64) = c1')
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
    (hAB : leLimbsToNat [a0, a1, a2, a3] + leLimbsToNat [b0, b1, b2, b3] < 2 * Fp.p) :
    leLimbsToNat [v138, v143, v146, v152] =
      Fp.add (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3]) := by
  have hp : Fp.p < 2 ^ 255 := by decide +kernel
  have hD := fadd_limbs_cf hd0 hc0 ht1 hc1 hd1 hc1' hk1 hs2 hc2 hd2 hc2' hk2 hs3 hd3 (by omega)
  rw [Fp.add, ← hD]
  exact fadd_reduce v112_def v116_def v117_def v118_def v120_def v121_def v123_def v124_def
    v125_def v126_def v127_def v128_def v129_def v130_def v134_def v135_def v137_def v138_def
    v139_def v140_def v141_def v142_def v143_def v144_def v145_def v146_def v147_def v150_def
    v151_def v152_def (by omega)

/-- Two four-limb sums agree when the limbs are swapped pairwise between the operands. -/
theorem limbs_add_swap (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    leLimbsToNat [a0, b1, a2, a3] + leLimbsToNat [b0, a1, b2, b3] =
      leLimbsToNat [a0, a1, a2, a3] + leLimbsToNat [b0, b1, b2, b3] := by
  simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring

end Cases.Zip2005
