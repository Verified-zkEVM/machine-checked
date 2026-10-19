import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Field.Fq
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Field.MontTail
import Cases.Zip2005.Image.F_7802e9b8
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- `Fq::to_repr`: the canonical little-endian bytes of `x`, i.e. the
    Montgomery representative `x` reduced to `x·R⁻¹ mod q`. Software Montgomery
    reduction (four rounds, then a conditional subtraction), no calls. -/
theorem fq_to_repr_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 : Word) (x0 x1 x2 x3 : Word)
    (hpc : s.pc = 0x7802e9b8#64) (hcode : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd : Disjoint a0 4 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (leLimbsToNat [x0, x1, x2, x3] * Fq.rInv % Fq.q)) t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨O, hO, hOlen⟩ := Region.exists_junk a0 4 s
  have hu := Unchanged.refl [(a0, 4)] s
  sym_exec
  bn_lin
  have z1 := Bn.mont_low (n0 := 10108024940646105087) (p0 := 10108024940646105089) (by decide) v8_def v11_def v14_def
  have z2 := Bn.mont_low (n0 := 10108024940646105087) (p0 := 10108024940646105089) (by decide) v35_def v37_def v38_def
  have z3 := Bn.mont_low (n0 := 10108024940646105087) (p0 := 10108024940646105089) (by decide) v59_def v61_def v62_def
  have z4 := Bn.mont_low (n0 := 10108024940646105087) (p0 := 10108024940646105089) (by decide) v83_def v85_def v86_def
  have r1 : x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat + v8.toNat * (10108024940646105089 + 2^64 * 2469829653919213789 + 2^254)
      = 2^64 * (v22.toNat + 2^64 * v25.toNat + 2^128 * v32.toNat + 2^192 * v34.toNat) := by
    linarith
  have r2 : v22.toNat + 2^64 * v25.toNat + 2^128 * v32.toNat + 2^192 * v34.toNat + v35.toNat * (10108024940646105089 + 2^64 * 2469829653919213789 + 2^254)
      = 2^64 * (v46.toNat + 2^64 * v49.toNat + 2^128 * v56.toNat + 2^192 * v58.toNat) := by
    linarith
  have r3 : v46.toNat + 2^64 * v49.toNat + 2^128 * v56.toNat + 2^192 * v58.toNat + v59.toNat * (10108024940646105089 + 2^64 * 2469829653919213789 + 2^254)
      = 2^64 * (v70.toNat + 2^64 * v73.toNat + 2^128 * v80.toNat + 2^192 * v82.toNat) := by
    linarith
  have r4 : v70.toNat + 2^64 * v73.toNat + 2^128 * v80.toNat + 2^192 * v82.toNat + v83.toNat * (10108024940646105089 + 2^64 * 2469829653919213789 + 2^254)
      = 2^64 * (v94.toNat + 2^64 * v97.toNat + 2^128 * v104.toNat + 2^192 * v106.toNat) := by
    linarith
  have hT : 2 ^ 256 * (v94.toNat + 2^64 * v97.toNat + 2^128 * v104.toNat + 2^192 * v106.toNat)
      = (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat)
        + (v8.toNat + 2^64 * v35.toNat + 2^128 * v59.toNat + 2^192 * v83.toNat) * Fq.q := by
    rw [show Fq.q = 10108024940646105089 + 2^64 * 2469829653919213789 + 2^192 * 2^62 by decide]
    symm; linear_combination r1 + 2^64 * r2 + 2^128 * r3 + 2^192 * r4
  have tl := mont_sub_tail (P0 := 10108024940646105089) (N0 := 8338719133063446527)
    (P1 := 2469829653919213789) (N1 := 15976914419790337827) (by decide) (by decide) (by decide)
    (by decide) v112_def v116_def v117_def v118_def v120_def v121_def v123_def v124_def
    v125_def v126_def v127_def v128_def v129_def v130_def v134_def v135_def v137_def v138_def
    v139_def v140_def v141_def v142_def v143_def v144_def v145_def v146_def v147_def v150_def
    v151_def v152_def
  dsimp only at tl
  rw [show 10108024940646105089 + 2 ^ 64 * 2469829653919213789 + 2 ^ 192 * 2 ^ 62 = Fq.q by decide]
    at tl
  have hXe : leLimbsToNat [x0, x1, x2, x3] =
      x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hMe : leLimbsToNat [v8, v35, v59, v83] =
      v8.toNat + 2^64 * v35.toNat + 2^128 * v59.toNat + 2^192 * v83.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hRe : leLimbsToNat [v138, v143, v146, v152] =
      v138.toNat + 2^64 * v143.toNat + 2^128 * v146.toNat + 2^192 * v152.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hX := leLimbsToNat_lt [x0, x1, x2, x3]
  have hM := leLimbsToNat_lt [v8, v35, v59, v83]
  rw [hXe] at hX
  rw [hMe] at hM
  have hR := Fq.redc_eq hT hX hM tl.1 tl.2
  have hout : [v167, v182, v197, v212] =
      natToLeLimbs 4 (leLimbsToNat [x0, x1, x2, x3] * Fq.rInv % Fq.q) := by
    subst v153_def v154_def v155_def v156_def v157_def v158_def v159_def v160_def v161_def v162_def
      v163_def v164_def v165_def v166_def v167_def v168_def v169_def v170_def v171_def v172_def
      v173_def v174_def v175_def v176_def v177_def v178_def v179_def v180_def v181_def v182_def
      v183_def v184_def v185_def v186_def v187_def v188_def v189_def v190_def v191_def v192_def
      v193_def v194_def v195_def v196_def v197_def v198_def v199_def v200_def v201_def v202_def
      v203_def v204_def v205_def v206_def v207_def v208_def v209_def v210_def v211_def v212_def
    rw [replaceBytes_word, replaceBytes_word, replaceBytes_word, replaceBytes_word, hXe, ← hR, ← hRe]
    exact (natToLeLimbs_leLimbsToNat _).symm
  rw [hout] at hR1
  sym_close hk

end Cases.Zip2005
