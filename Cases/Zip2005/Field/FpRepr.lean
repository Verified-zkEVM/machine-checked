import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Field.MontTail
import Cases.Zip2005.Image.F_78029468
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- `Fp::to_repr`: the canonical little-endian bytes of `x`, i.e. the
    Montgomery representative `x` reduced to `x·R⁻¹ mod p`. Software Montgomery
    reduction (four rounds, then a conditional subtraction), no calls. -/
theorem fp_to_repr_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 : Word) (x0 x1 x2 x3 : Word)
    (hpc : s.pc = 0x78029468#64) (hcode : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd : Disjoint a0 4 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (leLimbsToNat [x0, x1, x2, x3] * Fp.rInv % Fp.p)) t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨O, hO, hOlen⟩ := Region.exists_junk a0 4 s
  have hu := Unchanged.refl [(a0, 4)] s
  sym_exec
  bn_lin
  have z1 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v8_def v11_def v14_def
  have z2 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v35_def v37_def v38_def
  have z3 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v59_def v61_def v62_def
  have z4 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v83_def v85_def v86_def
  have r1 : x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat + v8.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v22.toNat + 2^64 * v25.toNat + 2^128 * v32.toNat + 2^192 * v34.toNat) := by
    linarith
  have r2 : v22.toNat + 2^64 * v25.toNat + 2^128 * v32.toNat + 2^192 * v34.toNat + v35.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v46.toNat + 2^64 * v49.toNat + 2^128 * v56.toNat + 2^192 * v58.toNat) := by
    linarith
  have r3 : v46.toNat + 2^64 * v49.toNat + 2^128 * v56.toNat + 2^192 * v58.toNat + v59.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v70.toNat + 2^64 * v73.toNat + 2^128 * v80.toNat + 2^192 * v82.toNat) := by
    linarith
  have r4 : v70.toNat + 2^64 * v73.toNat + 2^128 * v80.toNat + 2^192 * v82.toNat + v83.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v94.toNat + 2^64 * v97.toNat + 2^128 * v104.toNat + 2^192 * v106.toNat) := by
    linarith
  have hT : 2 ^ 256 * (v94.toNat + 2^64 * v97.toNat + 2^128 * v104.toNat + 2^192 * v106.toNat)
      = (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat)
        + (v8.toNat + 2^64 * v35.toNat + 2^128 * v59.toNat + 2^192 * v83.toNat) * Fp.p := by
    rw [show Fp.p = 11037532056220336129 + 2^64 * 2469829653914515739 + 2^192 * 2^62 by decide]
    symm; linear_combination r1 + 2^64 * r2 + 2^128 * r3 + 2^192 * r4
  have tl := mont_sub_tail (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v112_def v116_def v117_def v118_def v120_def v121_def v123_def v124_def
    v125_def v126_def v127_def v128_def v129_def v130_def v134_def v135_def v137_def v138_def
    v139_def v140_def v141_def v142_def v143_def v144_def v145_def v146_def v147_def v150_def
    v151_def v152_def
  dsimp only at tl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide]
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
  have hR := Fp.redc_eq hT hX hM tl.1 tl.2
  have hout : [v167, v182, v197, v212] =
      natToLeLimbs 4 (leLimbsToNat [x0, x1, x2, x3] * Fp.rInv % Fp.p) := by
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
