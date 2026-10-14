import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Field.Fq
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Runtime.BlackBox
import Cases.Zip2005.Field.MontTailR
import Cases.Zip2005.Image.F_7802ed10
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
theorem fq_from_repr_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word) (x0 x1 x2 x3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7802ed10#64) (hcode : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xb0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5) (hd : Disjoint a0 5 a1 4)
    (hd0 : Disjoint (sp - 0xb0#64) 22 a0 5) (hd1 : Disjoint (sp - 0xb0#64) 22 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xb0#64, 22), (a0, 5)] s t →
      Region a0 (natToLeLimbs 4 (Fq.mul (leLimbsToNat [x0, x1, x2, x3]) Fq.R2) ++
        [replaceByte O[4]! 0 (if leLimbsToNat [x0, x1, x2, x3] < Fq.q then 1#8 else 0#8)]) t →
      SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0xa0#64) 20 s
  obtain ⟨FB, hFB, hFBl⟩ := Region.exists_junk (sp - 0xb0#64) 2 s
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 22 := hstk.frame 22 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa0#64) 20 := hokA.sub' 2 20 (by decide) (by bv_omega)
  have hokFB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 2 := hokA.sub' 0 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0xb0#64, 22), (a0, 5)] s
  have hstkB : StackOk Ro.layout 0x10 (sp - 0xa0#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0xa0#64).toNat = sp.toNat - 0xa0 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  sym_exec [uint256_mulmod_spec, black_box_spec]
  sym_close hk
  have hx0 : v30 = x0 := by
    rw [← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def, ← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def, ← v14_def, ← v13_def, ← v12_def, ← v11_def, ← v10_def, ← v9_def]
    exact bytes_word x0
  have hx1 : v52 = x1 := by
    rw [← v52_def, ← v51_def, ← v50_def, ← v49_def, ← v48_def, ← v47_def, ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v34_def, ← v33_def, ← v32_def, ← v31_def]
    exact bytes_word x1
  have hx2 : v74 = x2 := by
    rw [← v74_def, ← v73_def, ← v72_def, ← v71_def, ← v70_def, ← v69_def, ← v68_def, ← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def, ← v56_def, ← v55_def, ← v54_def, ← v53_def]
    exact bytes_word x2
  have hx3 : v96 = x3 := by
    rw [← v96_def, ← v95_def, ← v94_def, ← v93_def, ← v92_def, ← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def, ← v76_def, ← v75_def]
    exact bytes_word x3
  have fl := lt_flag (P0 := 10108024940646105089) (N0 := 8338719133063446527)
    (P1 := 2469829653919213789) (N1 := 15976914419790337827) (by decide) (by decide) (by decide)
    (by decide) v102_def v106_def v107_def v108_def v110_def v111_def v113_def v114_def v115_def
    v116_def v117_def v118_def v119_def v120_def v124_def v125_def
  dsimp only at fl
  rw [show 10108024940646105089 + 2 ^ 64 * 2469829653919213789 + 2 ^ 192 * 2 ^ 62 = Fq.q by decide,
    hx0, hx1, hx2, hx3] at fl
  have hXe : leLimbsToNat [x0, x1, x2, x3] =
      x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hAm : acc182_0 = Fq.mul (leLimbsToNat [x0, x1, x2, x3]) Fq.R2 := by
    rw [← acc182_0_def, ← acc161_0_def, hx0, hx1, hx2, hx3]
    simp only [cells4', Fq.limbs_q, Fq.limbs_rInv, Fq.limbs_R2, Fq.limbs_mod]
    rw [Fq.mul]
  have hcells : [v183, v184, v185, v186] = natToLeLimbs 4 acc182_0 := by
    rw [← v183_def, ← v184_def, ← v185_def, ← v186_def]; rfl
  have hflag : v195 =
      replaceByte O[4]! 0 (if leLimbsToNat [x0, x1, x2, x3] < Fq.q then 1#8 else 0#8) := by
    rw [← v195_def, ← v187_def, hXe]
    by_cases h : x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat < Fq.q
    · rw [show v125 = 0#64 from BitVec.eq_of_toNat_eq (fl.1 h), if_pos h]; rfl
    · rw [show v125 = 1#64 from BitVec.eq_of_toNat_eq (fl.2 (by omega)), if_neg h]; rfl
  rw [show [v183, v184, v185, v186, v195] = [v183, v184, v185, v186] ++ [v195] from rfl,
    hcells, hAm, hflag]

end Cases.Zip2005
