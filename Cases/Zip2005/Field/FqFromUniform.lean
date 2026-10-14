/-
  Cases.Zip2005.FqFromUniform

  `Fq::from_uniform_bytes` (`[u8; 64]`): the bytes re-read as eight
  little-endian doublewords on the stack, then `Fq::from_u512`.
-/

import Cases.Zip2005.Field.FqFromU512
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Image.F_7802f038
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
theorem fq_from_uniform_bytes_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word) (x : List Word)
    (hxl : x.length = 8)
    (hpc : s.pc = 0x7802f038#64) (hcode : CodeAt F_7802f038.base F_7802f038.prog s)
    (hcodeU : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x140 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 x s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 8)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd : Disjoint a0 4 a1 8)
    (hd0 : Disjoint (sp - 0x140#64) 40 a0 4) (hd1 : Disjoint (sp - 0x140#64) 40 a1 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x140#64, 40), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (Fq.add
        (Fq.mul (leLimbsToNat [x[0]!, x[1]!, x[2]!, x[3]!]) Fq.R2)
        (Fq.mul (leLimbsToNat [x[4]!, x[5]!, x[6]!, x[7]!]) Fq.R3))) t → SafeN Gd n P t) :
    SafeN Gd n P s := by
  obtain ⟨O, hO, hOl⟩ := Region.exists_junk a0 4 s
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x50#64) 10 s
  obtain ⟨G, hG, hGl⟩ := Region.exists_junk (sp - 0x140#64) 30 s
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64) 40 := hstk.frame 40 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hokA.sub' 30 10 (by decide) (by bv_omega)
  have hokG : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64) 30 := hokA.sub' 0 30 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x140#64, 40), (a0, 4)] s
  have hstkB : StackOk Ro.layout 0xf0 (sp - 0x50#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0x50#64).toNat = sp.toNat - 0x50 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  sym_exec [fq_from_u512_spec]
  sym_close hk
  have h0 : v177 = x[0]! := by
    rw [← v177_def, ← v176_def, ← v175_def, ← v174_def, ← v173_def, ← v172_def, ← v171_def, ← v170_def, ← v169_def, ← v168_def, ← v167_def, ← v166_def, ← v165_def, ← v164_def, ← v163_def, ← v162_def, ← v161_def, ← v160_def, ← v159_def, ← v158_def, ← v157_def, ← v156_def]
    exact bytes_word _
  have h1 : v155 = x[1]! := by
    rw [← v155_def, ← v154_def, ← v153_def, ← v152_def, ← v151_def, ← v150_def, ← v149_def, ← v148_def, ← v147_def, ← v146_def, ← v145_def, ← v144_def, ← v143_def, ← v142_def, ← v141_def, ← v140_def, ← v139_def, ← v138_def, ← v137_def, ← v136_def, ← v135_def, ← v134_def]
    exact bytes_word _
  have h2 : v133 = x[2]! := by
    rw [← v133_def, ← v132_def, ← v131_def, ← v130_def, ← v129_def, ← v128_def, ← v127_def, ← v126_def, ← v125_def, ← v124_def, ← v123_def, ← v122_def, ← v121_def, ← v120_def, ← v119_def, ← v118_def, ← v117_def, ← v116_def, ← v115_def, ← v114_def, ← v113_def, ← v112_def]
    exact bytes_word _
  have h3 : v111 = x[3]! := by
    rw [← v111_def, ← v110_def, ← v109_def, ← v108_def, ← v107_def, ← v106_def, ← v105_def, ← v104_def, ← v103_def, ← v102_def, ← v101_def, ← v100_def, ← v99_def, ← v98_def, ← v97_def, ← v96_def, ← v95_def, ← v94_def, ← v93_def, ← v92_def, ← v91_def, ← v90_def]
    exact bytes_word _
  have h4 : v89 = x[4]! := by
    rw [← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def, ← v76_def, ← v75_def, ← v74_def, ← v73_def, ← v72_def, ← v71_def, ← v70_def, ← v69_def, ← v68_def]
    exact bytes_word _
  have h5 : v67 = x[5]! := by
    rw [← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def, ← v56_def, ← v55_def, ← v54_def, ← v53_def, ← v52_def, ← v51_def, ← v50_def, ← v49_def, ← v48_def, ← v47_def, ← v46_def]
    exact bytes_word _
  have h6 : v45 = x[6]! := by
    rw [← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v34_def, ← v33_def, ← v32_def, ← v31_def, ← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def]
    exact bytes_word _
  have h7 : v23 = x[7]! := by
    rw [← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def, ← v14_def, ← v13_def, ← v12_def, ← v11_def, ← v10_def, ← v9_def, ← v8_def, ← v7_def, ← v6_def, ← v5_def, ← v4_def, ← v3_def, ← v2_def]
    exact bytes_word _
  rw [cells4', ← acc189_0_def]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

end Cases.Zip2005
