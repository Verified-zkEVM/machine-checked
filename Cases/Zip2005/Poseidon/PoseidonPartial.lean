import Cases.Zip2005.Poseidon.PoseidonFull
import Cases.Zip2005.Poseidon.Sbox
import Cases.Zip2005.Image.F_7801ed68
import Cases.Zip2005.Field.FpAdd
import Cases.Zip2005.Image.Ro

/-!
# Poseidon's partial round (`halo2_poseidon::permute`, the partial-round closure)

`state ← mds · (state + rc)` with the S-box on the first element only: the round constants added
in place (the inline `Fp` addition), `sbox` on element 0, then the MDS closure.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem partial_round_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp env e1 mp st rc : Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 : Word)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Word)
    (hpc : s.pc = 0x7801ed68#64) (hcode : CodeAt F_7801ed68.base F_7801ed68.prog s)
    (hcodeX : CodeAt F_7801e704.base F_7801e704.prog s) (hcodeB : CodeAt F_78023a18.base F_78023a18.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1d0 sp)
    (ha0 : s.getReg .x10 = env) (ha1 : s.getReg .x11 = st) (ha2 : s.getReg .x12 = rc)
    (hE : Region env [e1] s) (hokE : RegionOk Ro.layout.roBase Ro.layout.textHi env 1)
    (hE1 : Region e1 [mp] s) (hokE1 : RegionOk Ro.layout.roBase Ro.layout.textHi e1 1)
    (hM : Region mp [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35] s) (hokM : RegionOk Ro.layout.roBase Ro.layout.textHi mp 36)
    (hX : Region st [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] s) (hokX : RegionOk Ro.layout.roBase Ro.layout.textHi st 12)
    (hC : Region rc [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] s) (hokC : RegionOk Ro.layout.roBase Ro.layout.textHi rc 12)
    (hxl0 : leLimbsToNat [x0, x1, x2, x3] < Fp.p) (hcl0 : leLimbsToNat [c0, c1, c2, c3] < Fp.p)
    (hxl1 : leLimbsToNat [x4, x5, x6, x7] < Fp.p) (hcl1 : leLimbsToNat [c4, c5, c6, c7] < Fp.p)
    (hxl2 : leLimbsToNat [x8, x9, x10, x11] < Fp.p) (hcl2 : leLimbsToNat [c8, c9, c10, c11] < Fp.p)
    (hd0 : Disjoint (sp - 0x1d0#64) 58 mp 36) (hd1 : Disjoint (sp - 0x1d0#64) 58 st 12)
    (hd2 : Disjoint (sp - 0x1d0#64) 58 rc 12) (hd3 : Disjoint (sp - 0x1d0#64) 58 env 1)
    (hd4 : Disjoint (sp - 0x1d0#64) 58 e1 1)
    (hd : Disjoint st 12 mp 36) (hd5 : Disjoint st 12 rc 12) (hd6 : Disjoint st 12 env 1)
    (hd7 : Disjoint st 12 e1 1)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1d0#64, 58), (st, 12)] s t → ∀ o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : Word,
      Region st [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11] t →
      leLimbsToNat [o0, o1, o2, o3] = Fp.add (Fp.add (Fp.add 0 (Fp.mul (leLimbsToNat [m0, m1, m2, m3]) (Fp.pow5 (Fp.add (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [c0, c1, c2, c3]))))) (Fp.mul (leLimbsToNat [m4, m5, m6, m7]) (Fp.add (leLimbsToNat [x4, x5, x6, x7]) (leLimbsToNat [c4, c5, c6, c7])))) (Fp.mul (leLimbsToNat [m8, m9, m10, m11]) (Fp.add (leLimbsToNat [x8, x9, x10, x11]) (leLimbsToNat [c8, c9, c10, c11]))) →
      leLimbsToNat [o4, o5, o6, o7] = Fp.add (Fp.add (Fp.add 0 (Fp.mul (leLimbsToNat [m12, m13, m14, m15]) (Fp.pow5 (Fp.add (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [c0, c1, c2, c3]))))) (Fp.mul (leLimbsToNat [m16, m17, m18, m19]) (Fp.add (leLimbsToNat [x4, x5, x6, x7]) (leLimbsToNat [c4, c5, c6, c7])))) (Fp.mul (leLimbsToNat [m20, m21, m22, m23]) (Fp.add (leLimbsToNat [x8, x9, x10, x11]) (leLimbsToNat [c8, c9, c10, c11]))) →
      leLimbsToNat [o8, o9, o10, o11] = Fp.add (Fp.add (Fp.add 0 (Fp.mul (leLimbsToNat [m24, m25, m26, m27]) (Fp.pow5 (Fp.add (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [c0, c1, c2, c3]))))) (Fp.mul (leLimbsToNat [m28, m29, m30, m31]) (Fp.add (leLimbsToNat [x4, x5, x6, x7]) (leLimbsToNat [c4, c5, c6, c7])))) (Fp.mul (leLimbsToNat [m32, m33, m34, m35]) (Fp.add (leLimbsToNat [x8, x9, x10, x11]) (leLimbsToNat [c8, c9, c10, c11]))) →
      leLimbsToNat [o0, o1, o2, o3] < Fp.p →
      leLimbsToNat [o4, o5, o6, o7] < Fp.p →
      leLimbsToNat [o8, o9, o10, o11] < Fp.p →
      SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x60#64) 12 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hstk.frame 12 (by decide)
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1d0#64) 58 := hstk.frame 58 (by decide)
  have hu := Unchanged.refl [(sp - 0x1d0#64, 58), (st, 12)] s
  have hlo := hstk.lo
  sym_exec [sbox_spec, mds_spec]
  sym_close hk
  all_goals
    have ch0 := fadd_chain v14_def v15_def v16_def v17_def v18_def v19_def v20_def v21_def v22_def v23_def v24_def v25_def v26_def v27_def v33_def v37_def v38_def v39_def v41_def v42_def v44_def v45_def v46_def v47_def v48_def v49_def v50_def v51_def v55_def v56_def v64_def v65_def v66_def v67_def v68_def v69_def v70_def v71_def v72_def v73_def v74_def v77_def v78_def v79_def hcl0 hxl0
    have ch1 := fadd_chain v92_def v93_def v94_def v95_def v96_def v97_def v98_def v99_def v100_def v101_def v102_def v103_def v104_def v105_def v107_def v109_def v110_def v111_def v113_def v114_def v116_def v117_def v118_def v119_def v120_def v121_def v122_def v123_def v125_def v126_def v128_def v129_def v130_def v131_def v132_def v133_def v134_def v135_def v136_def v137_def v138_def v139_def v140_def v141_def hcl1 hxl1
    have ch2 := fadd_chain v154_def v155_def v156_def v157_def v158_def v159_def v160_def v161_def v162_def v163_def v164_def v165_def v166_def v167_def v169_def v171_def v172_def v173_def v175_def v176_def v178_def v179_def v180_def v181_def v182_def v183_def v184_def v185_def v187_def v188_def v190_def v191_def v192_def v193_def v194_def v195_def v196_def v197_def v198_def v199_def v200_def v201_def v202_def v203_def hcl2 hxl2
    have e0 : leLimbsToNat [v222, v223, v224, v225] = Fp.pow5 (Fp.add (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [c0, c1, c2, c3])) := by
      rw [← v222_def, ← v223_def, ← v224_def, ← v225_def, cells4, ← acc220_0_def,
        leLimbsToNat_natToLeLimbs 4 _ (lt_trans (Fp.pow5_lt _) Fp.p_lt), ch0, Fp.add_comm]
  · rw [post234_17, e0, ch1, ch2, Fp.add_comm (leLimbsToNat [c4, c5, c6, c7]), Fp.add_comm (leLimbsToNat [c8, c9, c10, c11])]
  · rw [post234_18, e0, ch1, ch2, Fp.add_comm (leLimbsToNat [c4, c5, c6, c7]), Fp.add_comm (leLimbsToNat [c8, c9, c10, c11])]
  · rw [post234_19, e0, ch1, ch2, Fp.add_comm (leLimbsToNat [c4, c5, c6, c7]), Fp.add_comm (leLimbsToNat [c8, c9, c10, c11])]
  · rw [post234_17]; exact fadd_lt _ _
  · rw [post234_18]; exact fadd_lt _ _
  · rw [post234_19]; exact fadd_lt _ _

end Cases.Zip2005
