import Cases.Zip2005.Field.FromRaw
import Cases.Zip2005.Image.Ro

/-!
# `Fp::from_raw` on a read-only input

`Cases.Zip2005.fp_from_raw_spec` with the input region only required to lie outside the code (so a
constant in the read-only segment, such as `𝒦^Orchard`'s coordinates in `Nullifier::derive`, can be
the argument). Same proof.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
theorem fp_from_raw_ro_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word) (x0 x1 x2 x3 : Word)
    (hpc : s.pc = 0x78028298#64) (hcode : CodeAt F_78028298.base F_78028298.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi a1 4)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd : Disjoint a0 4 a1 4)
    (hd0 : Disjoint (sp - 0x10#64) 2 a0 4) (hd1 : Disjoint (sp - 0x10#64) 2 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) Fp.R2)) t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨O, hO, hOlen⟩ := Region.exists_junk a0 4 s
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(sp - 0x10#64, 2), (a0, 4)] s
  sym_exec
  bn_lin
  have o1 := or_carry_shl62 hb_v142 v144_def v145_def
  have o2 := or_carry_shl62 hb_v166 v168_def v169_def
  have sp1 := split62 v143_def v144_def
  have sp2 := split62 v167_def v168_def
  have sp3 := split62 v194_def v195_def
  have sp4 := split62 v222_def v223_def
  have z1 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v124_def v127_def v130_def
  have z2 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v151_def v153_def v154_def
  have z3 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v178_def v180_def v181_def
  have z4 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v206_def v208_def v209_def
  have row0 : x0.toNat * (10122100416058490895 + 2^64 * 15551789045973377255 + 2^128 * 8617542898466512152 + 2^192 * 679271340751763220)
      = v12.toNat + 2^64 * v18.toNat + 2^128 * v25.toNat + 2^192 * v30.toNat + 2^256 * v32.toNat := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, hn_v12, hn_v13, hn_v14, hn_v15, hn_v18, hn_v19, hn_v20, hn_v21, hn_v22, hn_v25, hn_v26, hn_v27, hn_v28, hn_v29, hn_v30, hn_v31, hn_v32]
  have row1 : (x0.toNat + 2^64 * x1.toNat) * (10122100416058490895 + 2^64 * 15551789045973377255 + 2^128 * 8617542898466512152 + 2^192 * 679271340751763220)
      = v12.toNat + 2^64 * v35.toNat + 2^128 * v43.toNat + 2^192 * v51.toNat + 2^256 * v59.toNat
        + 2^256 * 2^64 * v61.toNat := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, row0, hn_v33, hn_v34, hn_v35, hn_v36, hn_v37, hn_v38, hn_v39, hn_v40, hn_v41, hn_v42, hn_v43, hn_v44, hn_v45, hn_v46, hn_v47, hn_v48, hn_v49, hn_v50, hn_v51, hn_v52, hn_v53, hn_v54, hn_v55, hn_v56, hn_v57, hn_v58, hn_v59, hn_v60, hn_v61]
  have row2 : (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat) * (10122100416058490895 + 2^64 * 15551789045973377255 + 2^128 * 8617542898466512152 + 2^192 * 679271340751763220)
      = v12.toNat + 2^64 * v35.toNat + 2^128 * v64.toNat + 2^192 * v72.toNat + 2^256 * v80.toNat
        + 2^256 * 2^64 * v88.toNat + 2^256 * 2^128 * v90.toNat := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, row1, hn_v62, hn_v63, hn_v64, hn_v65, hn_v66, hn_v67, hn_v68, hn_v69, hn_v70, hn_v71, hn_v72, hn_v73, hn_v74, hn_v75, hn_v76, hn_v77, hn_v78, hn_v79, hn_v80, hn_v81, hn_v82, hn_v83, hn_v84, hn_v85, hn_v86, hn_v87, hn_v88, hn_v89, hn_v90]
  have row3 : (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat) * (10122100416058490895 + 2^64 * 15551789045973377255 + 2^128 * 8617542898466512152 + 2^192 * 679271340751763220)
      = v12.toNat + 2^64 * v35.toNat + 2^128 * v64.toNat + 2^192 * v93.toNat + 2^256 * v101.toNat
        + 2^256 * 2^64 * v109.toNat + 2^256 * 2^128 * v117.toNat + 2^256 * 2^192 * v119.toNat := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, row2, hn_v91, hn_v92, hn_v93, hn_v94, hn_v95, hn_v96, hn_v97, hn_v98, hn_v99, hn_v100, hn_v101, hn_v102, hn_v103, hn_v104, hn_v105, hn_v106, hn_v107, hn_v108, hn_v109, hn_v110, hn_v111, hn_v112, hn_v113, hn_v114, hn_v115, hn_v116, hn_v117, hn_v118, hn_v119]
  have rd0 : v12.toNat + 2^64 * v35.toNat + 2^128 * v64.toNat + 2^192 * v93.toNat + 2^256 * v101.toNat
        + 2^256 * 2^64 * v109.toNat + 2^256 * 2^128 * v117.toNat + 2^256 * 2^192 * v119.toNat + v124.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v138.toNat + 2^64 * v141.toNat + 2^128 * v146.toNat + 2^192 * v149.toNat
        + 2^256 * (v109.toNat + v150.toNat) + 2^256 * 2^64 * v117.toNat + 2^256 * 2^128 * v119.toNat) := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, z1, o1, sp1, hn_v124, hn_v126, hn_v127, hn_v130, hn_v131, hn_v132, hn_v133, hn_v134, hn_v135, hn_v136, hn_v137, hn_v138, hn_v139, hn_v140, hn_v141, hn_v142, hn_v143, hn_v144, hn_v146, hn_v147, hn_v148, hn_v149, hn_v150]
  have rd1 : v138.toNat + 2^64 * v141.toNat + 2^128 * v146.toNat + 2^192 * v149.toNat
        + 2^256 * (v109.toNat + v150.toNat) + 2^256 * 2^64 * v117.toNat + 2^256 * 2^128 * v119.toNat
        + v151.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v162.toNat + 2^64 * v165.toNat + 2^128 * v170.toNat + 2^192 * v175.toNat
        + 2^256 * (v117.toNat + v177.toNat) + 2^256 * 2^64 * v119.toNat) := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, z2, o2, sp2, hn_v151, hn_v152, hn_v153, hn_v154, hn_v155, hn_v156, hn_v157, hn_v158, hn_v159, hn_v160, hn_v161, hn_v162, hn_v163, hn_v164, hn_v165, hn_v166, hn_v167, hn_v168, hn_v170, hn_v171, hn_v172, hn_v173, hn_v174, hn_v175, hn_v176, hn_v177]
  have rd2 : v162.toNat + 2^64 * v165.toNat + 2^128 * v170.toNat + 2^192 * v175.toNat
        + 2^256 * (v117.toNat + v177.toNat) + 2^256 * 2^64 * v119.toNat + v178.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v189.toNat + 2^64 * v192.toNat + 2^128 * v199.toNat + 2^192 * v204.toNat
        + 2^256 * (v119.toNat + v203.toNat + v205.toNat)) := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, z3, sp3, hn_v178, hn_v179, hn_v180, hn_v181, hn_v182, hn_v183, hn_v184, hn_v185, hn_v186, hn_v187, hn_v188, hn_v189, hn_v190, hn_v191, hn_v192, hn_v193, hn_v194, hn_v195, hn_v196, hn_v197, hn_v198, hn_v199, hn_v200, hn_v201, hn_v202, hn_v203, hn_v204, hn_v205]
  have rd3 : v189.toNat + 2^64 * v192.toNat + 2^128 * v199.toNat + 2^192 * v204.toNat
        + 2^256 * (v119.toNat + v203.toNat + v205.toNat) + v206.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v217.toNat + 2^64 * v220.toNat + 2^128 * v227.toNat
        + 2^192 * (v119.toNat + v203.toNat + v205.toNat + v229.toNat)) := by
    linarith only [hz_0, hz_1, hz_2, hz_3, hz_4, hz_5, hz_6, hz_7, hz_8, hz_9, hz_10, hz_11, hz_12, hz_13, hz_14, hz_15, hz_16, hz_17, hz_18, hz_19, hz_20, hz_21, hz_22, hz_23, hz_24, hz_25, hz_26, hz_27, hz_28, hz_29, hz_30, hz_31, hz_32, hz_33, hz_34, hz_35, hz_36, hz_37, hz_38, hz_39, hz_40, hz_41, hz_42, z4, sp4, hn_v206, hn_v207, hn_v208, hn_v209, hn_v210, hn_v211, hn_v212, hn_v213, hn_v214, hn_v215, hn_v216, hn_v217, hn_v218, hn_v219, hn_v220, hn_v221, hn_v222, hn_v223, hn_v224, hn_v225, hn_v226, hn_v227, hn_v228, hn_v229]
  -- the reduction: `2^256 T = X·R2 + M·p`
  have hT : 2 ^ 256 * (v217.toNat + 2^64 * v220.toNat + 2^128 * v227.toNat
        + 2^192 * (v119.toNat + v203.toNat + v205.toNat + v229.toNat))
      = (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat) * Fp.R2
        + (v124.toNat + 2^64 * v151.toNat + 2^128 * v178.toNat + 2^192 * v206.toNat) * Fp.p := by
    rw [show Fp.p = 11037532056220336129 + 2^64 * 2469829653914515739 + 2^254 by decide,
      show Fp.R2 = (10122100416058490895 + 2^64 * 15551789045973377255 + 2^128 * 8617542898466512152 + 2^192 * 679271340751763220) by decide]
    symm; linear_combination row3 + rd0 + 2^64 * rd1 + 2^128 * rd2 + 2^192 * rd3
  have hXe : leLimbsToNat [x0, x1, x2, x3] =
      x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hMe : leLimbsToNat [v124, v151, v178, v206] =
      v124.toNat + 2^64 * v151.toNat + 2^128 * v178.toNat + 2^192 * v206.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hX := leLimbsToNat_lt [x0, x1, x2, x3]
  have hM := leLimbsToNat_lt [v124, v151, v178, v206]
  rw [hXe] at hX
  rw [hMe] at hM
  have hR2 : Fp.R2 < Fp.p := by decide
  have hPi : (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat) * Fp.R2
      < 2 ^ 256 * Fp.p :=
    Nat.mul_lt_mul_of_lt_of_le hX hR2.le (by decide)
  -- the top limb of `T` fits a word, and the product's top limb is below `2^62`
  have hMp : (v124.toNat + 2^64 * v151.toNat + 2^128 * v178.toNat + 2^192 * v206.toNat) * Fp.p
      < 2 ^ 256 * Fp.p := Nat.mul_lt_mul_of_pos_right hM Fp.p_pos
  have ha3 : v119.toNat + v203.toNat + v205.toNat + v229.toNat < 2 ^ 64 :=
    top_lt hT hPi hMp (by decide)
  have ht7 : v119.toNat < 2 ^ 62 := by
    have hR2b : Fp.R2 < 2 ^ 252 := by decide
    have h1 : (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat) * Fp.R2
        < 2 ^ 256 * 2 ^ 252 := Nat.mul_lt_mul_of_lt_of_le hX hR2b.le (by decide)
    rw [show Fp.R2 = (10122100416058490895 + 2^64 * 15551789045973377255 + 2^128 * 8617542898466512152 + 2^192 * 679271340751763220) by decide, row3] at h1
    exact prod_top_lt h1
  have tl := mont_sub_tail_r (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) ht7 hb_v203 hb_v205 ha3 v235_def v239_def v240_def v241_def v243_def v244_def v246_def v247_def v248_def v249_def v250_def v253_def v254_def v255_def v256_def v257_def v258_def v259_def v260_def v261_def v262_def v263_def v265_def v266_def v267_def v268_def v269_def v270_def v271_def v272_def v273_def v274_def v275_def v278_def v279_def v280_def
  dsimp only at tl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide]
    at tl
  have hR := Fp.redc_eq_wide hT hPi hM tl.1 tl.2
  have hRe : leLimbsToNat [v266, v271, v274, v280] =
      v266.toNat + 2^64 * v271.toNat + 2^128 * v274.toNat + 2^192 * v280.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hout : [v266, v271, v274, v280] =
      natToLeLimbs 4 (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) Fp.R2) := by
    rw [Fp.mul, hXe, Nat.mod_mul_mod, ← hR, ← hRe]
    exact (natToLeLimbs_leLimbsToNat _).symm
  sym_close hk
  exact hout

end Cases.Zip2005
