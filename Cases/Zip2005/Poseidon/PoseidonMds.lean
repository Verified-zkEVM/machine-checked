import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Poseidon.PoseidonAdd
import Cases.Zip2005.Image.F_7801e704
import Cases.Zip2005.Image.Ro

/-!
# Poseidon's MDS multiplication (`halo2_poseidon::permute`, the matrix closure)

`state ← mds · state` over `Fp` in Montgomery form: three rows, each three products
(`uint256_mulmod` twice: the product, then `R⁻¹`) accumulated into a zeroed buffer with the inline
`Fp` addition, the buffer copied back over the state.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem mds_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp mp st : Word)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 : Word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word)
    (hpc : s.pc = 0x7801e704#64) (hcode : CodeAt F_7801e704.base F_7801e704.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x170 sp)
    (ha0 : s.getReg .x10 = mp) (ha1 : s.getReg .x11 = st)
    (hM : Region mp [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35] s) (hokM : RegionOk Ro.layout.roBase Ro.layout.textHi mp 36)
    (hX : Region st [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] s) (hokX : RegionOk Ro.layout.roBase Ro.layout.textHi st 12)
    (hd0 : Disjoint (sp - 0x170#64) 46 mp 36) (hd1 : Disjoint (sp - 0x170#64) 46 st 12)
    (hd : Disjoint st 12 mp 36)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x170#64, 46), (st, 12)] s t → ∀ o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : Word, Region st [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11] t →
      leLimbsToNat [o0, o1, o2, o3] = Fp.add (Fp.add (Fp.add 0 (Fp.mul (leLimbsToNat [m0, m1, m2, m3]) (leLimbsToNat [x0, x1, x2, x3]))) (Fp.mul (leLimbsToNat [m4, m5, m6, m7]) (leLimbsToNat [x4, x5, x6, x7]))) (Fp.mul (leLimbsToNat [m8, m9, m10, m11]) (leLimbsToNat [x8, x9, x10, x11])) →
      leLimbsToNat [o4, o5, o6, o7] = Fp.add (Fp.add (Fp.add 0 (Fp.mul (leLimbsToNat [m12, m13, m14, m15]) (leLimbsToNat [x0, x1, x2, x3]))) (Fp.mul (leLimbsToNat [m16, m17, m18, m19]) (leLimbsToNat [x4, x5, x6, x7]))) (Fp.mul (leLimbsToNat [m20, m21, m22, m23]) (leLimbsToNat [x8, x9, x10, x11])) →
      leLimbsToNat [o8, o9, o10, o11] = Fp.add (Fp.add (Fp.add 0 (Fp.mul (leLimbsToNat [m24, m25, m26, m27]) (leLimbsToNat [x0, x1, x2, x3]))) (Fp.mul (leLimbsToNat [m28, m29, m30, m31]) (leLimbsToNat [x4, x5, x6, x7]))) (Fp.mul (leLimbsToNat [m32, m33, m34, m35]) (leLimbsToNat [x8, x9, x10, x11])) → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x170#64) 46 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x170#64) 46 := hstk.frame 46 (by decide)
  have hu := Unchanged.refl [(sp - 0x170#64, 46), (st, 12)] s
  have hlo := hstk.lo
  have hl1 : (mp + 160#64 == mp + 352#64) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, BitVec.add_right_inj]; decide
  have hl2 : (mp + 256#64 == mp + 352#64) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, BitVec.add_right_inj]; decide
  have hl3 : (mp + 352#64 == mp + 352#64) = true := beq_self_eq_true _
  sym_exec [uint256_mulmod_spec, memset96_spec, memcpy96_spec]
  sym_close hk
  · have P1 := mds_prod acc82_0_def acc99_0_def v100_def v101_def v102_def v103_def
    have z : leLimbsToNat [v104, v105, v106, v107] = 0 := by
      rw [← v104_def, ← v105_def, ← v106_def, ← v107_def, ← acc42_0_def]; rfl
    have D1 := fadd_limbs v108_def v109_def v110_def v111_def v112_def v113_def v114_def v115_def v116_def v117_def v118_def v119_def v120_def v121_def
      (by rw [z, P1.1]; exact (padd_lt Fp.p_pos P1.2).1)
    have R1 := padd_reduce (c0_def := v124_def) (e1_def := v126_def) (m0_def := v127_def) (c1a_def := v130_def) (u1_def := v132_def) (t1_def := v133_def) (c1b_def := v134_def) (w1_def := v135_def) (e2_def := v136_def) (m1_def := v137_def) (t2_def := v138_def) (c2_def := v139_def) (w2_def := v140_def) (e3_def := v141_def) (m2_def := v142_def) (c3a_def := v145_def) (u3_def := v147_def) (t3_def := v148_def) (c3b_def := v149_def) (M_def := v150_def) (t0_def := v151_def) (k0_def := v152_def) (r0_def := v153_def) (c4_def := v154_def) (t1'_def := v155_def) (k1_def := v156_def) (s1_def := v157_def) (c5_def := v158_def) (r1_def := v159_def) (c6_def := v160_def) (c7_def := v161_def) (t2'_def := v162_def) (r2_def := v163_def) (c8_def := v164_def) (k3_def := v166_def) (q3_def := v167_def)
      (by rw [D1, z, P1.1]; exact (padd_lt Fp.p_pos P1.2).2)
    rw [D1, z, P1.1] at R1
    have P2 := mds_prod acc192_0_def acc209_0_def v210_def v211_def v212_def v213_def
    rw [and_ones] at v216_def v222_def
    subst v216_def v222_def
    have h1 : v167 + v164 + v213 = v230 := by rw [← v230_def, ← v228_def]; ac_rfl
    have D2 := fadd_limbs v214_def v215_def v217_def v218_def v219_def v220_def v221_def v223_def v224_def v225_def v226_def v227_def h1 v231_def
      (by rw [limbs_swap0, R1, P2.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P2.2).1)
    have R2 := padd_reduce (c0_def := v234_def) (e1_def := v236_def) (m0_def := v237_def) (c1a_def := v240_def) (u1_def := v242_def) (t1_def := v243_def) (c1b_def := v244_def) (w1_def := v245_def) (e2_def := v246_def) (m1_def := v247_def) (t2_def := v248_def) (c2_def := v249_def) (w2_def := v250_def) (e3_def := v251_def) (m2_def := v252_def) (c3a_def := v255_def) (t3_def := v257_def) (c3b_def := v258_def) (u3_def := v259_def) (M_def := v260_def) (t0_def := v261_def) (k0_def := v262_def) (r0_def := v263_def) (c4_def := v264_def) (t1'_def := v265_def) (k1_def := v266_def) (s1_def := v267_def) (c5_def := v268_def) (r1_def := v269_def) (c6_def := v270_def) (c7_def := v271_def) (t2'_def := v272_def) (r2_def := v273_def) (c8_def := v274_def) (k3_def := v276_def) (q3_def := v277_def)
      (by rw [D2, limbs_swap0, R1, P2.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P2.2).2)
    rw [D2, limbs_swap0, R1, P2.1] at R2
    have P3 := mds_prod acc302_0_def acc319_0_def v320_def v321_def v322_def v323_def
    rw [and_ones] at v326_def v332_def
    subst v326_def v332_def
    have h2 : v277 + v274 + v323 = v340 := by rw [← v340_def, ← v338_def]; ac_rfl
    have D3 := fadd_limbs v324_def v325_def v327_def v328_def v329_def v330_def v331_def v333_def v334_def v335_def v336_def v337_def h2 v341_def
      (by rw [limbs_swap0, R2, P3.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P3.2).1)
    have R3 := padd_reduce (c0_def := v344_def) (e1_def := v346_def) (m0_def := v347_def) (c1a_def := v350_def) (u1_def := v352_def) (t1_def := v353_def) (c1b_def := v354_def) (w1_def := v355_def) (e2_def := v356_def) (m1_def := v357_def) (t2_def := v358_def) (c2_def := v359_def) (w2_def := v360_def) (e3_def := v361_def) (m2_def := v362_def) (c3a_def := v365_def) (t3_def := v367_def) (c3b_def := v368_def) (u3_def := v369_def) (M_def := v370_def) (t0_def := v371_def) (k0_def := v372_def) (r0_def := v373_def) (c4_def := v374_def) (t1'_def := v375_def) (k1_def := v376_def) (s1_def := v377_def) (c5_def := v378_def) (r1_def := v379_def) (c6_def := v380_def) (c7_def := v381_def) (t2'_def := v382_def) (r2_def := v383_def) (c8_def := v384_def) (k3_def := v385_def) (q3_def := v386_def)
      (by rw [D3, limbs_swap0, R2, P3.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P3.2).2)
    rw [D3, limbs_swap0, R2, P3.1] at R3
    rw [← v387_def]; exact R3
  · have P1 := mds_prod acc420_0_def acc437_0_def v438_def v439_def v440_def v441_def
    have z : leLimbsToNat [v442, v443, v444, v445] = 0 := by
      rw [← v442_def, ← v443_def, ← v444_def, ← v445_def, ← acc42_0_def]; rfl
    have D1 := fadd_limbs v446_def v447_def v448_def v449_def v450_def v451_def v452_def v453_def v454_def v455_def v456_def v457_def v458_def v459_def
      (by rw [z, P1.1]; exact (padd_lt Fp.p_pos P1.2).1)
    have R1 := padd_reduce (c0_def := v462_def) (e1_def := v464_def) (m0_def := v465_def) (c1a_def := v468_def) (u1_def := v470_def) (t1_def := v471_def) (c1b_def := v472_def) (w1_def := v473_def) (e2_def := v474_def) (m1_def := v475_def) (t2_def := v476_def) (c2_def := v477_def) (w2_def := v478_def) (e3_def := v479_def) (m2_def := v480_def) (c3a_def := v483_def) (u3_def := v485_def) (t3_def := v486_def) (c3b_def := v487_def) (M_def := v488_def) (t0_def := v489_def) (k0_def := v490_def) (r0_def := v491_def) (c4_def := v492_def) (t1'_def := v493_def) (k1_def := v494_def) (s1_def := v495_def) (c5_def := v496_def) (r1_def := v497_def) (c6_def := v498_def) (c7_def := v499_def) (t2'_def := v500_def) (r2_def := v501_def) (c8_def := v502_def) (k3_def := v504_def) (q3_def := v505_def)
      (by rw [D1, z, P1.1]; exact (padd_lt Fp.p_pos P1.2).2)
    rw [D1, z, P1.1] at R1
    have P2 := mds_prod acc530_0_def acc547_0_def v548_def v549_def v550_def v551_def
    rw [and_ones] at v554_def v560_def
    subst v554_def v560_def
    have h1 : v505 + v502 + v551 = v568 := by rw [← v568_def, ← v566_def]; ac_rfl
    have D2 := fadd_limbs v552_def v553_def v555_def v556_def v557_def v558_def v559_def v561_def v562_def v563_def v564_def v565_def h1 v569_def
      (by rw [limbs_swap0, R1, P2.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P2.2).1)
    have R2 := padd_reduce (c0_def := v572_def) (e1_def := v574_def) (m0_def := v575_def) (c1a_def := v578_def) (u1_def := v580_def) (t1_def := v581_def) (c1b_def := v582_def) (w1_def := v583_def) (e2_def := v584_def) (m1_def := v585_def) (t2_def := v586_def) (c2_def := v587_def) (w2_def := v588_def) (e3_def := v589_def) (m2_def := v590_def) (c3a_def := v593_def) (t3_def := v595_def) (c3b_def := v596_def) (u3_def := v597_def) (M_def := v598_def) (t0_def := v599_def) (k0_def := v600_def) (r0_def := v601_def) (c4_def := v602_def) (t1'_def := v603_def) (k1_def := v604_def) (s1_def := v605_def) (c5_def := v606_def) (r1_def := v607_def) (c6_def := v608_def) (c7_def := v609_def) (t2'_def := v610_def) (r2_def := v611_def) (c8_def := v612_def) (k3_def := v614_def) (q3_def := v615_def)
      (by rw [D2, limbs_swap0, R1, P2.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P2.2).2)
    rw [D2, limbs_swap0, R1, P2.1] at R2
    have P3 := mds_prod acc640_0_def acc657_0_def v658_def v659_def v660_def v661_def
    rw [and_ones] at v664_def v670_def
    subst v664_def v670_def
    have h2 : v615 + v612 + v661 = v678 := by rw [← v678_def, ← v676_def]; ac_rfl
    have D3 := fadd_limbs v662_def v663_def v665_def v666_def v667_def v668_def v669_def v671_def v672_def v673_def v674_def v675_def h2 v679_def
      (by rw [limbs_swap0, R2, P3.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P3.2).1)
    have R3 := padd_reduce (c0_def := v682_def) (e1_def := v684_def) (m0_def := v685_def) (c1a_def := v688_def) (u1_def := v690_def) (t1_def := v691_def) (c1b_def := v692_def) (w1_def := v693_def) (e2_def := v694_def) (m1_def := v695_def) (t2_def := v696_def) (c2_def := v697_def) (w2_def := v698_def) (e3_def := v699_def) (m2_def := v700_def) (c3a_def := v703_def) (t3_def := v705_def) (c3b_def := v706_def) (u3_def := v707_def) (M_def := v708_def) (t0_def := v709_def) (k0_def := v710_def) (r0_def := v711_def) (c4_def := v712_def) (t1'_def := v713_def) (k1_def := v714_def) (s1_def := v715_def) (c5_def := v716_def) (r1_def := v717_def) (c6_def := v718_def) (c7_def := v719_def) (t2'_def := v720_def) (r2_def := v721_def) (c8_def := v722_def) (k3_def := v723_def) (q3_def := v724_def)
      (by rw [D3, limbs_swap0, R2, P3.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P3.2).2)
    rw [D3, limbs_swap0, R2, P3.1] at R3
    rw [← v725_def]; exact R3
  · have P1 := mds_prod acc758_0_def acc775_0_def v776_def v777_def v778_def v779_def
    have z : leLimbsToNat [v780, v781, v782, v783] = 0 := by
      rw [← v780_def, ← v781_def, ← v782_def, ← v783_def, ← acc42_0_def]; rfl
    have D1 := fadd_limbs v784_def v785_def v786_def v787_def v788_def v789_def v790_def v791_def v792_def v793_def v794_def v795_def v796_def v797_def
      (by rw [z, P1.1]; exact (padd_lt Fp.p_pos P1.2).1)
    have R1 := padd_reduce (c0_def := v800_def) (e1_def := v802_def) (m0_def := v803_def) (c1a_def := v806_def) (u1_def := v808_def) (t1_def := v809_def) (c1b_def := v810_def) (w1_def := v811_def) (e2_def := v812_def) (m1_def := v813_def) (t2_def := v814_def) (c2_def := v815_def) (w2_def := v816_def) (e3_def := v817_def) (m2_def := v818_def) (c3a_def := v821_def) (u3_def := v823_def) (t3_def := v824_def) (c3b_def := v825_def) (M_def := v826_def) (t0_def := v827_def) (k0_def := v828_def) (r0_def := v829_def) (c4_def := v830_def) (t1'_def := v831_def) (k1_def := v832_def) (s1_def := v833_def) (c5_def := v834_def) (r1_def := v835_def) (c6_def := v836_def) (c7_def := v837_def) (t2'_def := v838_def) (r2_def := v839_def) (c8_def := v840_def) (k3_def := v842_def) (q3_def := v843_def)
      (by rw [D1, z, P1.1]; exact (padd_lt Fp.p_pos P1.2).2)
    rw [D1, z, P1.1] at R1
    have P2 := mds_prod acc868_0_def acc885_0_def v886_def v887_def v888_def v889_def
    rw [and_ones] at v892_def v898_def
    subst v892_def v898_def
    have h1 : v843 + v840 + v889 = v906 := by rw [← v906_def, ← v904_def]; ac_rfl
    have D2 := fadd_limbs v890_def v891_def v893_def v894_def v895_def v896_def v897_def v899_def v900_def v901_def v902_def v903_def h1 v907_def
      (by rw [limbs_swap0, R1, P2.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P2.2).1)
    have R2 := padd_reduce (c0_def := v910_def) (e1_def := v912_def) (m0_def := v913_def) (c1a_def := v916_def) (u1_def := v918_def) (t1_def := v919_def) (c1b_def := v920_def) (w1_def := v921_def) (e2_def := v922_def) (m1_def := v923_def) (t2_def := v924_def) (c2_def := v925_def) (w2_def := v926_def) (e3_def := v927_def) (m2_def := v928_def) (c3a_def := v931_def) (t3_def := v933_def) (c3b_def := v934_def) (u3_def := v935_def) (M_def := v936_def) (t0_def := v937_def) (k0_def := v938_def) (r0_def := v939_def) (c4_def := v940_def) (t1'_def := v941_def) (k1_def := v942_def) (s1_def := v943_def) (c5_def := v944_def) (r1_def := v945_def) (c6_def := v946_def) (c7_def := v947_def) (t2'_def := v948_def) (r2_def := v949_def) (c8_def := v950_def) (k3_def := v952_def) (q3_def := v953_def)
      (by rw [D2, limbs_swap0, R1, P2.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P2.2).2)
    rw [D2, limbs_swap0, R1, P2.1] at R2
    have P3 := mds_prod acc978_0_def acc995_0_def v996_def v997_def v998_def v999_def
    rw [and_ones] at v1002_def v1008_def
    subst v1002_def v1008_def
    have h2 : v953 + v950 + v999 = v1016 := by rw [← v1016_def, ← v1014_def]; ac_rfl
    have D3 := fadd_limbs v1000_def v1001_def v1003_def v1004_def v1005_def v1006_def v1007_def v1009_def v1010_def v1011_def v1012_def v1013_def h2 v1017_def
      (by rw [limbs_swap0, R2, P3.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P3.2).1)
    have R3 := padd_reduce (c0_def := v1020_def) (e1_def := v1022_def) (m0_def := v1023_def) (c1a_def := v1026_def) (u1_def := v1028_def) (t1_def := v1029_def) (c1b_def := v1030_def) (w1_def := v1031_def) (e2_def := v1032_def) (m1_def := v1033_def) (t2_def := v1034_def) (c2_def := v1035_def) (w2_def := v1036_def) (e3_def := v1037_def) (m2_def := v1038_def) (c3a_def := v1041_def) (t3_def := v1043_def) (c3b_def := v1044_def) (u3_def := v1045_def) (M_def := v1046_def) (t0_def := v1047_def) (k0_def := v1048_def) (r0_def := v1049_def) (c4_def := v1050_def) (t1'_def := v1051_def) (k1_def := v1052_def) (s1_def := v1053_def) (c5_def := v1054_def) (r1_def := v1055_def) (c6_def := v1056_def) (c7_def := v1057_def) (t2'_def := v1058_def) (r2_def := v1059_def) (c8_def := v1060_def) (k3_def := v1061_def) (q3_def := v1062_def)
      (by rw [D3, limbs_swap0, R2, P3.1]; exact (padd_lt (Nat.mod_lt _ Fp.p_pos) P3.2).2)
    rw [D3, limbs_swap0, R2, P3.1] at R3
    rw [← v1063_def]; exact R3

end Cases.Zip2005
