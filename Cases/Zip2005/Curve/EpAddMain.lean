import Cases.Zip2005.Curve.EpDouble
import Cases.Zip2005.Field.FpAddCf
import Cases.Zip2005.Image.F_78026b44
import Cases.Zip2005.Image.Ro

/-!
# `Ep::add`, the general case

The state at `0x780273e0` -- after `z1z1, z2z2, u1, u2, s1, s2` are in the frame and the
`u1 == u2` test has failed -- to the return: sixteen `UINT256_MULMOD`s and the inlined chains
of `add-2007-bl`, as `Fp.addJ_main`.  The frame is `sp - 0x280`; the save area holds the
caller's callee-saved registers `r8 … r27`, which the return restores.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem ep_add_main_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (t : MachineState) (ra sp a0 a1 a2 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (u0 u1 u2 u3 e0 e1 e2 e3 w0 w1 w2 w3 : Word)
    (k0 k1 k2 k3 l0 l1 l2 l3 m0 m1 m2 m3 n0 n1 n2 n3 p0 p1 p2 p3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 : Word) (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : Word)
    (r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : Word)
    (hpc : t.pc = 0x780273e0#64) (hcode : CodeAt F_78026b44.base F_78026b44.prog t)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog t)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi t) (hro : RoImage Ro.layout t)
    (hra1 : ra &&& ~~~1#64 = ra)
    (hstk : StackOk Ro.layout 0x430 sp) (hsp : t.getReg .x2 = sp - 0x280#64)
    (hx8 : t.getReg .x8 = m0)
    (hx9 : t.getReg .x9 = a1)
    (hx10 : t.getReg .x10 = g19)
    (hx11 : t.getReg .x11 = 1#64)
    (hx18 : t.getReg .x18 = a2)
    (hx19 : t.getReg .x19 = 1#64)
    (hx20 : t.getReg .x20 = 11037532056220336129#64)
    (hx21 : t.getReg .x21 = 2469829653914515739#64)
    (hx22 : t.getReg .x22 = n1)
    (hx23 : t.getReg .x23 = m3)
    (hx24 : t.getReg .x24 = m2)
    (hx25 : t.getReg .x25 = n3)
    (hx26 : t.getReg .x26 = m1)
    (hx27 : t.getReg .x27 = n2)
    (hp : Region a1 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] t) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hq : Region a2 [u0, u1, u2, u3, e0, e1, e2, e3, w0, w1, w2, w3] t) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 12)
    (hO : Region a0 [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11] t) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hF : Region (sp - 0x280#64) [g0, g1, g2, g3, g4, g5, g6, 4611686018427387904#64, l1, l2, w0, z0, n1, n2, q0, m3, m2, q1, n3, q2, p1, p2, q3, p3, p0, m0, m1, 8127635680764926565#64, n0, 2445952672640170197#64, l0, l3, 14933811601259063721#64, 12438865661331504215#64, k0, k1, k2, k3, a0, g7, g8, g9, g10, m0, m1, m2, m3, p0, p1, p2, p3, g11, g12, g13, g14, g15, g16, g17, g18, 14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64, 2445952672640170197#64, 11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] t)
    (hFS : Region (sp - 0x68#64) [r27, r26, r25, r24, r23, r22, r21, r20, r19, r18, r9, r8, ra] t)
    (hd0 : Disjoint (sp - 0x430#64) 134 a0 12) (hd1 : Disjoint (sp - 0x430#64) 134 a1 12)
    (hd2 : Disjoint (sp - 0x430#64) 134 a2 12)
    (he1 : Disjoint a0 12 a1 12) (he2 : Disjoint a0 12 a2 12)
    (hZ1 : leLimbsToNat [z0, z1, z2, z3] < Fp.p) (hZ2 : leLimbsToNat [w0, w1, w2, w3] < Fp.p)
    (hK : leLimbsToNat [k0, k1, k2, k3] < Fp.p) (hL : leLimbsToNat [l0, l1, l2, l3] < Fp.p) (hM : leLimbsToNat [m0, m1, m2, m3] < Fp.p) (hN : leLimbsToNat [n0, n1, n2, n3] < Fp.p)
    (hP : leLimbsToNat [p0, p1, p2, p3] < Fp.p) (hQ : leLimbsToNat [q0, q1, q2, q3] < Fp.p)
    (hk : ∀ u, u.pc = ra → u.code = t.code → u.getReg .x2 = sp →
      u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
      u.getReg .x8 = r8 → u.getReg .x9 = r9 → u.getReg .x18 = r18 → u.getReg .x19 = r19 →
      u.getReg .x20 = r20 → u.getReg .x21 = r21 → u.getReg .x22 = r22 → u.getReg .x23 = r23 →
      u.getReg .x24 = r24 → u.getReg .x25 = r25 → u.getReg .x26 = r26 → u.getReg .x27 = r27 →
      Unchanged [(sp - 0x430#64, 134), (a0, 12)] t u →
      Region a0 (natToLeLimbs 4 (Fp.addJ_main (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [l0, l1, l2, l3]) (leLimbsToNat [m0, m1, m2, m3]) (leLimbsToNat [n0, n1, n2, n3]) (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [q0, q1, q2, q3])).1 ++ natToLeLimbs 4 (Fp.addJ_main (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [l0, l1, l2, l3]) (leLimbsToNat [m0, m1, m2, m3]) (leLimbsToNat [n0, n1, n2, n3]) (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [q0, q1, q2, q3])).2.1 ++
        natToLeLimbs 4 (Fp.addJ_main (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [l0, l1, l2, l3]) (leLimbsToNat [m0, m1, m2, m3]) (leLimbsToNat [n0, n1, n2, n3]) (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [q0, q1, q2, q3])).2.2) u → SafeN G n P u) :
    SafeN G n P t := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x430#64) 134 := hstk.frame 134 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x280#64) 67 := hokW.sub' 54 67 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokW.sub' 121 13 (by decide) (by bv_omega)
  have hlo := hstk.lo
  have hu := Unchanged.refl [(sp - 0x430#64, 134), (a0, 12)] t
  sym_exec [uint256_mulmod_spec]
  -- the eight products
  have hI : acc135_0 = Fp.mul (leLimbsToNat [v86, v91, v94, v98]) (leLimbsToNat [v86, v91, v94, v98]) :=
    mulpair acc115_0_def acc135_0_def
  have hIl : leLimbsToNat [v136, v137, v138, v139] = acc135_0 := by
    rw [← v136_def, ← v137_def, ← v138_def, ← v139_def]; exact cells_lt (acc_ltp acc135_0_def)
  have hJ : acc177_0 = Fp.mul (leLimbsToNat [v24, v30, v33, v39]) (leLimbsToNat [v136, v137, v138, v139]) :=
    mulpair acc164_0_def acc177_0_def
  have hJl : leLimbsToNat [v178, v180, v182, v184] = acc177_0 := by
    rw [← v178_def, ← v180_def, ← v182_def, ← v184_def]; exact cells_lt (acc_ltp acc177_0_def)
  have hltJ : leLimbsToNat [v178, v180, v182, v184] < Fp.p := by rw [hJl]; exact acc_ltp acc177_0_def
  have hV : acc317_0 = Fp.mul (leLimbsToNat [m0, m1, m2, m3]) (leLimbsToNat [v136, v137, v138, v139]) :=
    mulpair acc301_0_def acc317_0_def
  have hVl : leLimbsToNat [v318, v320, v322, v324] = acc317_0 := by
    rw [← v318_def, ← v320_def, ← v322_def, ← v324_def]; exact cells_lt (acc_ltp acc317_0_def)
  have hltV : leLimbsToNat [v318, v320, v322, v324] < Fp.p := by rw [hVl]; exact acc_ltp acc317_0_def
  have hRR : acc359_0 = Fp.mul (leLimbsToNat [v263, v268, v271, v275]) (leLimbsToNat [v263, v268, v271, v275]) :=
    mulpair acc346_0_def acc359_0_def
  have hRRl : leLimbsToNat [v360, v361, v362, v363] = acc359_0 := by
    rw [← v360_def, ← v361_def, ← v362_def, ← v363_def]; exact cells_lt (acc_ltp acc359_0_def)
  have hltRR : leLimbsToNat [v360, v361, v362, v363] < Fp.p := by rw [hRRl]; exact acc_ltp acc359_0_def
  have hSJ : acc519_0 = Fp.mul (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [v178, v180, v182, v184]) :=
    mulpair acc506_0_def acc519_0_def
  have hSJl : leLimbsToNat [v520, v521, v522, v523] = acc519_0 := by
    rw [← v520_def, ← v521_def, ← v522_def, ← v523_def]; exact cells_lt (acc_ltp acc519_0_def)
  have hltSJ : leLimbsToNat [v520, v521, v522, v523] < Fp.p := by rw [hSJl]; exact acc_ltp acc519_0_def
  have hRVX : acc654_0 = Fp.mul (leLimbsToNat [v263, v268, v271, v275]) (leLimbsToNat [v613, v618, v621, v625]) :=
    mulpair acc638_0_def acc654_0_def
  have hRVXl : leLimbsToNat [v655, v656, v657, v658] = acc654_0 := by
    rw [← v655_def, ← v656_def, ← v657_def, ← v658_def]; exact cells_lt (acc_ltp acc654_0_def)
  have hltRVX : leLimbsToNat [v655, v656, v657, v658] < Fp.p := by rw [hRVXl]; exact acc_ltp acc654_0_def
  have hZZ2 : acc789_0 = Fp.mul (leLimbsToNat [v744, v749, v752, v756]) (leLimbsToNat [v744, v749, v752, v756]) :=
    mulpair acc773_0_def acc789_0_def
  have hZZ2l : leLimbsToNat [v790, v791, v792, v793] = acc789_0 := by
    rw [← v790_def, ← v791_def, ← v792_def, ← v793_def]; exact cells_lt (acc_ltp acc789_0_def)
  have hltZZ2 : leLimbsToNat [v790, v791, v792, v793] < Fp.p := by rw [hZZ2l]; exact acc_ltp acc789_0_def
  have hZ3 : acc908_0 = Fp.mul (leLimbsToNat [v862, v867, v870, v874]) (leLimbsToNat [v24, v30, v33, v39]) :=
    mulpair acc895_0_def acc908_0_def
  have hZ3l : leLimbsToNat [v909, v910, v911, v912] = acc908_0 := by
    rw [← v909_def, ← v910_def, ← v911_def, ← v912_def]; exact cells_lt (acc_ltp acc908_0_def)
  -- the thirteen inlined chains
  have ch0 := fsub_chain v1_def v2_def v3_def v4_def v5_def v6_def v7_def v8_def v9_def v10_def v11_def v12_def v13_def v14_def v15_def v16_def v17_def v18_def v19_def v20_def v21_def v22_def v23_def v24_def v25_def v27_def v28_def v29_def v30_def v31_def v32_def v33_def v35_def v37_def v38_def v39_def hN hM
  have hlt0 : leLimbsToNat [v24, v30, v33, v39] < Fp.p := by rw [ch0]; exact Fp.sub_lt _ _
  have ch1 := fdbl_chain_fused v41_def v55_def v56_def v57_def v45_def v42_def v68_def v46_def v44_def v53_def (by rw [← v61_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl) : v57 + (v53 + 18446744073709551615#64) = v61) (Bn.carry_either (x := v53 + 18446744073709551615#64) (y := v57) (by rw [← v61_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl)) v62_def) v63_def v65_def v66_def v69_def v70_def v71_def v72_def v73_def v77_def v78_def v79_def v80_def v81_def v82_def v83_def v85_def v86_def v87_def v88_def v89_def v90_def v91_def v92_def v93_def v94_def v95_def v96_def v97_def v98_def hlt0
  have ch2 := fsub_chain v188_def v189_def v191_def v192_def v193_def v194_def v195_def v196_def v197_def v199_def v200_def v201_def v202_def v203_def v204_def v205_def v207_def v208_def v209_def v210_def v211_def v212_def v213_def v214_def v215_def v216_def v217_def v218_def v219_def v220_def v221_def v222_def v223_def v224_def v225_def v226_def hQ hP
  have hlt2 : leLimbsToNat [v214, v219, v222, v226] < Fp.p := by rw [ch2]; exact Fp.sub_lt _ _
  have ch3 := fdbl_chain_fused v227_def v236_def v237_def v238_def v230_def v228_def v247_def v231_def v229_def v234_def (by rw [← v239_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl) : v238 + (v234 + 18446744073709551615#64) = v239) (Bn.carry_either (x := v234 + 18446744073709551615#64) (y := v238) (by rw [← v239_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl)) v240_def) v241_def v244_def v245_def v248_def v249_def v250_def v251_def v252_def v254_def v255_def v256_def v257_def v258_def v259_def v260_def v262_def v263_def v264_def v265_def v266_def v267_def v268_def v269_def v270_def v271_def v272_def v273_def v274_def v275_def hlt2
  have ch4 := fsub_chain v365_def v366_def v368_def v369_def v370_def v371_def v372_def v373_def v374_def v376_def v377_def v378_def v379_def v380_def v381_def v382_def v384_def v385_def v386_def v387_def v388_def v389_def v390_def v391_def v392_def v393_def v394_def v395_def v396_def v397_def v398_def v399_def v400_def v401_def v402_def v403_def hltRR hltJ
  have hlt4 : leLimbsToNat [v391, v396, v399, v403] < Fp.p := by rw [ch4]; exact Fp.sub_lt _ _
  have ch5 := fsubneg_chain v405_def v406_def v407_def v409_def v410_def v411_def v412_def v413_def v414_def v415_def v417_def v418_def v419_def v420_def v421_def v422_def v423_def v425_def v426_def v427_def v428_def v429_def v430_def v431_def v432_def v433_def v434_def v435_def v436_def v437_def v438_def v439_def v440_def v441_def v442_def v443_def v444_def hlt4 hltV
  have hlt5 : leLimbsToNat [v432, v437, v440, v444] < Fp.p := by rw [ch5]; exact Fp.sub_lt _ _
  have ch6 := fsubneg_chain v445_def v446_def v447_def v448_def v449_def v450_def v451_def v452_def v453_def v454_def v455_def v456_def v457_def v458_def v459_def v460_def v461_def v462_def v463_def v464_def v465_def v466_def v467_def v468_def v469_def v471_def v472_def v473_def v474_def v475_def v477_def v478_def v479_def v481_def v482_def v483_def v484_def hlt5 hltV
  have hlt6 : leLimbsToNat [v469, v475, v479, v484] < Fp.p := by rw [ch6]; exact Fp.sub_lt _ _
  have ch7 := fdbl_chain_native v524_def v530_def v529_def v531_def v541_def v540_def v542_def v548_def v547_def v549_def v527_def v532_def v533_def v534_def v537_def v538_def v543_def v544_def v545_def v546_def v550_def v551_def v552_def v553_def v556_def v557_def v559_def v560_def v562_def v563_def v564_def v565_def v566_def v567_def v568_def v570_def v571_def v572_def v573_def v574_def hltSJ
  have hlt7 : leLimbsToNat [v560, v566, v570, v574] < Fp.p := by rw [ch7]; exact Fp.add_lt _ _
  have ch8 := fsub_chain v585_def v586_def v590_def v589_def v593_def v591_def v592_def v594_def v595_def v598_def v597_def (by rw [← v600_def]; all_goals (ac_rfl) : v595 + v597 = v600) (Bn.carry_either (x := v597) (y := v595) v600_def v601_def) v599_def v602_def v603_def v607_def v606_def (by rw [← v609_def]; all_goals (ac_rfl) : v603 + v606 = v609) (Bn.carry_either (x := v606) (y := v603) v609_def v610_def) v608_def v611_def v612_def v613_def v614_def v615_def v616_def v617_def v618_def v619_def v620_def v621_def v622_def v623_def v624_def v625_def hltV hlt6
  have ch9 := fsub_chain v659_def v660_def v662_def v661_def v665_def v663_def v664_def v666_def v667_def v669_def v668_def v671_def v672_def v670_def v673_def v674_def v675_def v676_def v677_def v678_def v679_def v680_def v681_def v682_def v684_def v685_def v686_def v687_def v688_def v689_def v690_def v691_def v692_def v693_def v694_def v695_def hltRVX hlt7
  -- `z1 + z2`, carries taken against limbs of either operand
  have ch10 := fadd_chain_cf v700_def v701_def v704_def v705_def v708_def v709_def v710_def v711_def v712_def v713_def v714_def v715_def v716_def v717_def v720_def v722_def v723_def v724_def v727_def v728_def v730_def v731_def v732_def v733_def v734_def v735_def v736_def v737_def v740_def v741_def v743_def v744_def v745_def v746_def v747_def v748_def v749_def v750_def v751_def v752_def v753_def v754_def v755_def v756_def (by rw [limbs_add_swap]; omega)
  have hzz : leLimbsToNat [v744, v749, v752, v756] =
      Fp.add (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [w0, w1, w2, w3]) := by
    rw [ch10, Fp.add, Fp.add, limbs_add_swap, Nat.add_comm]
  have ch11 := fsub_chain v795_def v796_def v798_def v799_def v800_def v801_def v802_def v803_def v804_def v806_def v807_def v808_def v809_def v810_def v811_def v812_def v814_def v815_def v816_def v817_def v818_def v819_def v820_def v821_def v822_def v823_def v824_def v825_def v826_def v827_def v828_def v829_def v830_def v831_def v832_def v833_def hltZZ2 hK
  have hlt11 : leLimbsToNat [v821, v826, v829, v833] < Fp.p := by rw [ch11]; exact Fp.sub_lt _ _
  have ch12 := fsubneg_chain v835_def v836_def v837_def v839_def v840_def v841_def v842_def v843_def v844_def v845_def v847_def v848_def v849_def v850_def v851_def v852_def v853_def v855_def v856_def v857_def v858_def v859_def v860_def v861_def v862_def v863_def v864_def v865_def v866_def v867_def v868_def v869_def v870_def v871_def v872_def v873_def v874_def hlt11 hL
  -- the model, one equation per step
  have hres := Fp.addJ_main_eq (j := acc177_0) (v := acc317_0)
    (x3a := leLimbsToNat [v391, v396, v399, v403]) (x3b := leLimbsToNat [v432, v437, v440, v444])
    (x3 := leLimbsToNat [v469, v475, v479, v484]) (sj := acc519_0)
    (sj2 := leLimbsToNat [v560, v566, v570, v574]) (vx := leLimbsToNat [v613, v618, v621, v625])
    (y3 := leLimbsToNat [v682, v688, v691, v695]) (za := leLimbsToNat [v821, v826, v829, v833])
    (z3 := leLimbsToNat [v909, v910, v911, v912])
    ch0 ch1 hI (by rw [hJ, hIl]) ch2 ch3 (by rw [hV, hIl]) hRR (by rw [ch4, hRRl, hJl])
    (by rw [ch5, hVl]) (by rw [ch6, hVl]) (by rw [hSJ, hJl]) (by rw [ch7, hSJl]) (by rw [ch8, hVl]) hRVX
    (by rw [ch9, hRVXl]) hzz hZZ2 (by rw [ch11, hZZ2l]) ch12 (by rw [hZ3l]; exact hZ3)
  have e469 : natToLeLimbs 4 (leLimbsToNat [v469, v475, v479, v484]) = [v469, v475, v479, v484] :=
    natToLeLimbs_leLimbsToNat [v469, v475, v479, v484]
  have e682 : natToLeLimbs 4 (leLimbsToNat [v682, v688, v691, v695]) = [v682, v688, v691, v695] :=
    natToLeLimbs_leLimbsToNat [v682, v688, v691, v695]
  have e909 : natToLeLimbs 4 (leLimbsToNat [v909, v910, v911, v912]) = [v909, v910, v911, v912] :=
    natToLeLimbs_leLimbsToNat [v909, v910, v911, v912]
  sym_close hk
  rw [hres]
  simp only [e469, e682, e909]
  rfl

end Cases.Zip2005
