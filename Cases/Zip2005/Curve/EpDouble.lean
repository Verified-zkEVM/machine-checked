import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Field.PowT
import Cases.Zip2005.Field.FpAdd
import Cases.Zip2005.Field.FpSub
import Cases.Zip2005.Field.FpDbl
import Cases.Zip2005.Field.FpSubNeg
import Cases.Zip2005.Curve.EpModel
import Cases.Zip2005.Image.F_7802413c
import Cases.Zip2005.Image.Ro

/-!
# `Ep::double`

Jacobian doubling on Pallas (`a = 0`, the `dbl-2009-l` formulas of `pasta_curves`): seven
`Fp::mul`s (`UINT256_MULMOD` pairs), one inlined `Fp::add`, five `Fp::sub`s (two scheduled
neg-first), seven `Fp::double`s (shift-based, six with the fused top limb), the fused `a + 2a`,
then `conditional_select(&tmp, &identity, self.is_identity())` through `black_box`.
The result is `Cases.Zip2005.Fp.dblJ`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem Fp.add_comm (a b : Nat) : Fp.add a b = Fp.add b a := by
  unfold Fp.add; rw [Nat.add_comm]

/-- `(bw c - 1) &&& w`: the `conditional_select` mask. -/
theorem bwm1_and (c : Bool) (w : Word) :
    bw c + 18446744073709551615#64 &&& w = if c then 0#64 else w := by
  cases c
  · simp only [bw, Bool.false_eq_true, if_false, BitVec.zero_add]
    rw [show (18446744073709551615#64 : Word) = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]
  · simp [bw]

/-- `dblJ`, one equation per machine step. -/
theorem Fp.dblJ_eq {X Y Z a b c d0 d2 d3 d4 d e2 e f zy z3 dd x3 c2 c4 c8 dx edx y3 : Nat}
    (ha : a = Fp.mul X X) (hb : b = Fp.mul Y Y) (hc : c = Fp.mul b b)
    (hd0 : d0 = Fp.add X b) (hd2 : d2 = Fp.mul d0 d0) (hd3 : d3 = Fp.sub d2 a) (hd4 : d4 = Fp.sub d3 c)
    (hd : d = Fp.add d4 d4) (he2 : e2 = Fp.add a a) (he : e = Fp.add e2 a) (hf : f = Fp.mul e e)
    (hzy : zy = Fp.mul Z Y) (hz3 : z3 = Fp.add zy zy) (hdd : dd = Fp.add d d) (hx3 : x3 = Fp.sub f dd)
    (hc2 : c2 = Fp.add c c) (hc4 : c4 = Fp.add c2 c2) (hc8 : c8 = Fp.add c4 c4)
    (hdx : dx = Fp.sub d x3) (hedx : edx = Fp.mul e dx) (hy3 : y3 = Fp.sub edx c8) :
    Fp.dblJ X Y Z = if Z = 0 then (0, 0, 0) else (x3, y3, z3) := by
  subst ha hb hc hd0 hd2 hd3 hd4 hd he2 he hf hzy hz3 hdd hx3 hc2 hc4 hc8 hdx hedx hy3
  rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem ep_double_spec {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x7802413c#64) (hcode : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1b0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a1 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x1b0#64) 54 a0 12) (hd1 : Disjoint (sp - 0x1b0#64) 54 a1 12)
    (he1 : Disjoint a0 12 a1 12)
    (hX : leLimbsToNat [x0, x1, x2, x3] < Fp.p)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1b0#64, 54), (a0, 12)] s t →
      Region a0 (natToLeLimbs 4 (Fp.dblJ (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [z0, z1, z2, z3])).1 ++
        natToLeLimbs 4 (Fp.dblJ (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [z0, z1, z2, z3])).2.1 ++
        natToLeLimbs 4 (Fp.dblJ (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [z0, z1, z2, z3])).2.2) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1b0#64) 54 := hstk.frame 54 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1a0#64) 39 := hokW.sub' 2 39 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokW.sub' 41 13 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x1a0#64) 39 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x1b0#64, 54), (a0, 12)] s
  have hlo := hstk.lo
  sym_exec [uint256_mulmod_spec, black_box_spec]
  -- the seven products
  have hA : acc69_0 = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3]) := mulpair acc48_0_def acc69_0_def
  have hAl : leLimbsToNat [v82, v84, v86, v88] = acc69_0 := by
    rw [← v82_def, ← v84_def, ← v86_def, ← v88_def]; exact cells_lt (acc_ltp acc69_0_def)
  have hltA : leLimbsToNat [v82, v84, v86, v88] < Fp.p := by rw [hAl]; exact acc_ltp acc69_0_def
  have hB : acc115_0 = Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [y0, y1, y2, y3]) := mulpair acc102_0_def acc115_0_def
  have hBl : leLimbsToNat [v116, v117, v118, v119] = acc115_0 := by
    rw [← v116_def, ← v117_def, ← v118_def, ← v119_def]; exact cells_lt (acc_ltp acc115_0_def)
  have hltB : leLimbsToNat [v116, v117, v118, v119] < Fp.p := by rw [hBl]; exact acc_ltp acc115_0_def
  have hC : acc151_0 = Fp.mul acc115_0 acc115_0 := by rw [mulpair acc136_0_def acc151_0_def, hBl]
  have hCl : leLimbsToNat [v152, v154, v156, v158] = acc151_0 := by
    rw [← v152_def, ← v154_def, ← v156_def, ← v158_def]; exact cells_lt (acc_ltp acc151_0_def)
  have hltC : leLimbsToNat [v152, v154, v156, v158] < Fp.p := by rw [hCl]; exact acc_ltp acc151_0_def
  have hD2 : acc253_0 = Fp.mul (leLimbsToNat [v209, v214, v217, v221]) (leLimbsToNat [v209, v214, v217, v221]) :=
    mulpair acc238_0_def acc253_0_def
  have hD2l : leLimbsToNat [v254, v255, v256, v257] = acc253_0 := by
    rw [← v254_def, ← v255_def, ← v256_def, ← v257_def]; exact cells_lt (acc_ltp acc253_0_def)
  have hltD2 : leLimbsToNat [v254, v255, v256, v257] < Fp.p := by rw [hD2l]; exact acc_ltp acc253_0_def
  have hF : acc526_0 = Fp.mul (leLimbsToNat [v476, v481, v485, v490]) (leLimbsToNat [v476, v481, v485, v490]) :=
    mulpair acc509_0_def acc526_0_def
  have hFl : leLimbsToNat [v527, v528, v529, v530] = acc526_0 := by
    rw [← v527_def, ← v528_def, ← v529_def, ← v530_def]; exact cells_lt (acc_ltp acc526_0_def)
  have hltF : leLimbsToNat [v527, v528, v529, v530] < Fp.p := by rw [hFl]; exact acc_ltp acc526_0_def
  have hZY : acc569_0 = Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [y0, y1, y2, y3]) := mulpair acc556_0_def acc569_0_def
  have hZYl : leLimbsToNat [v570, v571, v572, v573] = acc569_0 := by
    rw [← v570_def, ← v571_def, ← v572_def, ← v573_def]; exact cells_lt (acc_ltp acc569_0_def)
  have hltZY : leLimbsToNat [v570, v571, v572, v573] < Fp.p := by rw [hZYl]; exact acc_ltp acc569_0_def
  have hEDX : acc929_0 = Fp.mul (leLimbsToNat [v476, v481, v485, v490]) (leLimbsToNat [v888, v893, v898, v900]) :=
    mulpair acc913_0_def acc929_0_def
  have hEDXl : leLimbsToNat [v930, v931, v932, v933] = acc929_0 := by
    rw [← v930_def, ← v931_def, ← v932_def, ← v933_def]; exact cells_lt (acc_ltp acc929_0_def)
  have hltEDX : leLimbsToNat [v930, v931, v932, v933] < Fp.p := by rw [hEDXl]; exact acc_ltp acc929_0_def
  -- the add/sub/double chains, in program order
  have ch0 := fadd_chain v164_def v165_def v166_def v167_def v168_def v169_def v170_def v171_def v172_def v173_def v174_def v175_def v176_def v177_def v183_def v187_def v188_def v189_def v191_def v192_def v194_def v195_def v196_def v197_def v198_def v199_def v200_def v201_def v205_def v206_def v208_def v209_def v210_def v211_def v212_def v213_def v214_def v215_def v216_def v217_def v218_def v219_def v220_def v221_def hX hltB
  have ch1 := fsub_chain v259_def v260_def v262_def v263_def v264_def v265_def v266_def v267_def v268_def v270_def v271_def v272_def v273_def v274_def v275_def v276_def v278_def v279_def v280_def v281_def v282_def v283_def v284_def v285_def v286_def v287_def v288_def v289_def v290_def v291_def v292_def v293_def v294_def v295_def v296_def v297_def hltD2 hltA
  have hlt1 : leLimbsToNat [v285, v290, v293, v297] < Fp.p := by rw [ch1]; exact Fp.sub_lt _ _
  have ch2 := fsubneg_chain v299_def v300_def v301_def v303_def v304_def v305_def v306_def v307_def v308_def v309_def v311_def v312_def v313_def v314_def v315_def v316_def v317_def v319_def v320_def v321_def v322_def v323_def v324_def v325_def v326_def v327_def v328_def v329_def v330_def v331_def v332_def v333_def v334_def v335_def v336_def v337_def v338_def hlt1 hltC
  have hlt2 : leLimbsToNat [v326, v331, v334, v338] < Fp.p := by rw [ch2]; exact Fp.sub_lt _ _
  have ch3 := fdbl_chain_fused v339_def v347_def v348_def v349_def v342_def v340_def v357_def v343_def v341_def v345_def (by rw [← v350_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl) : v349 + (v345 + 18446744073709551615#64) = v350) (Bn.carry_either (x := v345 + 18446744073709551615#64) (y := v349) (by rw [← v350_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl)) v351_def) v352_def v354_def v355_def v358_def v359_def v360_def v361_def v362_def v364_def v365_def v366_def v367_def v368_def v369_def v370_def v372_def v373_def v375_def v376_def v377_def v378_def v379_def v381_def v382_def v383_def v385_def v386_def v387_def v388_def hlt2
  have hlt3 : leLimbsToNat [v373, v379, v383, v388] < Fp.p := by rw [ch3]; exact Fp.add_lt _ _
  -- `2a`, whose last two steps are fused into `a + 2a`
  have ch2A := fdbl_chain_fused v390_def v400_def v399_def v401_def v393_def v391_def v410_def v394_def v392_def v397_def v402_def v403_def v404_def v407_def v408_def v411_def v412_def v413_def v414_def v415_def v416_def v418_def v419_def v420_def v421_def v422_def v423_def v425_def v426_def v427_def v428_def v429_def v430_def v431_def v432_def v433_def v434_def v435_def v436_def rfl rfl hltA
  have hlt2A : leLimbsToNat [v426, v431, v434, v436 + v421 + v435] < Fp.p := by rw [ch2A]; exact Fp.add_lt _ _
  have ch4 := fadd_chain v437_def v438_def (by rw [← v439_def]; ac_rfl : v84 + v431 = v439)
    (Bn.carry_either v439_def v440_def) v441_def v442_def v443_def
    (by rw [← v444_def]; ac_rfl : v86 + v434 = v444) (Bn.carry_either v444_def v445_def) v446_def v447_def
    v448_def (by rw [← v451_def, ← v450_def, ← v449_def]; ac_rfl : v88 + (v436 + v421 + v435) = v451) v452_def
    v454_def v456_def v457_def v458_def v460_def v461_def v463_def v464_def v465_def v466_def v467_def v468_def v469_def v470_def v472_def v473_def v475_def v476_def v477_def v478_def v479_def v480_def v481_def v483_def v484_def v485_def v487_def v488_def v489_def v490_def hltA hlt2A
  have ch5 := fdbl_chain_native v574_def v579_def v578_def v580_def v590_def v589_def v591_def v597_def v596_def v598_def v576_def v581_def v582_def v583_def v586_def v587_def v592_def v593_def v594_def v595_def v599_def v600_def v601_def v602_def v605_def v606_def v608_def v609_def v611_def v612_def v613_def v614_def v615_def v617_def v618_def v619_def v621_def v622_def v623_def v624_def hltZY
  have ch6 := fdbl_chain_fused v627_def v633_def v634_def v635_def v643_def v629_def v645_def v654_def v650_def v631_def (by rw [← v636_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl) : v635 + (v631 + 18446744073709551615#64) = v636) (Bn.carry_either (x := v631 + 18446744073709551615#64) (y := v635) (by rw [← v636_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl)) v637_def) v638_def v640_def v641_def v646_def v647_def v648_def v649_def v651_def v652_def v655_def v656_def v657_def v658_def v659_def v660_def v662_def v663_def v664_def v665_def v666_def v667_def v668_def v669_def v670_def v673_def v674_def v671_def v672_def v675_def hlt3
  have hlt6 : leLimbsToNat [v663, v668, v673, v675] < Fp.p := by rw [ch6]; exact Fp.add_lt _ _
  have ch7 := fsub_chain v676_def v677_def v679_def v678_def v680_def v681_def v682_def v683_def v686_def v685_def v684_def (by rw [← v688_def]; all_goals (ac_rfl) : v686 + v684 = v688) (Bn.carry_either (x := v684) (y := v686) v688_def v689_def) v687_def v690_def v691_def v694_def v693_def (by rw [← v696_def]; all_goals (ac_rfl) : v691 + v693 = v696) (Bn.carry_either (x := v693) (y := v691) v696_def v697_def) v695_def v698_def v699_def v700_def v701_def v702_def v703_def v704_def v705_def v706_def v707_def v708_def v709_def v710_def v711_def v712_def hltF hlt6
  have hlt7 : leLimbsToNat [v700, v705, v708, v712] < Fp.p := by rw [ch7]; exact Fp.sub_lt _ _
  have ch8 := fdbl_chain_fused v714_def v721_def v720_def v722_def v731_def v716_def v735_def v733_def v730_def v718_def v723_def v724_def v725_def v727_def v728_def v736_def v737_def v738_def v739_def v740_def v741_def v742_def v743_def v744_def v745_def v746_def v747_def v749_def v750_def v751_def v752_def v753_def v754_def v755_def v756_def v757_def v758_def v759_def v760_def v761_def v762_def hltC
  have hlt8 : leLimbsToNat [v750, v755, v758, v762] < Fp.p := by rw [ch8]; exact Fp.add_lt _ _
  have ch9 := fdbl_chain_fused v763_def v768_def v769_def v770_def v778_def v764_def v781_def v779_def v777_def v766_def (by rw [← v771_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl) : v770 + (v766 + 18446744073709551615#64) = v771) (Bn.carry_either (x := v766 + 18446744073709551615#64) (y := v770) (by rw [← v771_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl)) v772_def) v773_def v775_def v776_def v782_def v783_def v784_def v785_def v786_def v787_def v788_def v789_def v790_def v791_def v792_def v793_def v795_def v796_def v797_def v798_def v799_def v800_def v801_def v802_def v803_def v804_def v805_def v806_def v807_def v808_def hlt8
  have hlt9 : leLimbsToNat [v796, v801, v804, v808] < Fp.p := by rw [ch9]; exact Fp.add_lt _ _
  have ch10 := fdbl_chain_fused v809_def v813_def v814_def v815_def v823_def v819_def v825_def v831_def v830_def v811_def (by rw [← v816_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl) : v815 + (v811 + 18446744073709551615#64) = v816) (Bn.carry_either (x := v811 + 18446744073709551615#64) (y := v815) (by rw [← v816_def]; all_goals (generalize (18446744073709551615#64 : Word) = c0; ac_rfl)) v817_def) v818_def v821_def v822_def v826_def v827_def v828_def v829_def v832_def v833_def v834_def v835_def v836_def v837_def v838_def v839_def v841_def v842_def v843_def v844_def v845_def v846_def v847_def v848_def v849_def v852_def v853_def v850_def v851_def v854_def hlt9
  have hlt10 : leLimbsToNat [v842, v847, v852, v854] < Fp.p := by rw [ch10]; exact Fp.add_lt _ _
  have ch11 := fsubneg_chain v863_def v864_def v865_def v866_def v867_def v868_def v869_def v870_def v871_def v872_def v873_def v874_def v875_def v876_def v877_def v878_def v879_def v881_def v882_def v883_def v884_def v885_def v886_def v887_def v888_def v889_def v890_def v891_def v892_def v893_def v894_def v895_def v898_def v899_def v896_def v897_def v900_def hlt3 hlt7
  have ch12 := fsub_chain v934_def v935_def v937_def v936_def v940_def v938_def v939_def v941_def v942_def v944_def v943_def v946_def v947_def v945_def v948_def v949_def v950_def v951_def v952_def v953_def v954_def v955_def v956_def v957_def v958_def v959_def v960_def v961_def v962_def v963_def v964_def v965_def v966_def v968_def v969_def v970_def hltEDX hlt10
  -- the result, step by step
  have hres := Fp.dblJ_eq (d3 := leLimbsToNat [v285, v290, v293, v297])
    (e2 := leLimbsToNat [v426, v431, v434, v436 + v421 + v435]) (z3 := leLimbsToNat [v609, v615, v619, v624])
    (y3 := leLimbsToNat [v957, v962, v965, v970]) hA hB hC (by rw [ch0, hBl]) hD2 (by rw [ch1, hD2l, hAl]) (by rw [ch2, hCl]) ch3
    (by rw [ch2A, hAl]) (by rw [ch4, hAl, Fp.add_comm]) hF hZY (by rw [ch5, hZYl]) ch6 (by rw [ch7, hFl])
    (by rw [ch8, hCl]) ch9 ch10 ch11 hEDX (by rw [ch12, hEDXl])
  -- `is_identity` and the select
  have hid : (z3 = 0#64 ∧ z2 = 0#64 ∧ z1 = 0#64 ∧ z0 = 0#64) ↔ leLimbsToNat [z0, z1, z2, z3] = 0 := by
    rw [limbs_zero4]; constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h3, h2, h1⟩
  have hv1008 : v1008 = bw (decide (leLimbsToNat [z0, z1, z2, z3] = 0)) := by
    rw [← v1008_def, ← v1004_def, ← v1003_def, ← v999_def, ← v998_def, ← v993_def, ← v992_def, ← v988_def,
      ← v987_def, ← v982_def, ← v981_def, ← v977_def, ← v976_def, ← v971_def]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw, beq_zero_decide, ← Bool.decide_and]
    rw [decide_eq_decide.mpr hid]
  have e700 : natToLeLimbs 4 (leLimbsToNat [v700, v705, v708, v712]) = [v700, v705, v708, v712] :=
    natToLeLimbs_leLimbsToNat [v700, v705, v708, v712]
  have e957 : natToLeLimbs 4 (leLimbsToNat [v957, v962, v965, v970]) = [v957, v962, v965, v970] :=
    natToLeLimbs_leLimbsToNat [v957, v962, v965, v970]
  have e609 : natToLeLimbs 4 (leLimbsToNat [v609, v615, v619, v624]) = [v609, v615, v619, v624] :=
    natToLeLimbs_leLimbsToNat [v609, v615, v619, v624]
  sym_close hk
  rw [hres, ← v1010_def, ← v1011_def, ← v1012_def, ← v1014_def, ← v1015_def, ← v1016_def, ← v1017_def,
    ← v1018_def, ← v1020_def, ← v1022_def, ← v1024_def, ← v1026_def, hv1008]
  simp only [bwm1_and, decide_eq_true_eq]
  by_cases hz : leLimbsToNat [z0, z1, z2, z3] = 0
  · simp only [if_pos hz]; rfl
  · simp only [if_neg hz, e700, e957, e609]
    rfl

end Cases.Zip2005
