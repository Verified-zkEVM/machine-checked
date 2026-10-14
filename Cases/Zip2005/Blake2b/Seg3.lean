/-
  Cases.Zip2005.Blake2b.Seg3: segment 3 of `compress1_loop` (`0x78035194` to the return), 128-byte input.
  Generated from the executor trace (scratch `b2b_seg.py`): the round-boundary state is passed to the
  continuation word by word, together with the model equation `roundsTo … = [w…]` for the rounds done so far.
-/

import AsmVerif.RiscV.Sym
import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Runtime.MemcpyBytes
import Cases.Zip2005.Blake2b.Blake2bModel
import Cases.Zip2005.Image.F_78033260
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem compress1_seg3 {P : Prop} (t : MachineState) (ra sp wp t0 t1 fb fn : Word)
    (h0 h1 h2 h3 h4 h5 h6 h7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Word) (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : Word) (r27 r26 r25 r24 r23 r22 r21 r20 r19 r18 r9 r8 : Word)
    (hpc : t.pc = 0x78035194#64) (hcode : CodeAt F_78033260.base F_78033260.prog t)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi t) (hra1 : ra &&& ~~~1#64 = ra)
    (hstk : StackOk Ro.layout 0x250 sp) (hsp : t.getReg .x2 = sp - 0x250#64)
    (hx1 : t.getReg .x1 = m4)
    (hx5 : t.getReg .x5 = m15)
    (hx6 : t.getReg .x6 = m9)
    (hx7 : t.getReg .x7 = m2)
    (hx8 : t.getReg .x8 = w8)
    (hx9 : t.getReg .x9 = w15)
    (hx10 : t.getReg .x10 = w0)
    (hx11 : t.getReg .x11 = w1)
    (hx12 : t.getReg .x12 = w4)
    (hx13 : t.getReg .x13 = w2)
    (hx14 : t.getReg .x14 = w3)
    (hx15 : t.getReg .x15 = w12)
    (hx16 : t.getReg .x16 = w13)
    (hx17 : t.getReg .x17 = g26)
    (hx18 : t.getReg .x18 = w14)
    (hx19 : t.getReg .x19 = g27)
    (hx20 : t.getReg .x20 = w9)
    (hx21 : t.getReg .x21 = m3)
    (hx22 : t.getReg .x22 = w10)
    (hx23 : t.getReg .x23 = w7)
    (hx24 : t.getReg .x24 = m0)
    (hx25 : t.getReg .x25 = w11)
    (hx26 : t.getReg .x26 = w5)
    (hx27 : t.getReg .x27 = w6)
    (hx28 : t.getReg .x28 = m14)
    (hx29 : t.getReg .x29 = m6)
    (hx30 : t.getReg .x30 = m8)
    (hx31 : t.getReg .x31 = m10)
    (hF : Region (sp - 0x250#64) [wp, g0, g1, g2, g3, g4, 11912009170470909681#64, 6620516959819538809#64, 4354685564936845355#64, 2270897969802886507#64, 13503953896175478587#64, 11170449401992604703#64, 7640891576956012808#64, 5840696475078001361#64, 0#64, g5, g6, g7, g8, g9, h7, h3, h6, h2, h5, h0, h4, 0#64, h1, m4, m13, m14, m8, m9, m3, m11, m1, m12, m6, m10, m0, m5, m15, m7, m2, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, r27, r26, r25, r24, r23, r22, r21, r20, r19, r18, r9, r8, ra] t)
    (hRH : Region wp [h0, h1, h2, h3, h4, h5, h6, h7] t) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi wp 8)
    (hd2 : Disjoint (sp - 0x250#64) 74 wp 8)
    (hV : roundsTo [h0, h1, h2, h3, h4, h5, h6, h7] [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] t0 t1 fb fn 8 = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15])
    (hk : ∀ u (o0 o1 o2 o3 o4 o5 o6 o7 : Word), u.pc = ra → u.code = t.code →
      u.getReg .x2 = sp → u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
      u.getReg .x8 = r8 → u.getReg .x9 = r9 → u.getReg .x18 = r18 → u.getReg .x19 = r19 → u.getReg .x20 = r20 → u.getReg .x21 = r21 → u.getReg .x22 = r22 → u.getReg .x23 = r23 → u.getReg .x24 = r24 → u.getReg .x25 = r25 → u.getReg .x26 = r26 → u.getReg .x27 = r27 →
      Unchanged [(sp - 0x250#64, 74), (wp, 8)] t u → Region wp [o0, o1, o2, o3, o4, o5, o6, o7] u →
      compress [h0, h1, h2, h3, h4, h5, h6, h7] [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] t0 t1 fb fn = [o0, o1, o2, o3, o4, o5, o6, o7] → Safe P u) :
    Safe P t := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x250#64) 74 := hstk.frame 74 (by decide)
  have hlo := hstk.lo
  have hu := Unchanged.refl [(sp - 0x250#64, 74), (wp, 8)] t
  sym_exec
  have Gs_8_0 := G_step_xb v0_def v1_def ((BitVec.xor_comm w12 v1).trans v2_def) v3_def v4_def ((BitVec.or_comm v3 v4).trans v5_def) ((BitVec.add_comm w8 v5).trans v6_def) ((BitVec.xor_comm w4 v6).trans v7_def) v8_def v9_def ((BitVec.or_comm v8 v9).trans v10_def) v11_def v12_def ((BitVec.xor_comm v5 v12).trans v13_def) v14_def v15_def ((BitVec.or_comm v14 v15).trans v16_def) ((BitVec.add_comm v6 v16).trans v17_def) ((BitVec.xor_comm v10 v17).trans v18_def) v19_def v20_def ((BitVec.or_comm v19 v20).trans v21_def)
  have Gs_8_1 := G_step_xb v22_def v23_def ((BitVec.xor_comm w13 v23).trans v24_def) v25_def v26_def ((BitVec.or_comm v25 v26).trans v27_def) ((BitVec.add_comm w9 v27).trans v28_def) ((BitVec.xor_comm w5 v28).trans v29_def) v30_def v31_def ((BitVec.or_comm v30 v31).trans v32_def) v33_def v34_def ((BitVec.xor_comm v27 v34).trans v35_def) v36_def v37_def ((BitVec.or_comm v36 v37).trans v38_def) ((BitVec.add_comm v28 v38).trans v39_def) ((BitVec.xor_comm v32 v39).trans v40_def) v41_def v42_def ((BitVec.or_comm v41 v42).trans v43_def)
  have Gs_8_2 := G_step_xb v45_def v46_def v47_def v48_def v49_def ((BitVec.or_comm v48 v49).trans v50_def) ((BitVec.add_comm w10 v50).trans v51_def) ((BitVec.xor_comm w6 v51).trans v52_def) v53_def v54_def ((BitVec.or_comm v53 v54).trans v55_def) v56_def v57_def ((BitVec.xor_comm v50 v57).trans v58_def) v59_def v60_def ((BitVec.or_comm v59 v60).trans v61_def) ((BitVec.add_comm v51 v61).trans v62_def) ((BitVec.xor_comm v55 v62).trans v63_def) v64_def v65_def ((BitVec.or_comm v64 v65).trans v66_def)
  have Gs_8_3 := G_step_xb v67_def v68_def ((BitVec.xor_comm w15 v68).trans v69_def) v70_def v71_def ((BitVec.or_comm v70 v71).trans v72_def) ((BitVec.add_comm w11 v72).trans v73_def) ((BitVec.xor_comm w7 v73).trans v74_def) v75_def v76_def ((BitVec.or_comm v75 v76).trans v77_def) v78_def v79_def ((BitVec.xor_comm v72 v79).trans v80_def) v81_def v82_def ((BitVec.or_comm v81 v82).trans v83_def) ((BitVec.add_comm v73 v83).trans v84_def) ((BitVec.xor_comm v77 v84).trans v85_def) v86_def v87_def ((BitVec.or_comm v86 v87).trans v88_def)
  have Gs_8_4 := G_step_xb v90_def v91_def ((BitVec.xor_comm v83 v91).trans v92_def) v93_def v94_def ((BitVec.or_comm v93 v94).trans v95_def) ((BitVec.add_comm v62 v95).trans v96_def) ((BitVec.xor_comm v43 v96).trans v97_def) v98_def v99_def ((BitVec.or_comm v98 v99).trans v100_def) v101_def v102_def ((BitVec.xor_comm v95 v102).trans v103_def) v104_def v105_def ((BitVec.or_comm v104 v105).trans v106_def) ((BitVec.add_comm v96 v106).trans v107_def) ((BitVec.xor_comm v100 v107).trans v108_def) v109_def v110_def ((BitVec.or_comm v109 v110).trans v111_def)
  have Gs_8_5 := G_step_xb v113_def v114_def ((BitVec.xor_comm v16 v114).trans v115_def) v116_def v117_def ((BitVec.or_comm v116 v117).trans v118_def) ((BitVec.add_comm v84 v118).trans v119_def) ((BitVec.xor_comm v66 v119).trans v120_def) v121_def v122_def ((BitVec.or_comm v121 v122).trans v123_def) v125_def v126_def ((BitVec.xor_comm v118 v126).trans v127_def) v128_def v129_def ((BitVec.or_comm v128 v129).trans v130_def) ((BitVec.add_comm v119 v130).trans v131_def) ((BitVec.xor_comm v123 v131).trans v132_def) v133_def v134_def ((BitVec.or_comm v133 v134).trans v135_def)
  have Gs_8_6 := G_step_xb v137_def v138_def ((BitVec.xor_comm v38 v138).trans v139_def) v140_def v141_def ((BitVec.or_comm v140 v141).trans v142_def) ((BitVec.add_comm v17 v142).trans v143_def) ((BitVec.xor_comm v88 v143).trans v144_def) v145_def v146_def ((BitVec.or_comm v145 v146).trans v147_def) v149_def v150_def ((BitVec.xor_comm v142 v150).trans v151_def) v152_def v153_def ((BitVec.or_comm v152 v153).trans v154_def) ((BitVec.add_comm v143 v154).trans v155_def) ((BitVec.xor_comm v147 v155).trans v156_def) v157_def v158_def ((BitVec.or_comm v157 v158).trans v159_def)
  have Gs_8_7 := G_step_xb v160_def v161_def ((BitVec.xor_comm v61 v161).trans v162_def) v163_def v164_def ((BitVec.or_comm v163 v164).trans v165_def) ((BitVec.add_comm v39 v165).trans v166_def) ((BitVec.xor_comm v21 v166).trans v167_def) v168_def v169_def ((BitVec.or_comm v168 v169).trans v170_def) v172_def v173_def ((BitVec.xor_comm v165 v173).trans v174_def) v175_def v176_def ((BitVec.or_comm v175 v176).trans v177_def) ((BitVec.add_comm v166 v177).trans v178_def) ((BitVec.xor_comm v170 v178).trans v179_def) v180_def v181_def ((BitVec.or_comm v180 v181).trans v182_def)
  have Gs_9_0 := G_step_xb v183_def v184_def ((BitVec.xor_comm v130 v184).trans v185_def) v186_def v187_def ((BitVec.or_comm v186 v187).trans v188_def) ((BitVec.add_comm v155 v188).trans v189_def) ((BitVec.xor_comm v182 v189).trans v190_def) v191_def v192_def ((BitVec.or_comm v191 v192).trans v193_def) v194_def v195_def ((BitVec.xor_comm v188 v195).trans v196_def) v197_def v198_def ((BitVec.or_comm v197 v198).trans v199_def) ((BitVec.add_comm v189 v199).trans v200_def) ((BitVec.xor_comm v193 v200).trans v201_def) v202_def v203_def ((BitVec.or_comm v202 v203).trans v204_def)
  have Gs_9_1 := G_step_xb v205_def v206_def ((BitVec.xor_comm v154 v206).trans v207_def) v208_def v209_def ((BitVec.or_comm v208 v209).trans v210_def) ((BitVec.add_comm v178 v210).trans v211_def) ((BitVec.xor_comm v111 v211).trans v212_def) v213_def v214_def ((BitVec.or_comm v213 v214).trans v215_def) v216_def v217_def ((BitVec.xor_comm v210 v217).trans v218_def) v219_def v220_def ((BitVec.or_comm v219 v220).trans v221_def) ((BitVec.add_comm v211 v221).trans v222_def) ((BitVec.xor_comm v215 v222).trans v223_def) v224_def v225_def ((BitVec.or_comm v224 v225).trans v226_def)
  have Gs_9_2 := G_step_xb v227_def v228_def v229_def v230_def v231_def ((BitVec.or_comm v230 v231).trans v232_def) ((BitVec.add_comm v107 v232).trans v233_def) ((BitVec.xor_comm v135 v233).trans v234_def) v235_def v236_def ((BitVec.or_comm v235 v236).trans v237_def) v239_def v240_def ((BitVec.xor_comm v232 v240).trans v241_def) v242_def v243_def ((BitVec.or_comm v242 v243).trans v244_def) ((BitVec.add_comm v233 v244).trans v245_def) ((BitVec.xor_comm v237 v245).trans v246_def) v247_def v248_def ((BitVec.or_comm v247 v248).trans v249_def)
  have Gs_9_3 := G_step_xb v250_def v251_def ((BitVec.xor_comm v106 v251).trans v252_def) v253_def v254_def ((BitVec.or_comm v253 v254).trans v255_def) ((BitVec.add_comm v131 v255).trans v256_def) ((BitVec.xor_comm v159 v256).trans v257_def) v258_def v259_def ((BitVec.or_comm v258 v259).trans v260_def) v261_def v263_def ((BitVec.xor_comm v255 v263).trans v264_def) v265_def v266_def ((BitVec.or_comm v265 v266).trans v267_def) ((BitVec.add_comm v256 v267).trans v268_def) ((BitVec.xor_comm v260 v268).trans v269_def) v270_def v271_def ((BitVec.or_comm v270 v271).trans v272_def)
  have Gs_9_4 := G_step_xb v274_def v275_def ((BitVec.xor_comm v267 v275).trans v276_def) v277_def v278_def ((BitVec.or_comm v277 v278).trans v279_def) ((BitVec.add_comm v245 v279).trans v280_def) ((BitVec.xor_comm v226 v280).trans v281_def) v282_def v283_def ((BitVec.or_comm v282 v283).trans v284_def) v286_def v287_def ((BitVec.xor_comm v279 v287).trans v288_def) v289_def v290_def ((BitVec.or_comm v289 v290).trans v291_def) ((BitVec.add_comm v280 v291).trans v292_def) ((BitVec.xor_comm v284 v292).trans v293_def) v294_def v295_def ((BitVec.or_comm v294 v295).trans v296_def)
  have Gs_9_5 := G_step_xb v298_def v299_def ((BitVec.xor_comm v199 v299).trans v300_def) v301_def v302_def ((BitVec.or_comm v301 v302).trans v303_def) ((BitVec.add_comm v268 v303).trans v304_def) ((BitVec.xor_comm v249 v304).trans v305_def) v306_def v307_def ((BitVec.or_comm v306 v307).trans v308_def) v310_def v311_def ((BitVec.xor_comm v303 v311).trans v312_def) v313_def v314_def ((BitVec.or_comm v313 v314).trans v315_def) ((BitVec.add_comm v304 v315).trans v316_def) ((BitVec.xor_comm v308 v316).trans v317_def) v318_def v319_def ((BitVec.or_comm v318 v319).trans v320_def)
  have Gs_9_6 := G_step_xb v322_def v323_def ((BitVec.xor_comm v221 v323).trans v324_def) v325_def v326_def ((BitVec.or_comm v325 v326).trans v327_def) ((BitVec.add_comm v200 v327).trans v328_def) ((BitVec.xor_comm v272 v328).trans v329_def) v330_def v331_def ((BitVec.or_comm v330 v331).trans v332_def) v333_def v334_def ((BitVec.xor_comm v327 v334).trans v335_def) v336_def v337_def ((BitVec.or_comm v336 v337).trans v338_def) ((BitVec.add_comm v328 v338).trans v339_def) ((BitVec.xor_comm v332 v339).trans v340_def) v341_def v342_def ((BitVec.or_comm v341 v342).trans v343_def)
  have Gs_9_7 := G_step_xb v345_def v346_def ((BitVec.xor_comm v244 v346).trans v347_def) v348_def v349_def ((BitVec.or_comm v348 v349).trans v350_def) ((BitVec.add_comm v222 v350).trans v351_def) ((BitVec.xor_comm v204 v351).trans v352_def) v353_def v354_def ((BitVec.or_comm v353 v354).trans v355_def) v357_def v358_def ((BitVec.xor_comm v350 v358).trans v359_def) v360_def v361_def ((BitVec.or_comm v360 v361).trans v362_def) ((BitVec.add_comm v351 v362).trans v363_def) ((BitVec.xor_comm v355 v363).trans v364_def) v365_def v366_def ((BitVec.or_comm v365 v366).trans v367_def)
  have Gs_10_0 := G_step_xb v368_def v369_def ((BitVec.xor_comm v315 v369).trans v370_def) v371_def v372_def ((BitVec.or_comm v371 v372).trans v373_def) ((BitVec.add_comm v339 v373).trans v374_def) ((BitVec.xor_comm v367 v374).trans v375_def) v376_def v377_def ((BitVec.or_comm v376 v377).trans v378_def) v379_def v380_def ((BitVec.xor_comm v373 v380).trans v381_def) v382_def v383_def ((BitVec.or_comm v382 v383).trans v384_def) ((BitVec.add_comm v374 v384).trans v385_def) ((BitVec.xor_comm v378 v385).trans v386_def) v387_def v388_def ((BitVec.or_comm v387 v388).trans v389_def)
  have Gs_10_1 := G_step_xb v390_def v391_def ((BitVec.xor_comm v338 v391).trans v392_def) v393_def v394_def ((BitVec.or_comm v393 v394).trans v395_def) ((BitVec.add_comm v363 v395).trans v396_def) ((BitVec.xor_comm v296 v396).trans v397_def) v398_def v399_def ((BitVec.or_comm v398 v399).trans v400_def) v401_def v402_def ((BitVec.xor_comm v395 v402).trans v403_def) v404_def v405_def ((BitVec.or_comm v404 v405).trans v406_def) ((BitVec.add_comm v396 v406).trans v407_def) ((BitVec.xor_comm v400 v407).trans v408_def) v409_def v410_def ((BitVec.or_comm v409 v410).trans v411_def)
  have Gs_10_2 := G_step_xb v412_def v413_def v414_def v415_def v416_def ((BitVec.or_comm v415 v416).trans v417_def) ((BitVec.add_comm v292 v417).trans v418_def) ((BitVec.xor_comm v320 v418).trans v419_def) v420_def v421_def ((BitVec.or_comm v420 v421).trans v422_def) v423_def v424_def ((BitVec.xor_comm v417 v424).trans v425_def) v426_def v427_def ((BitVec.or_comm v426 v427).trans v428_def) ((BitVec.add_comm v418 v428).trans v429_def) ((BitVec.xor_comm v422 v429).trans v430_def) v431_def v432_def ((BitVec.or_comm v431 v432).trans v433_def)
  have Gs_10_3 := G_step_xb v434_def v435_def ((BitVec.xor_comm v291 v435).trans v436_def) v437_def v438_def ((BitVec.or_comm v437 v438).trans v439_def) ((BitVec.add_comm v316 v439).trans v440_def) ((BitVec.xor_comm v343 v440).trans v441_def) v442_def v443_def ((BitVec.or_comm v442 v443).trans v444_def) v446_def v447_def ((BitVec.xor_comm v439 v447).trans v448_def) v449_def v450_def ((BitVec.or_comm v449 v450).trans v451_def) ((BitVec.add_comm v440 v451).trans v452_def) ((BitVec.xor_comm v444 v452).trans v453_def) v454_def v455_def ((BitVec.or_comm v454 v455).trans v456_def)
  have Gs_10_4 := G_step_xb v458_def v459_def ((BitVec.xor_comm v451 v459).trans v460_def) v461_def v462_def ((BitVec.or_comm v461 v462).trans v463_def) ((BitVec.add_comm v429 v463).trans v464_def) ((BitVec.xor_comm v411 v464).trans v465_def) v466_def v467_def ((BitVec.or_comm v466 v467).trans v468_def) v470_def v471_def ((BitVec.xor_comm v463 v471).trans v472_def) v473_def v474_def ((BitVec.or_comm v473 v474).trans v475_def) ((BitVec.add_comm v464 v475).trans v476_def) ((BitVec.xor_comm v468 v476).trans v477_def) v478_def v479_def ((BitVec.or_comm v478 v479).trans v480_def)
  have Gs_10_5 := G_step_xb v482_def v483_def ((BitVec.xor_comm v384 v483).trans v484_def) v485_def v486_def ((BitVec.or_comm v485 v486).trans v487_def) ((BitVec.add_comm v452 v487).trans v488_def) ((BitVec.xor_comm v433 v488).trans v489_def) v490_def v491_def ((BitVec.or_comm v490 v491).trans v492_def) v493_def v495_def ((BitVec.xor_comm v487 v495).trans v496_def) v497_def v498_def ((BitVec.or_comm v497 v498).trans v499_def) ((BitVec.add_comm v488 v499).trans v500_def) ((BitVec.xor_comm v492 v500).trans v501_def) v502_def v503_def ((BitVec.or_comm v502 v503).trans v504_def)
  have Gs_10_6 := G_step_xb v506_def v507_def ((BitVec.xor_comm v406 v507).trans v508_def) v509_def v510_def ((BitVec.or_comm v509 v510).trans v511_def) ((BitVec.add_comm v385 v511).trans v512_def) ((BitVec.xor_comm v456 v512).trans v513_def) v514_def v515_def ((BitVec.or_comm v514 v515).trans v516_def) v517_def v518_def ((BitVec.xor_comm v511 v518).trans v519_def) v520_def v521_def ((BitVec.or_comm v520 v521).trans v522_def) ((BitVec.add_comm v512 v522).trans v523_def) ((BitVec.xor_comm v516 v523).trans v524_def) v525_def v526_def ((BitVec.or_comm v525 v526).trans v527_def)
  have Gs_10_7 := G_step_xb v529_def v530_def ((BitVec.xor_comm v428 v530).trans v531_def) v532_def v533_def ((BitVec.or_comm v532 v533).trans v534_def) ((BitVec.add_comm v407 v534).trans v535_def) ((BitVec.xor_comm v389 v535).trans v536_def) v537_def v538_def ((BitVec.or_comm v537 v538).trans v539_def) v541_def v542_def ((BitVec.xor_comm v534 v542).trans v543_def) v544_def v545_def ((BitVec.or_comm v544 v545).trans v546_def) ((BitVec.add_comm v535 v546).trans v547_def) ((BitVec.xor_comm v539 v547).trans v548_def) v549_def v550_def ((BitVec.or_comm v549 v550).trans v551_def)
  have Gs_11_0 := G_step_xb v552_def v553_def ((BitVec.xor_comm v499 v553).trans v554_def) v555_def v556_def ((BitVec.or_comm v555 v556).trans v557_def) ((BitVec.add_comm v523 v557).trans v558_def) ((BitVec.xor_comm v551 v558).trans v559_def) v560_def v561_def ((BitVec.or_comm v560 v561).trans v562_def) v563_def v564_def ((BitVec.xor_comm v557 v564).trans v565_def) v566_def v567_def ((BitVec.or_comm v566 v567).trans v568_def) ((BitVec.add_comm v558 v568).trans v569_def) ((BitVec.xor_comm v562 v569).trans v570_def) v571_def v572_def ((BitVec.or_comm v571 v572).trans v573_def)
  have Gs_11_1 := G_step_xb v574_def v575_def ((BitVec.xor_comm v522 v575).trans v576_def) v577_def v578_def ((BitVec.or_comm v577 v578).trans v579_def) ((BitVec.add_comm v547 v579).trans v580_def) ((BitVec.xor_comm v480 v580).trans v581_def) v582_def v583_def ((BitVec.or_comm v582 v583).trans v584_def) v585_def v586_def ((BitVec.xor_comm v579 v586).trans v587_def) v588_def v589_def ((BitVec.or_comm v588 v589).trans v590_def) ((BitVec.add_comm v580 v590).trans v591_def) ((BitVec.xor_comm v584 v591).trans v592_def) v593_def v594_def ((BitVec.or_comm v593 v594).trans v595_def)
  have Gs_11_2 := G_step_xb v596_def v597_def v598_def v599_def v600_def ((BitVec.or_comm v599 v600).trans v601_def) ((BitVec.add_comm v476 v601).trans v602_def) ((BitVec.xor_comm v504 v602).trans v603_def) v604_def v605_def ((BitVec.or_comm v604 v605).trans v606_def) v607_def v608_def ((BitVec.xor_comm v601 v608).trans v609_def) v610_def v611_def ((BitVec.or_comm v610 v611).trans v612_def) ((BitVec.add_comm v602 v612).trans v613_def) ((BitVec.xor_comm v606 v613).trans v614_def) v615_def v616_def ((BitVec.or_comm v615 v616).trans v617_def)
  have Gs_11_3 := G_step_xb v618_def v619_def ((BitVec.xor_comm v475 v619).trans v620_def) v621_def v622_def ((BitVec.or_comm v621 v622).trans v623_def) ((BitVec.add_comm v500 v623).trans v624_def) ((BitVec.xor_comm v527 v624).trans v625_def) v626_def v627_def ((BitVec.or_comm v626 v627).trans v628_def) v630_def v631_def ((BitVec.xor_comm v623 v631).trans v632_def) v633_def v634_def ((BitVec.or_comm v633 v634).trans v635_def) ((BitVec.add_comm v624 v635).trans v636_def) ((BitVec.xor_comm v628 v636).trans v637_def) v638_def v639_def ((BitVec.or_comm v638 v639).trans v640_def)
  have Gs_11_4 := G_step_xb v642_def v643_def ((BitVec.xor_comm v635 v643).trans v644_def) v645_def v646_def ((BitVec.or_comm v645 v646).trans v647_def) ((BitVec.add_comm v613 v647).trans v648_def) ((BitVec.xor_comm v595 v648).trans v649_def) v650_def v651_def ((BitVec.or_comm v650 v651).trans v652_def) v653_def v654_def ((BitVec.xor_comm v647 v654).trans v655_def) v656_def v657_def ((BitVec.or_comm v656 v657).trans v658_def) ((BitVec.add_comm v648 v658).trans v659_def) ((BitVec.xor_comm v652 v659).trans v660_def) v661_def v662_def ((BitVec.or_comm v661 v662).trans v663_def)
  have Gs_11_5 := G_step_xb v665_def v666_def ((BitVec.xor_comm v568 v666).trans v667_def) v668_def v669_def ((BitVec.or_comm v668 v669).trans v670_def) ((BitVec.add_comm v636 v670).trans v671_def) ((BitVec.xor_comm v617 v671).trans v672_def) v673_def v674_def ((BitVec.or_comm v673 v674).trans v675_def) v677_def v678_def ((BitVec.xor_comm v670 v678).trans v679_def) v680_def v681_def ((BitVec.or_comm v680 v681).trans v682_def) ((BitVec.add_comm v671 v682).trans v683_def) ((BitVec.xor_comm v675 v683).trans v684_def) v685_def v686_def ((BitVec.or_comm v685 v686).trans v687_def)
  have Gs_11_6 := G_step_xb v688_def v689_def ((BitVec.xor_comm v590 v689).trans v690_def) v691_def v692_def ((BitVec.or_comm v691 v692).trans v693_def) ((BitVec.add_comm v569 v693).trans v694_def) ((BitVec.xor_comm v640 v694).trans v695_def) v696_def v697_def ((BitVec.or_comm v696 v697).trans v698_def) v700_def v701_def ((BitVec.xor_comm v693 v701).trans v702_def) v703_def v704_def ((BitVec.or_comm v703 v704).trans v705_def) ((BitVec.add_comm v694 v705).trans v706_def) ((BitVec.xor_comm v698 v706).trans v707_def) v708_def v709_def ((BitVec.or_comm v708 v709).trans v710_def)
  have Gs_11_7 := G_step_xb v712_def v713_def ((BitVec.xor_comm v612 v713).trans v714_def) v715_def v716_def ((BitVec.or_comm v715 v716).trans v717_def) ((BitVec.add_comm v591 v717).trans v718_def) ((BitVec.xor_comm v573 v718).trans v719_def) v720_def v721_def ((BitVec.or_comm v720 v721).trans v722_def) v724_def v725_def ((BitVec.xor_comm v717 v725).trans v726_def) v727_def v728_def ((BitVec.or_comm v727 v728).trans v729_def) ((BitVec.add_comm v718 v729).trans v730_def) ((BitVec.xor_comm v722 v730).trans v731_def) v732_def v733_def ((BitVec.or_comm v732 v733).trans v734_def)
  have hV12 : roundsTo [h0, h1, h2, h3, h4, h5, h6, h7] [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] t0 t1 fb fn 12 = [v654, v678, v701, v725, v734, v663, v687, v710, v706, v730, v659, v683, v682, v705, v729, v658] := by
    simp only [roundsTo_12, hV, round_eq_8, round_eq_9, round_eq_10, round_eq_11, G_pos_0_4_8_12, G_pos_1_5_9_13, G_pos_2_6_10_14, G_pos_3_7_11_15, G_pos_0_5_10_15, G_pos_1_6_11_12, G_pos_2_7_8_13, G_pos_3_4_9_14, Gs_8_0, Gs_8_1, Gs_8_2, Gs_8_3, Gs_8_4, Gs_8_5, Gs_8_6, Gs_8_7, Gs_9_0, Gs_9_1, Gs_9_2, Gs_9_3, Gs_9_4, Gs_9_5, Gs_9_6, Gs_9_7, Gs_10_0, Gs_10_1, Gs_10_2, Gs_10_3, Gs_10_4, Gs_10_5, Gs_10_6, Gs_10_7, Gs_11_0, Gs_11_1, Gs_11_2, Gs_11_3, Gs_11_4, Gs_11_5, Gs_11_6, Gs_11_7]
  have o0 : h0 ^^^ v654 ^^^ v706 = v737 := by
    rw [← v737_def, ← v736_def]; ac_rfl
  have o1 : h1 ^^^ v678 ^^^ v730 = v740 := by
    rw [← v740_def, ← v739_def]; ac_rfl
  have o2 : h2 ^^^ v701 ^^^ v659 = v743 := by
    rw [← v743_def, ← v742_def]; ac_rfl
  have o3 : h3 ^^^ v725 ^^^ v683 = v747 := by
    rw [← v747_def, ← v745_def]; ac_rfl
  have o4 : h4 ^^^ v734 ^^^ v682 = v750 := by
    rw [← v750_def, ← v749_def]; ac_rfl
  have o5 : h5 ^^^ v663 ^^^ v705 = v753 := by
    rw [← v753_def, ← v752_def]; ac_rfl
  have o6 : h6 ^^^ v687 ^^^ v729 = v757 := by
    rw [← v757_def, ← v756_def]; ac_rfl
  have o7 : h7 ^^^ v710 ^^^ v658 = v760 := by
    rw [← v760_def, ← v759_def]; ac_rfl
  sym_close hk _ v737 v740 v743 v747 v750 v753 v757 v760
  rw [compress_eq hV12, o0, o1, o2, o3, o4, o5, o6, o7]

end Cases.Zip2005
