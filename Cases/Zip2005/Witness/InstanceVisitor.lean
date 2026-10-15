import Cases.Zip2005.Witness.Array32R0
import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Image.F_780191c4
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Zip2005Instance`'s serde visitor (`deserialize_struct`, 0x780191c4)

The four `Bytes32` fields (`anchor`, `rk`, `nf`, `sighash`) read in turn by `ArrayVisitor<u8, 32>`
from the reader's aligned input `q` (four blocks of four words), each result unpacked from its
`Result` and the struct written as `Ok(instance)`: tag byte 0, then the 128 input bytes, at
`out + 1`. The first `Err` is passed up (tag 1, the boxed error at `out + 8`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- Byte `k` of `Ok(instance)`: the tag, then the input bytes. -/
def instByte (W : List Word) (k : Nat) : BitVec 8 := if k = 0 then 0#8 else inByte W 0 (k - 1)

/-- `Ok(instance)` over the 17 words `O`, the input words `W` (16). -/
def instW (O W : List Word) : List Word :=
  (List.range 16).map (fun j => word8 (instByte W (8 * j)) (instByte W (8 * j + 1))
    (instByte W (8 * j + 2)) (instByte W (8 * j + 3)) (instByte W (8 * j + 4))
    (instByte W (8 * j + 5)) (instByte W (8 * j + 6)) (instByte W (8 * j + 7))) ++
  [replaceByte O[16]! 0 (instByte W 128)]

@[simp] theorem instW_length (O W : List Word) : (instW O W).length = 17 := by simp [instW]

/-- A cell of four four-word blocks laid end to end. -/
theorem get4 (W0 W1 W2 W3 : List Word) (h0 : W0.length = 4) (h1 : W1.length = 4)
    (h2 : W2.length = 4) (h3 : W3.length = 4) (j : Nat) (hj : j < 16) :
    (W0 ++ W1 ++ W2 ++ W3)[j]! =
      if j < 4 then W0[j]! else if j < 8 then W1[j - 4]! else if j < 12 then W2[j - 8]! else W3[j - 12]! := by
  rw [AsmVerif.RiscV.Sym.List.eq_map_range W0 h0, AsmVerif.RiscV.Sym.List.eq_map_range W1 h1, AsmVerif.RiscV.Sym.List.eq_map_range W2 h2,
    AsmVerif.RiscV.Sym.List.eq_map_range W3 h3]
  interval_cases j <;> rfl

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option asmverif.sym.foldBytes true in
theorem instance_visitor_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W0 W1 W2 W3 : List Word) (hOl : O.length = 17)
    (hW0l : W0.length = 4) (hW1l : W1.length = 4) (hW2l : W2.length = 4) (hW3l : W3.length = 4)
    (hpc : s.pc = 0x780191c4#64) (hcode : CodeAt F_780191c4.base F_780191c4.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x420 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha5 : s.getReg .x15 = 4#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 17)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW0 : Region q W0 s) (hW1 : Region (q + 32#64) W1 s) (hW2 : Region (q + 64#64) W2 s)
    (hW3 : Region (q + 96#64) W3 s)
    (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 16)
    (hdO : Disjoint (sp - 0x420#64) 132 out 17) (hdD : Disjoint (sp - 0x420#64) 132 de 2)
    (heD : Disjoint out 17 de 2) (hOlo : out.toNat + 136 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      t.privateInput = s.privateInput →
      Unchanged [(sp - 0x420#64, 132), (out, 17), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (instW O (W0 ++ W1 ++ W2 ++ W3)) t → Region de [q + 128#64, l - 128#64] t →
      128 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      t.privateInput = s.privateInput →
      Unchanged [(sp - 0x420#64, 132), (out, 17), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t →
      l.toNat < 128 → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x420#64) 132 := hstk.frame 132 (by decide)
  have hu := Unchanged.refl [(sp - 0x420#64, 132), (out, 17), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hI : s.privateInput = s.privateInput := rfl
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokW0 : RegionOk Ro.layout.textLo Ro.layout.textHi q 4 := hokW.sub' 0 4 (by decide) (by bv_omega)
  have hokW1 : RegionOk Ro.layout.textLo Ro.layout.textHi (q + 32#64) 4 := hokW.sub' 4 4 (by decide) (by bv_omega)
  have hokW2 : RegionOk Ro.layout.textLo Ro.layout.textHi (q + 64#64) 4 := hokW.sub' 8 4 (by decide) (by bv_omega)
  have hokW3 : RegionOk Ro.layout.textLo Ro.layout.textHi (q + 96#64) 4 := hokW.sub' 12 4 (by decide) (by bv_omega)
  -- the frame (`sp' = sp - 0x110`): locals [0, 0x98), the `ArrayVisitor` result [0x98, 0xc0),
  -- saved registers [0xc0, 0x110)
  have hokL : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 19 := hokS.sub' 98 19 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x78#64) 5 := hokS.sub' 117 5 (by decide) (by bv_omega)
  have hokV : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hokS.sub' 122 10 (by decide) (by bv_omega)
  obtain ⟨FL, hFL, hFLl⟩ := Region.exists_junk (sp - 0x110#64) 19 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x78#64) 5 s
  obtain ⟨FV, hFV, hFVl⟩ := Region.exists_junk (sp - 0x50#64) 10 s
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  have hmS : sp &&& 7#64 = 0#64 := by
    have ha := hstk.aligned
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    simp only [BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  -- how many of the four fields the reader holds
  rcases (by omega : l.toNat < 32 ∨ (32 ≤ l.toNat ∧ l.toNat < 64) ∨ (64 ≤ l.toNat ∧ l.toNat < 96) ∨
      (96 ≤ l.toNat ∧ l.toNat < 128) ∨ 128 ≤ l.toNat) with hl | ⟨hl, hl'⟩ | ⟨hl, hl'⟩ | ⟨hl, hl'⟩ | hl
  all_goals sym_exec [array32_r0_ok_spec, array32_r0_err_spec, hio]
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v25_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!] := by
      rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post19_0 :: O.drop 2) s_38 := by
      rw [hd, v25_def]; exact hR0
    clear hR0
    have hlt : l.toNat < 128 := by omega
    sym_close (hkE _ post19_0 post19_1 post19_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v76_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!] := by
      rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post70_0 :: O.drop 2) s_89 := by
      rw [hd, v76_def]; exact hR0
    clear hR0
    have hlt : l.toNat < 128 := by omega
    sym_close (hkE _ post70_0 post70_1 post70_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v127_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!] := by
      rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post121_0 :: O.drop 2) s_140 := by
      rw [hd, v127_def]; exact hR0
    clear hR0
    have hlt : l.toNat < 128 := by omega
    sym_close (hkE _ post121_0 post121_1 post121_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v178_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!] := by
      rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post172_0 :: O.drop 2) s_191 := by
      rw [hd, v178_def]; exact hR0
    clear hR0
    have hlt : l.toNat < 128 := by omega
    sym_close (hkE _ post172_0 post172_1 post172_2)
  · have hq4 : q + 32#64 + 32#64 + 32#64 + 32#64 = q + 128#64 := by bv_omega
    have hl4 : l - 32#64 - 32#64 - 32#64 - 32#64 = l - 128#64 := by bv_omega
    rw [hq4, hl4] at hR1
    have e : [v429, v390, v38, v39, v391, v406, v91, v92, v407, v422, v140, v141, v423, v427, v193, v194, v205] = instW O (W0 ++ W1 ++ W2 ++ W3) := by
      subst v429_def v427_def v426_def v425_def v424_def v423_def v422_def v421_def v420_def v419_def v418_def v417_def v416_def v415_def v414_def v413_def v412_def v411_def v410_def v409_def v408_def v407_def v406_def v405_def v404_def v403_def v402_def v401_def v400_def v399_def v398_def v397_def v396_def v395_def v394_def v393_def v392_def v391_def v390_def v389_def v388_def v387_def v386_def v385_def v384_def v383_def v382_def v381_def v380_def v379_def v378_def v377_def v376_def v375_def v374_def v373_def v372_def v371_def v370_def v369_def v368_def v367_def v366_def v365_def v364_def v361_def v360_def v330_def v329_def v328_def v327_def v326_def v325_def v324_def v323_def v322_def v321_def v320_def v319_def v317_def v316_def v286_def v285_def v284_def v283_def v282_def v281_def v280_def v279_def v278_def v277_def v276_def v275_def v273_def v272_def v242_def v241_def v240_def v239_def v238_def v237_def v236_def v235_def v234_def v233_def v232_def v231_def v230_def v229_def v228_def v227_def v226_def v225_def v224_def v223_def v221_def v220_def v219_def v218_def v217_def v216_def v215_def v214_def v213_def v212_def v211_def v210_def v209_def v208_def v206_def v205_def v202_def v201_def v197_def v196_def v195_def v194_def v193_def v190_def v189_def v188_def v187_def v186_def v185_def v184_def v183_def v182_def v181_def v180_def v179_def v178_def v177_def v176_def v175_def acc172_0_def v164_def v163_def v162_def v161_def v159_def v158_def v157_def v156_def v155_def v154_def v153_def v152_def v151_def v150_def v148_def v142_def v141_def v140_def v139_def v138_def v137_def v136_def v135_def v134_def v133_def v132_def v131_def v130_def v129_def v128_def v127_def v126_def v125_def v124_def acc121_0_def v113_def v112_def v111_def v110_def v109_def v108_def v107_def v106_def v105_def v104_def v103_def v102_def v101_def v100_def v98_def v93_def v92_def v91_def v88_def v87_def v86_def v85_def v84_def v83_def v82_def v81_def v80_def v79_def v78_def v77_def v76_def v75_def v74_def v73_def acc70_0_def v62_def v61_def v60_def v59_def v57_def v56_def v55_def v54_def v53_def v52_def v51_def v50_def v49_def v48_def v46_def v40_def v39_def v38_def v37_def v36_def v35_def v34_def v33_def v32_def v31_def v30_def v29_def v28_def v27_def v26_def v25_def v24_def v23_def v22_def acc19_0_def
      simp only [instW, show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals
        apply word_ext
        intro k hk
        interval_cases k <;> simp (disch := decide) only [word8, arr32W, instByte, inByte, extractByte_replaceByte,
          extractByte_replaceByte_ne, extractByte_or, extractByte_zext8,
          extractByte_zext8_shl8, extractByte_zext8_shl16, extractByte_zext8_shl24,
          extractByte_zext_trunc32, extractByte_zext_trunc16, trunc8_eq_extractByte, extractByte_zero,
          extractByte_shr8, extractByte_shr16, extractByte_shr24, extractByte_shr32, extractByte_shr40,
          extractByte_shr48, extractByte_shr56, get4 W0 W1 W2 W3 hW0l hW1l hW2l hW3l,
          List.getElem!_cons_zero, List.getElem!_cons_succ, BitVec.zero_or, BitVec.or_zero,
          ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod,
          Nat.reduceEqDiff, Nat.reduceLT]
    rw [e] at hR0
    sym_close hk

end Cases.Zip2005
