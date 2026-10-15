/-
  Cases.Zip2005.Mul

  `pasta_curves::sp1_pallas::zkvm::mul(out, p, k)`: `[k] p` on `Ep` through the
  `PALLAS_ADD`/`PALLAS_DOUBLE` precompiles.

  The projective point is made affine (`to_affine`, unless `Z = R`), both
  coordinates are taken out of Montgomery form (`to_repr`), and the scalar's
  canonical bytes drive the loop of `Cases.Zip2005.ScalarMul` from the fixed offset `Q`.
  The offset is removed by adding `-Q`; a non-identity result is checked
  canonical (`x < p`, `y < p`, asserted) and put back into Montgomery form
  (`Fp.mul x R2`) with `Z = R`. The identity, on either side, is all zeros.
-/

import Cases.Zip2005.Curve.MulModel
import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Field.FqRepr
import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Image.F_7803a110
import Cases.Zip2005.Image.F_7803dd28
import Cases.Zip2005.Image.F_7803f57c
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym


set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem mul_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra a0 a1 a2 sp : Word) (pt k O : List Word)
    (hptl : pt.length = 12) (hkl : k.length = 4) (hOl : O.length = 12)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hpc : s.pc = 0x78031be8#64) (hcode : CodeAt F_78031be8.base F_78031be8.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeC : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeL : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x490 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (hp : Region a1 pt s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hk : Region a2 k s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x490#64) 146 a0 12) (hd1 : Disjoint (sp - 0x490#64) 146 a1 12)
    (hd2 : Disjoint (sp - 0x490#64) 146 a2 4)
    (hd01 : Disjoint a0 12 a1 12) (hd02 : Disjoint a0 12 a2 4)
    (hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x490#64, 146), (a0, 12)] s t → (mulW pt k).length = 12 →
      Region a0 (mulW pt k) t → mulFacts pt k → SafeN G n P t) :
    SafeN G n P s := by
  -- mul's frame, `sp0 = sp - 0x260`, in the blocks its callees write
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk (sp - 0x490#64) 70 s
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x260#64) 12 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x200#64) 8 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x1c0#64) 9 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0x178#64) 9 s
  obtain ⟨F4, hF4, hF4l⟩ := Region.exists_junk (sp - 0x130#64) 4 s
  obtain ⟨F5, hF5, hF5l⟩ := Region.exists_junk (sp - 0x110#64) 9 s
  obtain ⟨F6, hF6, hF6l⟩ := Region.exists_junk (sp - 0xc8#64) 8 s
  obtain ⟨F7, hF7, hF7l⟩ := Region.exists_junk (sp - 0x88#64) 4 s
  obtain ⟨F8, hF8, hF8l⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x490#64) 146 := hstk.frame 146 (by decide)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x490#64) 70 := hokA.sub' 0 70 (by decide) (by bv_omega)
  have hokF0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x260#64) 12 := hokA.sub' 70 12 (by decide) (by bv_omega)
  have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x200#64) 8 := hokA.sub' 82 8 (by decide) (by bv_omega)
  have hokF2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1c0#64) 9 := hokA.sub' 90 9 (by decide) (by bv_omega)
  have hokF3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x178#64) 9 := hokA.sub' 99 9 (by decide) (by bv_omega)
  have hokF4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 4 := hokA.sub' 108 4 (by decide) (by bv_omega)
  have hokF5 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 9 := hokA.sub' 112 9 (by decide) (by bv_omega)
  have hokF6 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xc8#64) 8 := hokA.sub' 121 8 (by decide) (by bv_omega)
  have hokF7 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x88#64) 4 := hokA.sub' 129 4 (by decide) (by bv_omega)
  have hokF8 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokA.sub' 133 13 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x490#64, 146), (a0, 12)] s
  have hstk0 : StackOk Ro.layout 0x230 (sp - 0x260#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0x260#64).toNat = sp.toNat - 0x260 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  have Lp := fun S g3 g4 g8 g24 g25 g26 g27 t acc base =>
    mul_loop (G := G) (n := n) (P := P) (L := L) (sp - 0x260#64) S s.code g3 g4 g8 g24 g25 g26 g27 hpanic 255 0 t acc base
      rfl (by decide)
  replace hk' := fun t h1 h2 h3 h4 => hk' t h1 h2 h3 h4 (length_mulW pt k)
  sym_exec [memset96_spec, black_box_spec, to_affine_spec, coordinates_spec, fp_to_repr_spec, fq_to_repr_spec,
    complete_add_assign_spec, uint256_mulmod_spec, hpanic, Lp]
  all_goals sym_close hk'
  · exact (mul_pathA pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v57_def := v57_def)
      (v58_def := v58_def) (v59_def := v59_def) (v60_def := v60_def) (v65_def := v65_def)
      (v66_def := v66_def) (v67_def := v67_def) (v68_def := v68_def) (v77_def := v77_def)
      (v78_def := v78_def) (v84_def := v84_def) (v85_def := v85_def) (v86_def := v86_def)
      (v90_def := v90_def) (v91_def := v91_def) (v95_def := v95_def) (v97_def := v97_def)
      (v101_def := v101_def) (v102_def := v102_def) (v106_def := v106_def) (v109_def :=
      v109_def) (v110_def := v110_def) (v114_def := v114_def) (v115_def := v115_def) (v119_def
      := v119_def) (hbr120 := hbr120) (acc141_0_def := acc141_0_def) (v142_def := v142_def)
      (v143_def := v143_def) (v144_def := v144_def) (v145_def := v145_def) (acc150_0_def :=
      acc150_0_def) (v151_def := v151_def) (v152_def := v152_def) (v153_def := v153_def)
      (v154_def := v154_def) (acc223_0_def := acc223_0_def) (post226_12 := post226_12)
      (post226_15 := post226_15) (acc226_1_def := acc226_1_def) (acc248_0_def := acc248_0_def)
      (v249_def := v249_def) (hbr250 := hbr250) (acc256_0_def := acc256_0_def)).1
  · exact (mul_pathA pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v57_def := v57_def)
      (v58_def := v58_def) (v59_def := v59_def) (v60_def := v60_def) (v65_def := v65_def)
      (v66_def := v66_def) (v67_def := v67_def) (v68_def := v68_def) (v77_def := v77_def)
      (v78_def := v78_def) (v84_def := v84_def) (v85_def := v85_def) (v86_def := v86_def)
      (v90_def := v90_def) (v91_def := v91_def) (v95_def := v95_def) (v97_def := v97_def)
      (v101_def := v101_def) (v102_def := v102_def) (v106_def := v106_def) (v109_def :=
      v109_def) (v110_def := v110_def) (v114_def := v114_def) (v115_def := v115_def) (v119_def
      := v119_def) (hbr120 := hbr120) (acc141_0_def := acc141_0_def) (v142_def := v142_def)
      (v143_def := v143_def) (v144_def := v144_def) (v145_def := v145_def) (acc150_0_def :=
      acc150_0_def) (v151_def := v151_def) (v152_def := v152_def) (v153_def := v153_def)
      (v154_def := v154_def) (acc223_0_def := acc223_0_def) (post226_12 := post226_12)
      (post226_15 := post226_15) (acc226_1_def := acc226_1_def) (acc248_0_def := acc248_0_def)
      (v249_def := v249_def) (hbr250 := hbr250) (acc256_0_def := acc256_0_def)).2
  · exact (mul_pathB pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v57_def := v57_def)
      (v58_def := v58_def) (v59_def := v59_def) (v60_def := v60_def) (v65_def := v65_def)
      (v66_def := v66_def) (v67_def := v67_def) (v68_def := v68_def) (v77_def := v77_def)
      (v78_def := v78_def) (v84_def := v84_def) (v85_def := v85_def) (v86_def := v86_def)
      (v90_def := v90_def) (v91_def := v91_def) (v95_def := v95_def) (v97_def := v97_def)
      (v101_def := v101_def) (v102_def := v102_def) (v106_def := v106_def) (v109_def :=
      v109_def) (v110_def := v110_def) (v114_def := v114_def) (v115_def := v115_def) (v119_def
      := v119_def) (hbr120 := hbr120) (acc141_0_def := acc141_0_def) (v142_def := v142_def)
      (v143_def := v143_def) (v144_def := v144_def) (v145_def := v145_def) (acc150_0_def :=
      acc150_0_def) (v151_def := v151_def) (v152_def := v152_def) (v153_def := v153_def)
      (v154_def := v154_def) (acc223_0_def := acc223_0_def) (post226_12 := post226_12)
      (post226_15 := post226_15) (acc226_1_def := acc226_1_def) (acc248_0_def := acc248_0_def)
      (v249_def := v249_def) (hbr250 := hbr250) (v263_def := v263_def) (hbr264 := hbr264)
      (v268_def := v268_def) (v269_def := v269_def) (v270_def := v270_def) (v271_def :=
      v271_def) (v274_def := v274_def) (v276_def := v276_def) (v277_def := v277_def) (v278_def
      := v278_def) (v281_def := v281_def) (v282_def := v282_def) (v284_def := v284_def)
      (v285_def := v285_def) (v286_def := v286_def) (v287_def := v287_def) (v288_def :=
      v288_def) (v289_def := v289_def) (v290_def := v290_def) (v291_def := v291_def) (v294_def
      := v294_def) (v295_def := v295_def) (acc329_0_def := acc329_0_def) (acc348_0_def :=
      acc348_0_def) (v349_def := v349_def) (v351_def := v351_def) (v353_def := v353_def)
      (v355_def := v355_def) (v358_def := v358_def) (v362_def := v362_def) (hbr364 := hbr364)
      (v365_def := v365_def) (v366_def := v366_def) (v367_def := v367_def) (v368_def :=
      v368_def) (v371_def := v371_def) (v374_def := v374_def) (v377_def := v377_def) (v379_def
      := v379_def) (v380_def := v380_def) (v381_def := v381_def) (v382_def := v382_def)
      (v383_def := v383_def) (v384_def := v384_def) (v385_def := v385_def) (v386_def :=
      v386_def) (v387_def := v387_def) (v390_def := v390_def) (v392_def := v392_def) (v393_def
      := v393_def) (v394_def := v394_def) (v395_def := v395_def) (acc415_0_def := acc415_0_def)
      (acc428_0_def := acc428_0_def) (v429_def := v429_def) (v430_def := v430_def) (v431_def :=
      v431_def) (v432_def := v432_def) (v433_def := v433_def) (v437_def := v437_def) (hbr440 :=
      hbr440)).1
  · exact (mul_pathB pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v57_def := v57_def)
      (v58_def := v58_def) (v59_def := v59_def) (v60_def := v60_def) (v65_def := v65_def)
      (v66_def := v66_def) (v67_def := v67_def) (v68_def := v68_def) (v77_def := v77_def)
      (v78_def := v78_def) (v84_def := v84_def) (v85_def := v85_def) (v86_def := v86_def)
      (v90_def := v90_def) (v91_def := v91_def) (v95_def := v95_def) (v97_def := v97_def)
      (v101_def := v101_def) (v102_def := v102_def) (v106_def := v106_def) (v109_def :=
      v109_def) (v110_def := v110_def) (v114_def := v114_def) (v115_def := v115_def) (v119_def
      := v119_def) (hbr120 := hbr120) (acc141_0_def := acc141_0_def) (v142_def := v142_def)
      (v143_def := v143_def) (v144_def := v144_def) (v145_def := v145_def) (acc150_0_def :=
      acc150_0_def) (v151_def := v151_def) (v152_def := v152_def) (v153_def := v153_def)
      (v154_def := v154_def) (acc223_0_def := acc223_0_def) (post226_12 := post226_12)
      (post226_15 := post226_15) (acc226_1_def := acc226_1_def) (acc248_0_def := acc248_0_def)
      (v249_def := v249_def) (hbr250 := hbr250) (v263_def := v263_def) (hbr264 := hbr264)
      (v268_def := v268_def) (v269_def := v269_def) (v270_def := v270_def) (v271_def :=
      v271_def) (v274_def := v274_def) (v276_def := v276_def) (v277_def := v277_def) (v278_def
      := v278_def) (v281_def := v281_def) (v282_def := v282_def) (v284_def := v284_def)
      (v285_def := v285_def) (v286_def := v286_def) (v287_def := v287_def) (v288_def :=
      v288_def) (v289_def := v289_def) (v290_def := v290_def) (v291_def := v291_def) (v294_def
      := v294_def) (v295_def := v295_def) (acc329_0_def := acc329_0_def) (acc348_0_def :=
      acc348_0_def) (v349_def := v349_def) (v351_def := v351_def) (v353_def := v353_def)
      (v355_def := v355_def) (v358_def := v358_def) (v362_def := v362_def) (hbr364 := hbr364)
      (v365_def := v365_def) (v366_def := v366_def) (v367_def := v367_def) (v368_def :=
      v368_def) (v371_def := v371_def) (v374_def := v374_def) (v377_def := v377_def) (v379_def
      := v379_def) (v380_def := v380_def) (v381_def := v381_def) (v382_def := v382_def)
      (v383_def := v383_def) (v384_def := v384_def) (v385_def := v385_def) (v386_def :=
      v386_def) (v387_def := v387_def) (v390_def := v390_def) (v392_def := v392_def) (v393_def
      := v393_def) (v394_def := v394_def) (v395_def := v395_def) (acc415_0_def := acc415_0_def)
      (acc428_0_def := acc428_0_def) (v429_def := v429_def) (v430_def := v430_def) (v431_def :=
      v431_def) (v432_def := v432_def) (v433_def := v433_def) (v437_def := v437_def) (hbr440 :=
      hbr440)).2
  · exact (mul_pathC pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v135_def := v135_def)
      (v136_def := v136_def) (v137_def := v137_def) (v138_def := v138_def) (v143_def :=
      v143_def) (v144_def := v144_def) (v145_def := v145_def) (v146_def := v146_def)
      (acc171_0_def := acc171_0_def) (v172_def := v172_def) (v173_def := v173_def) (v174_def :=
      v174_def) (v175_def := v175_def) (acc180_0_def := acc180_0_def) (v181_def := v181_def)
      (v182_def := v182_def) (v183_def := v183_def) (v184_def := v184_def) (acc253_0_def :=
      acc253_0_def) (post256_12 := post256_12) (post256_15 := post256_15) (acc256_1_def :=
      acc256_1_def) (acc278_0_def := acc278_0_def) (v279_def := v279_def) (hbr280 := hbr280)
      (acc286_0_def := acc286_0_def)).1
  · exact (mul_pathC pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v135_def := v135_def)
      (v136_def := v136_def) (v137_def := v137_def) (v138_def := v138_def) (v143_def :=
      v143_def) (v144_def := v144_def) (v145_def := v145_def) (v146_def := v146_def)
      (acc171_0_def := acc171_0_def) (v172_def := v172_def) (v173_def := v173_def) (v174_def :=
      v174_def) (v175_def := v175_def) (acc180_0_def := acc180_0_def) (v181_def := v181_def)
      (v182_def := v182_def) (v183_def := v183_def) (v184_def := v184_def) (acc253_0_def :=
      acc253_0_def) (post256_12 := post256_12) (post256_15 := post256_15) (acc256_1_def :=
      acc256_1_def) (acc278_0_def := acc278_0_def) (v279_def := v279_def) (hbr280 := hbr280)
      (acc286_0_def := acc286_0_def)).2
  · exact (mul_pathD pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v135_def := v135_def)
      (v136_def := v136_def) (v137_def := v137_def) (v138_def := v138_def) (v143_def :=
      v143_def) (v144_def := v144_def) (v145_def := v145_def) (v146_def := v146_def)
      (acc171_0_def := acc171_0_def) (v172_def := v172_def) (v173_def := v173_def) (v174_def :=
      v174_def) (v175_def := v175_def) (acc180_0_def := acc180_0_def) (v181_def := v181_def)
      (v182_def := v182_def) (v183_def := v183_def) (v184_def := v184_def) (acc253_0_def :=
      acc253_0_def) (post256_12 := post256_12) (post256_15 := post256_15) (acc256_1_def :=
      acc256_1_def) (acc278_0_def := acc278_0_def) (v279_def := v279_def) (hbr280 := hbr280)
      (v293_def := v293_def) (hbr294 := hbr294) (v298_def := v298_def) (v299_def := v299_def)
      (v300_def := v300_def) (v301_def := v301_def) (v304_def := v304_def) (v306_def :=
      v306_def) (v307_def := v307_def) (v308_def := v308_def) (v311_def := v311_def) (v312_def
      := v312_def) (v314_def := v314_def) (v315_def := v315_def) (v316_def := v316_def)
      (v317_def := v317_def) (v318_def := v318_def) (v319_def := v319_def) (v320_def :=
      v320_def) (v321_def := v321_def) (v324_def := v324_def) (v325_def := v325_def)
      (acc359_0_def := acc359_0_def) (acc378_0_def := acc378_0_def) (v379_def := v379_def)
      (v381_def := v381_def) (v383_def := v383_def) (v385_def := v385_def) (v388_def :=
      v388_def) (v392_def := v392_def) (hbr394 := hbr394) (v395_def := v395_def) (v396_def :=
      v396_def) (v397_def := v397_def) (v398_def := v398_def) (v401_def := v401_def) (v404_def
      := v404_def) (v407_def := v407_def) (v409_def := v409_def) (v410_def := v410_def)
      (v411_def := v411_def) (v412_def := v412_def) (v413_def := v413_def) (v414_def :=
      v414_def) (v415_def := v415_def) (v416_def := v416_def) (v417_def := v417_def) (v420_def
      := v420_def) (v422_def := v422_def) (v423_def := v423_def) (v424_def := v424_def)
      (v425_def := v425_def) (acc445_0_def := acc445_0_def) (acc458_0_def := acc458_0_def)
      (v459_def := v459_def) (v460_def := v460_def) (v461_def := v461_def) (v462_def :=
      v462_def) (v463_def := v463_def) (v467_def := v467_def) (hbr470 := hbr470)).1
  · exact (mul_pathD pt k hkl (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (v135_def := v135_def)
      (v136_def := v136_def) (v137_def := v137_def) (v138_def := v138_def) (v143_def :=
      v143_def) (v144_def := v144_def) (v145_def := v145_def) (v146_def := v146_def)
      (acc171_0_def := acc171_0_def) (v172_def := v172_def) (v173_def := v173_def) (v174_def :=
      v174_def) (v175_def := v175_def) (acc180_0_def := acc180_0_def) (v181_def := v181_def)
      (v182_def := v182_def) (v183_def := v183_def) (v184_def := v184_def) (acc253_0_def :=
      acc253_0_def) (post256_12 := post256_12) (post256_15 := post256_15) (acc256_1_def :=
      acc256_1_def) (acc278_0_def := acc278_0_def) (v279_def := v279_def) (hbr280 := hbr280)
      (v293_def := v293_def) (hbr294 := hbr294) (v298_def := v298_def) (v299_def := v299_def)
      (v300_def := v300_def) (v301_def := v301_def) (v304_def := v304_def) (v306_def :=
      v306_def) (v307_def := v307_def) (v308_def := v308_def) (v311_def := v311_def) (v312_def
      := v312_def) (v314_def := v314_def) (v315_def := v315_def) (v316_def := v316_def)
      (v317_def := v317_def) (v318_def := v318_def) (v319_def := v319_def) (v320_def :=
      v320_def) (v321_def := v321_def) (v324_def := v324_def) (v325_def := v325_def)
      (acc359_0_def := acc359_0_def) (acc378_0_def := acc378_0_def) (v379_def := v379_def)
      (v381_def := v381_def) (v383_def := v383_def) (v385_def := v385_def) (v388_def :=
      v388_def) (v392_def := v392_def) (hbr394 := hbr394) (v395_def := v395_def) (v396_def :=
      v396_def) (v397_def := v397_def) (v398_def := v398_def) (v401_def := v401_def) (v404_def
      := v404_def) (v407_def := v407_def) (v409_def := v409_def) (v410_def := v410_def)
      (v411_def := v411_def) (v412_def := v412_def) (v413_def := v413_def) (v414_def :=
      v414_def) (v415_def := v415_def) (v416_def := v416_def) (v417_def := v417_def) (v420_def
      := v420_def) (v422_def := v422_def) (v423_def := v423_def) (v424_def := v424_def)
      (v425_def := v425_def) (acc445_0_def := acc445_0_def) (acc458_0_def := acc458_0_def)
      (v459_def := v459_def) (v460_def := v460_def) (v461_def := v461_def) (v462_def :=
      v462_def) (v463_def := v463_def) (v467_def := v467_def) (hbr470 := hbr470)).2
  · exact (mul_pathE pt k (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (acc62_0_def :=
      acc62_0_def)).1
  · exact (mul_pathE pt k (v15_def := v15_def) (v18_def := v18_def) (v22_def := v22_def) (v23_def :=
      v23_def) (v24_def := v24_def) (v28_def := v28_def) (v29_def := v29_def) (v33_def :=
      v33_def) (v34_def := v34_def) (v35_def := v35_def) (v39_def := v39_def) (v40_def :=
      v40_def) (v44_def := v44_def) (v45_def := v45_def) (v46_def := v46_def) (v50_def :=
      v50_def) (v51_def := v51_def) (v55_def := v55_def) (hbr56 := hbr56) (acc62_0_def :=
      acc62_0_def)).2

end Cases.Zip2005
