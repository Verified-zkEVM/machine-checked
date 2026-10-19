import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Image.F_78025a1c
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `EpAffine::from_bytes`

Two executor runs: to the `sqrt` call, then to the return; the boolean-word and limb
facts (`Cases.Zip2005.FromBytesKit`) are derived between and after them.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `EpAffine::from_bytes` (`0x78025a1c`): see `FromBytesPost`. The `FP_TABLES` must be
    initialised (`Once` state `2`), as for `sqrt_alt`. -/
theorem ep_affine_from_bytes_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 9) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hpc : s.pc = 0x78025a1c#64) (hcode : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x6f0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.textLo Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x6f0#64) 222 a0 9) (hd_a1 : Disjoint (sp - 0x6f0#64) 222 a1 4)
    (hd_tb : Disjoint (sp - 0x6f0#64) 222 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x6f0#64) 222 iptr 138)
    (hd_g0 : Disjoint (sp - 0x6f0#64) 222 g0 1024) (hd_g1 : Disjoint (sp - 0x6f0#64) 222 g1 1024)
    (hd_g2 : Disjoint (sp - 0x6f0#64) 222 g2 1024) (hd_g3 : Disjoint (sp - 0x6f0#64) 222 g3 516)
    (he_a1 : Disjoint a0 9 a1 4) (he_tb : Disjoint a0 9 0x780488a8#64 10)
    (he_iptr : Disjoint a0 9 iptr 138)
    (he_g0 : Disjoint a0 9 g0 1024) (he_g1 : Disjoint a0 9 g1 1024)
    (he_g2 : Disjoint a0 9 g2 1024) (he_g3 : Disjoint a0 9 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 : Word) (f : BitVec 8),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x6f0#64, 222), (a0, 9)] s t →
      Region a0 [x0, x1, x2, x3, y0, y1, y2, y3, replaceByte O[8]! 0 f] t →
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f →
      SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6f0#64) 222 := hstk.frame 222 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 38 := hokW.sub' 184 38 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 25 := hokF.sub' 0 25 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 25 13 (by decide) (by bv_omega)
  have hok_tb : RegionOk Ro.layout.roBase Ro.layout.textHi 0x780488a8#64 10 := ⟨by decide, by decide, Or.inr (by decide)⟩
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0x130#64) 25 s
  obtain ⟨S, hS, hSl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x6f0#64, 222), (a0, 9)] s
  -- run 1: up to the `sqrt` call
  sym_exec [uint256_mulmod_spec, fp_from_raw_spec, black_box_spec, hpb, hpp, hprz] stop [0x78026050]
  -- the encoding's words, reassembled from bytes
  have hb0 : v40 = b0 := by
    rw [← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v34_def, ← v33_def,
      ← v32_def, ← v31_def, ← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def,
      ← v24_def, ← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def]
    exact bytes_word b0
  have hb1 : v62 = b1 := by
    rw [← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def, ← v56_def, ← v55_def,
      ← v54_def, ← v53_def, ← v52_def, ← v51_def, ← v50_def, ← v49_def, ← v48_def, ← v47_def,
      ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def]
    exact bytes_word b1
  have hb2 : v84 = b2 := by
    rw [← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def,
      ← v76_def, ← v75_def, ← v74_def, ← v73_def, ← v72_def, ← v71_def, ← v70_def, ← v69_def,
      ← v68_def, ← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def]
    exact bytes_word b2
  have hb3 : v108 = b3 := by
    rw [← v108_def, ← v107_def, ← v106_def, ← v105_def, ← v104_def, ← v103_def, ← v100_def,
      ← v99_def, ← v98_def, ← v97_def, ← v96_def, ← v95_def, ← v94_def, ← v93_def, ← v92_def,
      ← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def]
    exact bytes_word b3
  have hhi : v106 = b3 >>> 32 := by
    rw [← v106_def, ← v105_def, ← v104_def, ← v103_def, ← v100_def, ← v99_def, ← v98_def, ← v97_def,
      ← v96_def, ← v95_def]
    exact bytes_word_hi b3
  have hx3 : v116 = b3 &&& 0x7fffffffffffffff#64 := by rw [← v116_def, ← v115_def, hb3, shl1_shr1]
  have hys : bw b3.msb = v113 := by rw [← v113_def, ← v109_def, hhi, sign_word, bb_bw]
  obtain ⟨X, hX⟩ : ∃ X, leLimbsToNat [b0, b1, b2, b3 &&& 0x7fffffffffffffff#64] = X := ⟨_, rfl⟩
  -- the canonical check (`from_repr`, inlined)
  have hXe : X = b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat +
      2 ^ 192 * (b3 &&& 0x7fffffffffffffff#64).toNat := by
    rw [← hX]; simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have fl := lt_flag (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v123_def v128_def v129_def v130_def v132_def v133_def v135_def v136_def v137_def
    v138_def v139_def v140_def v141_def v142_def v146_def v147_def
  dsimp only at fl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide,
    hb0, hb1, hb2, hx3, ← hXe] at fl
  obtain ⟨canon, hcanon⟩ : ∃ c, decide (X < Fp.p) = c := ⟨_, rfl⟩
  have h201 : bw canon = v201 := by
    rw [← v201_def, ← hcanon]
    by_cases hc : X < Fp.p
    · rw [show v147 = 0#64 from BitVec.eq_of_toNat_eq (fl.1 hc), decide_eq_true hc]; rfl
    · rw [show v147 = 1#64 from BitVec.eq_of_toNat_eq (fl.2 (by omega)), decide_eq_false hc]; rfl
  have h205 : bw canon = v205 := by rw [← v205_def, ← h201, bb_bw]
  have h207 : -(bw canon) = v207 := by rw [← v207_def, ← v206_def, ← h201, bb_bw, and255_bw]
  have h208 : (if canon then v197 else 0#64) = v208 := by rw [← v208_def, ← h207, and_negbw]
  have h209 : (if canon then v198 else 0#64) = v209 := by rw [← v209_def, ← h207, and_negbw]
  have h210 : (if canon then v199 else 0#64) = v210 := by rw [← v210_def, ← h207, and_negbw]
  have h211 : (if canon then v200 else 0#64) = v211 := by rw [← v211_def, ← h207, and_negbw]
  -- `x` in Montgomery form, masked by the flag
  have hXm : acc196_0 = Fp.mul X Fp.R2 := by
    rw [mulpair acc177_0_def acc196_0_def, hb0, hb1, hb2, hx3, hX, Fp.limbs_R2]
  have hXc : leLimbsToNat [v197, v198, v199, v200] = acc196_0 := by
    rw [← v197_def, ← v198_def, ← v199_def, ← v200_def]; exact cells_lt (acc_ltp acc196_0_def)
  obtain ⟨xm, hxm_def⟩ : ∃ m, leLimbsToNat [v208, v209, v210, v211] = m := ⟨_, rfl⟩
  have hxm : (if canon then Fp.mul X Fp.R2 else 0) = xm := by
    rw [← hxm_def, ← h208, ← h209, ← h210, ← h211]
    cases canon
    · simp only [Bool.false_eq_true, if_false]; rfl
    · simp only [if_true]; rw [hXc, hXm]
  -- `x.is_zero()`
  obtain ⟨zero, hzero_def⟩ :
    ∃ z, (v211 == 0#64 && (v210 == 0#64 && (v209 == 0#64 && v208 == 0#64))) = z := ⟨_, rfl⟩
  have h246 : bw zero = v246 := by
    rw [← v246_def, ← v242_def, ← v241_def, ← v237_def, ← v236_def, ← v232_def, ← v231_def,
      ← v227_def, ← v226_def, ← v222_def, ← v221_def, ← v217_def, ← v216_def, ← v212_def,
      ← hzero_def]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw]
  have hzero : zero = true ↔ xm = 0 := by
    rw [← hzero_def, ← hxm_def, limbs_zero4]
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩, fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩⟩
  -- the identity case `x.is_zero() & !ysign`, and its negation
  have h247 : bw (!b3.msb) = v247 := by rw [← v247_def, ← v114_def, v113_def, ← hys, not1_bw]
  obtain ⟨ident, hident_def⟩ : ∃ i, (!b3.msb && zero) = i := ⟨_, rfl⟩
  have h256 : bw ident = v256 := by
    rw [← v256_def, ← v252_def, ← v251_def, ← h247, ← h246, bb_bw, and_bw, and255_bw, bb_bw, hident_def]
  have h262 : bw (!ident) = v262 := by
    rw [← v262_def, ← v258_def, ← v257_def, v256_def, ← h256, not1_bw, bb_bw]
  -- `x³ + 5`
  have hsq2 : acc302_0 = Fp.mul xm xm := by rw [mulpair acc281_0_def acc302_0_def, hxm_def]
  have hc302 : leLimbsToNat [v303, v304, v305, v306] = acc302_0 := by
    rw [← v303_def, ← v304_def, ← v305_def, ← v306_def]; exact cells_lt (acc_ltp acc302_0_def)
  have hcube : acc337_0 = Fp.mul (Fp.mul xm xm) xm := by
    rw [mulpair acc324_0_def acc337_0_def, hc302, hsq2, hxm_def]
  have h5 : acc351_0 = Fp.mul 5 Fp.R2 := by
    rw [← acc351_0_def, show leLimbsToNat [5#64, 0#64, 0#64, 0#64] = 5 by decide]
  have hA5 : leLimbsToNat [v352, v353, v354, v355] = acc351_0 := by
    rw [← v352_def, ← v353_def, ← v354_def, ← v355_def]
    exact cells_lt (by rw [← acc351_0_def]; exact Fp.mul_lt _ _)
  have hB3 : leLimbsToNat [v338, v339, v340, v341] = acc337_0 := by
    rw [← v338_def, ← v339_def, ← v340_def, ← v341_def]; exact cells_lt (acc_ltp acc337_0_def)
  have hU : leLimbsToNat [v395, v400, v403, v407] = Fp.rhs xm := by
    rw [fadd_chain v356_def v357_def v358_def v359_def v360_def v361_def v362_def v363_def v364_def
      v365_def v366_def v367_def v368_def v369_def v372_def v374_def v375_def v376_def v379_def
      v380_def v382_def v383_def v384_def v385_def v386_def v387_def v388_def v389_def v391_def
      v392_def v394_def v395_def v396_def v397_def v398_def v399_def v400_def v401_def v402_def
      v403_def v404_def v405_def v406_def v407_def
      (by rw [hA5, h5]; exact Fp.mul_lt _ _) (by rw [hB3]; exact acc_ltp acc337_0_def),
      hA5, hB3, h5, hcube]
    rfl
  have hUlt : leLimbsToNat [v395, v400, v403, v407] < Fp.p := by
    rw [hU]; exact Nat.mod_lt _ Fp.p_pos
  clear hb0 hb1 hb2 hb3 hhi hx3 fl hXe hXm hXc hsq2 hc302 hcube h5 hA5 hB3 h201 h207 h247 h246
  -- a second run from the call site: its own frame fact, the first run's kept aside
  have hU1 : ∀ u, Unchanged [(sp - 0x6f0#64, 222), (a0, 9)] s_416 u →
      Unchanged [(sp - 0x6f0#64, 222), (a0, 9)] s u := fun u h => hunch.trans h
  clear hunch
  have hu2 := Unchanged.refl [(sp - 0x6f0#64, 222), (a0, 9)] s_416
  have hpb' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s_416.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u :=
    fun u sp' L' h1 h2 => hpb u sp' L' h1 (h2.trans hcode)
  have hpp' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s_416.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u :=
    fun u sp' L' h1 h2 => hpp u sp' L' h1 (h2.trans hcode)
  have hprz' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s_416.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u :=
    fun u sp' L' h1 h2 => hprz u sp' L' h1 (h2.trans hcode)
  clear hpb hpp hprz
  have hcodeS : s_416.code = s.code := hcode
  have hro2 : RoImage Ro.layout s_416 := hro
  -- the callee's frame facts against the fixed table address, in the shape the spec states them
  have hd_tb' : Disjoint (sp + 18446744073709551312#64 - 1472#64) 184 0x780488a8#64 9 := by
    rw [MachineChecked.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  have he_tb' : Disjoint (sp + 18446744073709551448#64) 5 0x780488a8#64 9 := by
    rw [MachineChecked.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  -- run 2: from the `sqrt` call to the return
  sym_exec [uint256_mulmod_spec, sqrt_alt_spec, fp_to_repr_spec, black_box_spec, hpb', hpp', hprz']
  -- the square root `R` and its flag `sq`
  obtain ⟨R, hR_def⟩ : ∃ r, leLimbsToNat [post6_1, post6_2, post6_3, post6_4] = r := ⟨_, rfl⟩
  rw [hR_def] at post6_10 post6_11 post6_12
  rw [hU] at post6_11 post6_12
  obtain ⟨sq, hsq_def⟩ : ∃ b, decide (Fp.mul R R = Fp.rhs xm) = b := ⟨_, rfl⟩
  have hv7 : bw sq = v7 := by
    rw [← v7_def, extractByte_replaceByte _ 0 (by decide), hR_def, zext_if8, hsq_def]
  -- the `CtOption` value: `R` under the flag
  obtain ⟨Y, hY_def⟩ : ∃ y, leLimbsToNat [v13, v14, v15, v16] = y := ⟨_, rfl⟩
  have hY : Y = if sq then R else 0 := by
    rw [← hY_def, ← v13_def, ← v14_def, ← v15_def, ← v16_def, ← v12_def, ← hv7, and_negbw, and_negbw,
      and_negbw, and_negbw]
    cases sq
    · simp only [Bool.false_eq_true, if_false]; rfl
    · simp only [if_true]; exact hR_def
  have hYlt : Y < Fp.p := by
    rw [hY]; cases sq
    · simp only [Bool.false_eq_true, if_false]; exact Fp.p_pos
    · simp only [if_true]; exact post6_10
  -- `y.is_odd()`
  have hpar : bw (decide (Fp.fromMont Y % 2 = 1)) = v27 := by
    rw [← v27_def, ← v26_def, ← acc25_0_def, low_bit, hY_def]; rfl
  -- `-y`
  have hneg : leLimbsToNat [v52, v53, v54, v55] = Fp.sub 0 Y := by
    rw [← hY_def]
    exact fneg_chain v31_def v32_def v33_def v34_def v35_def v36_def v38_def v39_def v40_def rfl
      v41_def v42_def v43_def v44_def rfl v46_def v47_def v48_def v49_def v50_def v52_def v53_def
      v54_def v55_def (hY_def ▸ hYlt)
  -- `conditional_select(&y, &-y, ysign ^ sign)`
  obtain ⟨flip, hflip_def⟩ : ∃ f, (decide (Fp.fromMont Y % 2 = 1) != b3.msb) = f := ⟨_, rfl⟩
  have h63 : -(bw flip) = v63 := by
    rw [← v63_def, ← v62_def, ← v58_def, ← v57_def, ← hpar, bb_bw, ← hys, xor_bw, and255_bw, bb_bw,
      and255_bw, hflip_def]
  have hy0 : (if flip then v52 else v13) = v66 := by rw [← v66_def, ← v65_def, ← v64_def, ← h63, sel_bw]
  have hy1 : (if flip then v53 else v14) = v69 := by rw [← v69_def, ← v68_def, ← v67_def, ← h63, sel_bw]
  have hy2 : (if flip then v54 else v15) = v72 := by rw [← v72_def, ← v71_def, ← v70_def, ← h63, sel_bw]
  have hy3 : (if flip then v55 else v16) = v75 := by rw [← v75_def, ← v74_def, ← v73_def, ← h63, sel_bw]
  have hYf : leLimbsToNat [v66, v69, v72, v75] = if flip then Fp.sub 0 Y else Y := by
    rw [← hy0, ← hy1, ← hy2, ← hy3]
    cases flip
    · simp only [Bool.false_eq_true, if_false]; exact hY_def
    · simp only [if_true]; exact hneg
  -- the `CtOption` masks and the final flag
  have hv80 : bw sq = v80 := by rw [← v80_def, ← hv7, and1_bw]
  have hv86 : -(bw (!ident)) = v86 := by rw [← v86_def, ← v85_def, ← h262, and255_bw]
  have hx0 : (if !ident then v208 else 0#64) = v88 := by rw [← v88_def, ← hv86, and_negbw]
  have hx1 : (if !ident then v209 else 0#64) = v89 := by rw [← v89_def, ← hv86, and_negbw]
  have hx2 : (if !ident then v210 else 0#64) = v90 := by rw [← v90_def, ← hv86, and_negbw]
  have hx3 : (if !ident then v211 else 0#64) = v91 := by rw [← v91_def, ← hv86, and_negbw]
  have hy0' : (if !ident then v66 else 0#64) = v92 := by rw [← v92_def, ← hv86, and_negbw]
  have hy1' : (if !ident then v69 else 0#64) = v93 := by rw [← v93_def, ← hv86, and_negbw]
  have hy2' : (if !ident then v72 else 0#64) = v94 := by rw [← v94_def, ← hv86, and_negbw]
  have hy3' : (if !ident then v75 else 0#64) = v95 := by rw [← v95_def, ← hv86, and_negbw]
  have hv105 : -(bw (!ident)) = v105 := by rw [← v105_def, ← h262, sext_neg_bw]
  have hv109 : (if !ident then bw sq else bw ident) = v109 := by
    rw [← v109_def, ← v108_def, ← v107_def, ← hv80, bb_bw, ← h256, ← hv105, sel_bw]
  have hv112 : bw ((if !ident then sq else ident) && canon) = v112 := by
    rw [← v112_def, ← v111_def, ← hv109, ite_bw, ← h205, and_bw, and255_bw]
  rw [← hv112, bb_bw, bw_trunc8] at v116_def
  subst v116_def
  sym_close hk _ _ _ _ _ _ _ _ _ _
  all_goals first | exact hU1 _ hunch | exact hcode.trans hcodeS | skip
  -- the postcondition
  have hxout : leLimbsToNat [if !ident then v208 else 0#64, if !ident then v209 else 0#64,
      if !ident then v210 else 0#64, if !ident then v211 else 0#64] = if !ident then xm else 0 := by
    cases ident
    · simp only [Bool.not_false, if_true]; exact hxm_def
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]; rfl
  have hyout : leLimbsToNat [if !ident then v66 else 0#64, if !ident then v69 else 0#64,
      if !ident then v72 else 0#64, if !ident then v75 else 0#64] =
      if !ident then (if flip then Fp.sub 0 Y else Y) else 0 := by
    cases ident
    · simp only [Bool.not_false, if_true]; exact hYf
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]; rfl
  rw [← hx0, ← hx1, ← hx2, ← hx3, ← hy0', ← hy1', ← hy2', ← hy3', hxout, hyout]
  exact fb_post hX hcanon hxm hzero hident_def post6_10 hsq_def post6_12 hY hflip_def

end Cases.Zip2005
