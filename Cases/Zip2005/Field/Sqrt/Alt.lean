import Cases.Zip2005.Field.Sqrt.Common
import Cases.Zip2005.Field.Pow
import Cases.Zip2005.Runtime.BlackBox
import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Field.FpSub
import Cases.Zip2005.Image.F_780315c0
import Cases.Zip2005.Image.Ro

/-! `SqrtTables::<Fp>::sqrt_alt(&self, u)`: `v = u^((t-1)/2)`, `res = sqrt_common(u·v, v)`,
then the self-check `res² = u` (is_square) / `res² = ROOT·u` (is_nonsquare) with
`assert!(u == 0 | is_square ^ is_nonsquare)`, returning `CtOption { is_square, res }`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem xor_bw (a b : Bool) : bw a ^^^ bw b = bw (a != b) := by cases a <;> cases b <;> decide
theorem or_bw (a b : Bool) : bw a ||| bw b = bw (a || b) := by cases a <;> cases b <;> decide
theorem bw_trunc8 (b : Bool) : BitVec.truncate 8 (bw b) = if b then 1#8 else 0#8 := by
  cases b <;> decide
theorem bw_ne_zero (b : Bool) : (¬(bw b == 0#64) = true) ↔ b = true := by cases b <;> simp [bw]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `sqrt_alt`: the result `r` is canonical, the flag is `r² = u`, and (the assertion having
    passed) `u = 0` or exactly one of `r² = u`, `r² = ROOT·u` holds. Requires `u` canonical
    (`ct_eq` compares Montgomery limbs) and the tables initialised (`tb`'s regions). -/
theorem sqrt_alt_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 tb a2 : Word)
    (u0 u1 u2 u3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 5) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G n P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN G n P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x780315c0#64) (hcode : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x5c0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = tb) (ha2 : s.getReg .x12 = a2)
    (hU : Region a2 [u0, u1, u2, u3] s) (hok_a2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4)
    (hUlt : leLimbsToNat [u0, u1, u2, u3] < Fp.p)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hT : Region tb [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx] s) (hok_tb : RegionOk Ro.layout.roBase Ro.layout.textHi tb 9)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x5c0#64) 184 a0 5) (hd_a2 : Disjoint (sp - 0x5c0#64) 184 a2 4)
    (hd_tb : Disjoint (sp - 0x5c0#64) 184 tb 9) (hd_iptr : Disjoint (sp - 0x5c0#64) 184 iptr 138)
    (hd_g0 : Disjoint (sp - 0x5c0#64) 184 g0 1024) (hd_g1 : Disjoint (sp - 0x5c0#64) 184 g1 1024)
    (hd_g2 : Disjoint (sp - 0x5c0#64) 184 g2 1024) (hd_g3 : Disjoint (sp - 0x5c0#64) 184 g3 516)
    (he_a2 : Disjoint a0 5 a2 4) (he_tb : Disjoint a0 5 tb 9) (he_iptr : Disjoint a0 5 iptr 138)
    (he_g0 : Disjoint a0 5 g0 1024) (he_g1 : Disjoint a0 5 g1 1024)
    (he_g2 : Disjoint a0 5 g2 1024) (he_g3 : Disjoint a0 5 g3 516)
    (hk : ∀ (t : MachineState) (f : BitVec 8) (r0 r1 r2 r3 : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x5c0#64, 184), (a0, 5)] s t →
      Region a0 [replaceByte O[0]! 0 f, r0, r1, r2, r3] t →
      leLimbsToNat [r0, r1, r2, r3] < Fp.p →
      f = (if Fp.mul (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [r0, r1, r2, r3]) =
          leLimbsToNat [u0, u1, u2, u3] then 1#8 else 0#8) →
      (leLimbsToNat [u0, u1, u2, u3] = 0 ∨
        (Fp.mul (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [r0, r1, r2, r3]) =
            leLimbsToNat [u0, u1, u2, u3] ↔
          ¬ Fp.mul (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [r0, r1, r2, r3]) =
            Fp.mul Fp.rootOfUnity (leLimbsToNat [u0, u1, u2, u3]))) →
      SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x5c0#64) 184 := hstk.frame 184 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x170#64) 46 := hokW.sub' 138 46 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x170#64) 33 := hokF.sub' 0 33 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 33 13 (by decide) (by bv_omega)
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0x170#64) 33 s
  obtain ⟨S, hS, hSl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x5c0#64, 184), (a0, 5)] s
  sym_exec [uint256_mulmod_spec, pow_by_t_minus1_over2_spec, sqrt_common_spec, black_box_spec,
    hpb, hpp, hprz]
  -- the two products: `res²` and `ROOT·u`
  have hSQ : acc128_0 = Fp.mul (leLimbsToNat [post94_0, post94_1, post94_2, post94_3])
      (leLimbsToNat [post94_0, post94_1, post94_2, post94_3]) := mulpair acc115_0_def acc128_0_def
  have hRU : acc261_0 = Fp.mul Fp.rootOfUnity (leLimbsToNat [u0, u1, u2, u3]) :=
    (mulpair acc244_0_def acc261_0_def).trans (congrArg₂ Fp.mul Fp.limbs_root rfl)
  have hsq : leLimbsToNat [v129, v130, v131, v132] = acc128_0 := by
    rw [← v129_def, ← v130_def, ← v131_def, ← v132_def]; exact cells_lt (acc_ltp acc128_0_def)
  have hru : leLimbsToNat [v262, v263, v264, v265] = acc261_0 := by
    rw [← v262_def, ← v263_def, ← v264_def, ← v265_def]; exact cells_lt (acc_ltp acc261_0_def)
  -- the two `Fp::sub` chains
  have c1 := fsub_chain v139_def v140_def v143_def v144_def v145_def v146_def v147_def v148_def
    v151_def v152_def v153_def v154_def v155_def v156_def v157_def v160_def v161_def v162_def
    v163_def v164_def v165_def v166_def v167_def v168_def v169_def v170_def v171_def v172_def
    v173_def v174_def v175_def v176_def v177_def v178_def v179_def v180_def
    (by rw [hsq]; exact acc_ltp acc128_0_def) hUlt
  have c2 := fsub_chain v266_def v267_def v268_def v269_def v270_def v271_def v272_def v273_def
    v274_def v275_def v276_def v277_def v278_def v279_def v280_def v281_def v282_def v283_def
    v284_def v285_def v286_def v287_def v288_def v289_def v290_def v291_def v292_def v293_def
    v294_def v295_def v296_def v297_def v298_def v299_def v300_def v301_def
    (by rw [hsq]; exact acc_ltp acc128_0_def) (by rw [hru]; exact acc_ltp acc261_0_def)
  rw [hsq, hSQ] at c1 c2
  rw [hru, hRU] at c2
  have z1 : (v180 = 0#64 ∧ v176 = 0#64 ∧ v173 = 0#64 ∧ v168 = 0#64) ↔
      Fp.mul (leLimbsToNat [post94_0, post94_1, post94_2, post94_3])
        (leLimbsToNat [post94_0, post94_1, post94_2, post94_3]) = leLimbsToNat [u0, u1, u2, u3] := by
    rw [← Fp.sub_eq_zero_iff (Fp.mul_lt _ _) hUlt, ← c1, limbs_zero4]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩, fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩⟩
  have z2 : (v301 = 0#64 ∧ v297 = 0#64 ∧ v294 = 0#64 ∧ v289 = 0#64) ↔
      Fp.mul (leLimbsToNat [post94_0, post94_1, post94_2, post94_3])
        (leLimbsToNat [post94_0, post94_1, post94_2, post94_3]) =
        Fp.mul Fp.rootOfUnity (leLimbsToNat [u0, u1, u2, u3]) := by
    rw [← Fp.sub_eq_zero_iff (Fp.mul_lt _ _) (Fp.mul_lt _ _), ← c2, limbs_zero4]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩, fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩⟩
  have z0 : (u3 = 0#64 ∧ u2 = 0#64 ∧ u1 = 0#64 ∧ u0 = 0#64) ↔ leLimbsToNat [u0, u1, u2, u3] = 0 := by
    rw [limbs_zero4]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩, fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩⟩
  -- the `ct_eq` folds through `black_box`, as booleans
  subst v181_def v185_def v186_def v190_def v191_def v195_def v196_def v200_def v201_def v205_def
    v206_def v210_def v211_def v215_def
  subst v302_def v306_def v307_def v311_def v312_def v316_def v317_def v321_def v322_def v326_def
    v327_def v331_def v332_def v336_def
  subst v137_def v141_def v149_def v158_def v341_def v346_def v347_def v351_def v356_def v357_def
    v361_def v366_def v367_def v371_def
  subst v372_def v373_def v377_def v378_def v382_def v390_def
  simp only [seqz_bw, bb_bw, and255_bw, and_bw, xor_bw, or_bw] at hbr383 hR1
  rw [bw_ne_zero] at hbr383
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hbr383
  sym_close hk _ _ _ _ _ _
  all_goals first
    | exact post94_9
    | (rw [bw_trunc8]
       have e : (v180 == 0#64 && (v176 == 0#64 && (v173 == 0#64 && v168 == 0#64))) =
           decide (Fp.mul (leLimbsToNat [post94_0, post94_1, post94_2, post94_3])
             (leLimbsToNat [post94_0, post94_1, post94_2, post94_3]) = leLimbsToNat [u0, u1, u2, u3]) := by
         rw [Bool.eq_iff_iff, decide_eq_true_iff, ← z1]
         simp only [Bool.and_eq_true, beq_iff_eq]
       rw [e]
       simp only [decide_eq_true_eq])
    | (have h1 : (v180 == 0#64 && (v176 == 0#64 && (v173 == 0#64 && v168 == 0#64))) = true ↔
           Fp.mul (leLimbsToNat [post94_0, post94_1, post94_2, post94_3])
             (leLimbsToNat [post94_0, post94_1, post94_2, post94_3]) = leLimbsToNat [u0, u1, u2, u3] := by
         simp only [Bool.and_eq_true, beq_iff_eq]; exact z1
       have h2 : (v301 == 0#64 && (v297 == 0#64 && (v294 == 0#64 && v289 == 0#64))) = true ↔
           Fp.mul (leLimbsToNat [post94_0, post94_1, post94_2, post94_3])
             (leLimbsToNat [post94_0, post94_1, post94_2, post94_3]) =
             Fp.mul Fp.rootOfUnity (leLimbsToNat [u0, u1, u2, u3]) := by
         simp only [Bool.and_eq_true, beq_iff_eq]; exact z2
       have h0 : (u3 == 0#64 && (u2 == 0#64 && (u1 == 0#64 && u0 == 0#64))) = true ↔
           leLimbsToNat [u0, u1, u2, u3] = 0 := by
         simp only [Bool.and_eq_true, beq_iff_eq]; exact z0
       rcases hbr383 with h | h
       · right
         rw [Bool.eq_iff_iff, h2, h1] at h
         constructor
         · intro hp1 hp2; exact h ⟨fun _ => hp1, fun _ => hp2⟩
         · intro hn; by_contra hp1; exact h ⟨fun hp2 => absurd hp2 hn, fun hp1' => absurd hp1' hp1⟩
       · left
         exact h0.mp h)

end Cases.Zip2005
