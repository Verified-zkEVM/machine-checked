import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Field.FromRaw
import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Field.PowT
import Cases.Zip2005.Field.FpAdd
import Cases.Zip2005.Field.FpSub
import Cases.Zip2005.Image.F_78026258
import Cases.Zip2005.Image.Ro

/-!
# `EpAffine::is_on_curve`

`(y² - (x³ + 5)).is_zero() | self.is_identity()`: two `UINT256_MULMOD`s for `y²`, two for `x³`,
`from_raw(5)`, the inlined `Fp::add` and `Fp::sub` chains, and the zero tests through `black_box`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym


theorem xor_eq_zero_decide (x y : Word) : decide (x ^^^ y = 0#64) = decide (x = y) := by
  rw [← beq_zero_decide, xor_beq_zero]

/-- Four limbs agree iff the values do (`ct_eq` on canonical field elements). -/
theorem limbs4_eq_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (b3 = a3 ∧ b2 = a2 ∧ b1 = a1 ∧ b0 = a0) ↔
      leLimbsToNat [a0, a1, a2, a3] = leLimbsToNat [b0, b1, b2, b3] := by
  constructor
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl
  · intro h
    have ha := natToLeLimbs_leLimbsToNat [a0, a1, a2, a3]
    have hb := natToLeLimbs_leLimbsToNat [b0, b1, b2, b3]
    simp only [List.length_cons, List.length_nil] at ha hb
    rw [h, hb] at ha
    simp only [List.cons.injEq, and_true] at ha
    exact ⟨ha.2.2.2, ha.2.2.1, ha.2.1, ha.1⟩

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem is_on_curve_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word)
    (hpc : s.pc = 0x78026258#64) (hcode : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x120 sp)
    (ha0 : s.getReg .x10 = a0)
    (hp : Region a0 [x0, x1, x2, x3, y0, y1, y2, y3] s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 8)
    (hd0 : Disjoint (sp - 0x120#64) 36 a0 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x120#64, 36)] s t →
      t.getReg .x10 = bw (decide (Fp.sub (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [y0, y1, y2, y3])) (Fp.mul (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3])) (leLimbsToNat [x0, x1, x2, x3])) = Fp.mul 5 Fp.R2) || decide (x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64 ∧ y0 = 0#64 ∧ y1 = 0#64 ∧ y2 = 0#64 ∧ y3 = 0#64)) → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x120#64) 36 := hstk.frame 36 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 34 := hokW.sub' 2 34 (by decide) (by bv_omega)
  -- the frame: [8, 0x28) `y²`, [0x28, 0x48) `from_raw(5)`, [0x48, 0x68) the `mulmod` result,
  -- [0x68, 0xa8) the `mulmod` operand and modulus, saved registers
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x108#64) 4 := hokF.sub' 1 4 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe8#64) 4 := hokF.sub' 5 4 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xc8#64) 4 := hokF.sub' 9 4 (by decide) (by bv_omega)
  have hok4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa8#64) 8 := hokF.sub' 13 8 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 21 13 (by decide) (by bv_omega)
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x108#64) 4 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0xe8#64) 4 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0xc8#64) 4 s
  obtain ⟨F4, hF4, hF4l⟩ := Region.exists_junk (sp - 0xa8#64) 8 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x120#64, 36)] s
  have hlo := hstk.lo
  sym_exec [uint256_mulmod_spec, fp_from_raw_spec, black_box_spec]
  -- `y²`, `x²`, `from_raw(0)`, `x² + 0`, `x³`, `y² - x³`, `from_raw(5)`
  have hy2 : acc68_0 = Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [y0, y1, y2, y3]) := mulpair acc47_0_def acc68_0_def
  have hY2 : leLimbsToNat [v69, v71, v73, v75] = acc68_0 := by
    rw [← v69_def, ← v71_def, ← v73_def, ← v75_def]; exact cells_lt (acc_ltp acc68_0_def)
  have hx2 : acc114_0 = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3]) := mulpair acc101_0_def acc114_0_def
  have hX2 : leLimbsToNat [v115, v116, v117, v118] = acc114_0 := by
    rw [← v115_def, ← v116_def, ← v117_def, ← v118_def]; exact cells_lt (acc_ltp acc114_0_def)
  have h0 : acc127_0 = 0 := by
    rw [← acc127_0_def, show leLimbsToNat [0#64, 0#64, 0#64, 0#64] = 0 by decide]; decide +kernel
  have hZ : leLimbsToNat [v128, v129, v130, v131] = acc127_0 := by
    rw [← v128_def, ← v129_def, ← v130_def, ← v131_def]; exact cells_lt (by rw [h0]; exact Fp.p_pos)
  have hsum : leLimbsToNat [v177, v182, v185, v189] = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3]) := by
    rw [fadd_chain v132_def v133_def v134_def v135_def v136_def v137_def v138_def v139_def v140_def v141_def v142_def v143_def v144_def v145_def v151_def v155_def v156_def v157_def v159_def v160_def v162_def v163_def v164_def v165_def v166_def v167_def v168_def v169_def v173_def v174_def v176_def v177_def v178_def v179_def v180_def v181_def v182_def v183_def v184_def v185_def v186_def v187_def v188_def v189_def (by rw [hZ, h0]; exact Fp.p_pos) (by rw [hX2]; exact acc_ltp acc114_0_def),
      hZ, hX2, h0, hx2]
    unfold Fp.add
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (Fp.mul_lt _ _)
  have hx3 : acc223_0 = Fp.mul (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3])) (leLimbsToNat [x0, x1, x2, x3]) := by
    rw [mulpair acc210_0_def acc223_0_def, hsum]
  have hX3 : leLimbsToNat [v224, v225, v226, v227] = acc223_0 := by
    rw [← v224_def, ← v225_def, ← v226_def, ← v227_def]; exact cells_lt (acc_ltp acc223_0_def)
  have hsub : leLimbsToNat [v255, v260, v263, v267] =
      Fp.sub (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [y0, y1, y2, y3])) (Fp.mul (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3])) (leLimbsToNat [x0, x1, x2, x3])) := by
    rw [fsub_chain v229_def v230_def v232_def v233_def v234_def v235_def v236_def v237_def v238_def v240_def v241_def v242_def v243_def v244_def v245_def v246_def v248_def v249_def v250_def v251_def v252_def v253_def v254_def v255_def v256_def v257_def v258_def v259_def v260_def v261_def v262_def v263_def v264_def v265_def v266_def v267_def (by rw [hY2]; exact acc_ltp acc68_0_def) (by rw [hX3]; exact acc_ltp acc223_0_def),
      hY2, hX3, hy2, hx3]
  have h5 : acc277_0 = Fp.mul 5 Fp.R2 := by
    rw [← acc277_0_def, show leLimbsToNat [5#64, 0#64, 0#64, 0#64] = 5 by decide]
  have hA5 : leLimbsToNat [v278, v284, v296, v308] = acc277_0 := by
    rw [← v278_def, ← v284_def, ← v296_def, ← v308_def]
    exact cells_lt (by rw [← acc277_0_def]; exact Fp.mul_lt _ _)
  -- the limb-wise `ct_eq` against `5·R`
  have hbeq : (decide (v308 = v267) && (decide (v296 = v263) && (decide (v284 = v260) && decide (v278 = v255)))) =
      decide (Fp.sub (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [y0, y1, y2, y3])) (Fp.mul (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3])) (leLimbsToNat [x0, x1, x2, x3])) = Fp.mul 5 Fp.R2) := by
    rw [← Bool.decide_and, ← Bool.decide_and, ← Bool.decide_and]
    exact decide_eq_decide.mpr (by rw [limbs4_eq_iff, hsub, hA5, h5])
  have hfin : s_423.getReg .x10 = bw (decide (Fp.sub (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [y0, y1, y2, y3])) (Fp.mul (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3])) (leLimbsToNat [x0, x1, x2, x3])) = Fp.mul 5 Fp.R2) || decide (x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64 ∧ y0 = 0#64 ∧ y1 = 0#64 ∧ y2 = 0#64 ∧ y3 = 0#64)) := by
    rw [hx10, ← v404_def, ← v403_def, ← v399_def, ← v398_def, ← v394_def, ← v393_def, ← v389_def, ← v388_def, ← v383_def, ← v382_def, ← v378_def, ← v377_def, ← v372_def, ← v371_def, ← v367_def, ← v366_def, ← v361_def, ← v360_def, ← v355_def, ← v354_def, ← v350_def, ← v349_def, ← v344_def, ← v343_def, ← v339_def, ← v338_def, ← v333_def, ← v332_def, ← v328_def, ← v327_def, ← v322_def, ← v321_def, ← v316_def, ← v315_def, ← v311_def, ← v310_def, ← v309_def, ← v304_def, ← v303_def, ← v299_def, ← v298_def, ← v297_def, ← v292_def, ← v291_def, ← v287_def, ← v286_def, ← v285_def, ← v280_def, ← v279_def]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw, or_bw, beq_zero_decide, xor_eq_zero_decide]
    rw [hbeq]
    simp only [Bool.decide_and, Bool.and_comm, Bool.and_assoc, Bool.or_comm]
  sym_close hk

end Cases.Zip2005
