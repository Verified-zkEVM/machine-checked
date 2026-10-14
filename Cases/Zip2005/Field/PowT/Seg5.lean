import Cases.Zip2005.Field.PowT.Seg4
import Cases.Zip2005.Image.Ro

/-! `pow_by_t_minus1_over2`, segment 5 of the addition chain (see `Cases.Zip2005.PowT`). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 20000 in
theorem pow_seg5 {P : Prop} (s0 : MachineState) (sp a0 : Word) (T0 T1 T2 T3 A : Nat) (t : MachineState)
    (hstk : StackOk Ro.layout 0x450 sp)
    (h : PowCut false s0 sp a0 0x7802b290#64 T0 T1 T2 T3 A t)
    (hk : ∀ u, PowCut false s0 sp a0 0x7802b650#64 T0 T1 T2 T3 (Fp.powRun [T0, T1, T2, T3] Fp.powOps5 A) u →
      Safe P u) : Safe P t := by
  obtain ⟨w0, w1, t00, t01, t02, t03, t10, t11, t12, t13, t20, t21, t22, t23, t30, t31, t32, t33, d0, d1, d2, d3, b0, b1, b2, b3, hpc, hcode, hcA, hcM, hcw, hok, hU0, hx2, hx3, hx4, hx8, hx9, hx10, hx11, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hB0, hX1, hB1, hX2, hB2, hC, hD1, hD2, hE, hS, eT0, eT1, eT2, eT3, eA, eB⟩ := h
  rw [if_neg (by decide)] at hx23
  replace hx25 := hx25 rfl
  obtain ⟨X1, hX1l, hX1⟩ := hX1
  obtain ⟨B1, hB1l, hB1⟩ := hB1
  obtain ⟨X2, hX2l, hX2⟩ := hX2
  obtain ⟨B2, hB2l, hB2⟩ := hB2
  obtain ⟨C, hCl, hC⟩ := hC
  obtain ⟨D2, hD2l, hD2⟩ := hD2
  have hokB0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1104#64) 18 := hok.sub' 0 18 (by decide) (by bv_omega)
  have hokX1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 960#64) 4 := hok.sub' 18 4 (by decide) (by bv_omega)
  have hokB1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 928#64) 20 := hok.sub' 22 20 (by decide) (by bv_omega)
  have hokX2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 768#64) 4 := hok.sub' 42 4 (by decide) (by bv_omega)
  have hokB2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 736#64) 56 := hok.sub' 46 56 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 288#64) 8 := hok.sub' 102 8 (by decide) (by bv_omega)
  have hokD1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 224#64) 4 := hok.sub' 110 4 (by decide) (by bv_omega)
  have hokD2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 192#64) 4 := hok.sub' 114 4 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 160#64) 8 := hok.sub' 118 8 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 96#64) 12 := hok.sub' 126 12 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 1104#64, 138)] t
  have hk' : ∀ (u : MachineState) (w0' w1' t00' t01' t02' t03' t10' t11' t12' t13' t20' t21' t22' t23' t30' t31' t32' t33' d0' d1' d2' d3' b0' b1' b2' b3' : Word),
      u.pc = 0x7802b650#64 → u.code = t.code → CodeAt F_78029d94.base F_78029d94.prog u →
      CodeAt F_7801bf5c.base F_7801bf5c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.getReg .x2 = sp - 1104#64 →
      u.getReg .x3 = t.getReg .x3 →
      u.getReg .x4 = t.getReg .x4 →
      u.getReg .x8 = a0 →
      u.getReg .x9 = 4611686018427387904#64 →
      u.getReg .x10 = sp - 224#64 →
      u.getReg .x11 = sp - 160#64 →
      u.getReg .x18 = 2469829653914515739#64 →
      u.getReg .x19 = 2445952672640170197#64 →
      u.getReg .x20 = 8127635680764926565#64 →
      u.getReg .x21 = 12438865661331504215#64 →
      u.getReg .x22 = 14933811601259063721#64 →
      u.getReg .x23 = sp - 128#64 →
      u.getReg .x24 = 11037532056220336129#64 →
      u.getReg .x25 = 4611686018427387904#64 →
      u.getReg .x27 = t.getReg .x27 →
      Unchanged [(sp - 1104#64, 138)] t u →
      Region (sp - 1104#64) [w0', w1', t00', t01', t02', t03', t10', t11', t12', t13', t20', t21', t22', t23', t30', t31', t32', t33'] u →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 960#64) W u) →
      (∃ W : List Word, W.length = 20 ∧ Region (sp - 928#64) W u) →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 768#64) W u) →
      (∃ W : List Word, W.length = 56 ∧ Region (sp - 736#64) W u) →
      (∃ W : List Word, W.length = 8 ∧ Region (sp - 288#64) W u) →
      Region (sp - 224#64) [d0', d1', d2', d3'] u →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 192#64) W u) →
      Region (sp - 160#64) [b0', b1', b2', b3', 11037532056220336129#64, 2469829653914515739#64, 0#64,
        4611686018427387904#64] u →
      Region (sp - 96#64) [s0.getReg .x26, s0.getReg .x25, s0.getReg .x24, s0.getReg .x23,
      s0.getReg .x22, s0.getReg .x21, s0.getReg .x20, s0.getReg .x19, s0.getReg .x18,
      s0.getReg .x9, s0.getReg .x8, s0.getReg .x1] u →
      leLimbsToNat [t00', t01', t02', t03'] = T0 →
      leLimbsToNat [t10', t11', t12', t13'] = T1 →
      leLimbsToNat [t20', t21', t22', t23'] = T2 →
      leLimbsToNat [t30', t31', t32', t33'] = T3 →
      leLimbsToNat [d0', d1', d2', d3'] = Fp.powRun [T0, T1, T2, T3] Fp.powOps5 A →
      [b0', b1', b2', b3'] = [d0', d1', d2', d3'] →
      Safe P u := by
    intro u w0' w1' t00' t01' t02' t03' t10' t11' t12' t13' t20' t21' t22' t23' t30' t31' t32' t33' d0' d1' d2' d3' b0' b1' b2' b3' upc ucode ucA ucM ucw rx2 rx3 rx4 rx8 rx9 rx10 rx11 rx18 rx19 rx20 rx21 rx22 rx23 rx24 rx25 rx27 uU uB0 uX1 uB1 uX2 uB2 uC uD1 uD2 uE uS f0 f1 f2 f3 fA hbd
    exact hk u ⟨w0', w1', t00', t01', t02', t03', t10', t11', t12', t13', t20', t21', t22', t23', t30', t31', t32', t33', d0', d1', d2', d3', b0', b1', b2', b3', upc, ucode.trans hcode, ucA, ucM, ucw, hok, hU0.trans uU, rx2, rx3.trans hx3, rx4.trans hx4, rx8, rx9, rx10, rx11, rx18, rx19, rx20, rx21, rx22, (by rw [if_neg (by decide)]; exact rx23), rx24, (fun _ => rx25), rx27.trans hx27, uB0, uX1, uB1, uX2, uB2, uC, uD1, uD2, uE, uS, f0, f1, f2, f3, fA, by rw [hbd]; exact fA⟩
  sym_exec [uint256_mulmod_spec] stop [0x7802b650]
  sym_close hk' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have M_acc15_0 : acc15_0 = Fp.mul A A :=
    (mulpair acc2_0_def acc15_0_def).trans (congrArg₂ Fp.mul eA eB)
  have M_acc57_0 : acc57_0 = Fp.mul acc15_0 acc15_0 :=
    (mulpair acc44_0_def acc57_0_def).trans (congrArg₂ Fp.mul (by rw [← v16_def, ← v17_def, ← v18_def, ← v19_def]; exact cells_lt (acc_ltp acc15_0_def)) (by rw [← v16_def, ← v17_def, ← v18_def, ← v19_def]; exact cells_lt (acc_ltp acc15_0_def)))
  have M_acc99_0 : acc99_0 = Fp.mul acc57_0 acc57_0 :=
    (mulpair acc86_0_def acc99_0_def).trans (congrArg₂ Fp.mul (by rw [← v58_def, ← v59_def, ← v60_def, ← v61_def]; exact cells_lt (acc_ltp acc57_0_def)) (by rw [← v58_def, ← v59_def, ← v60_def, ← v61_def]; exact cells_lt (acc_ltp acc57_0_def)))
  have M_acc141_0 : acc141_0 = Fp.mul acc99_0 T1 :=
    (mulpair acc128_0_def acc141_0_def).trans (congrArg₂ Fp.mul (by rw [← v100_def, ← v101_def, ← v102_def, ← v103_def]; exact cells_lt (acc_ltp acc99_0_def)) eT1)
  have M_acc183_0 : acc183_0 = Fp.mul acc141_0 acc141_0 :=
    (mulpair acc170_0_def acc183_0_def).trans (congrArg₂ Fp.mul (by rw [← v142_def, ← v143_def, ← v144_def, ← v145_def]; exact cells_lt (acc_ltp acc141_0_def)) (by rw [← v142_def, ← v143_def, ← v144_def, ← v145_def]; exact cells_lt (acc_ltp acc141_0_def)))
  have M_acc225_0 : acc225_0 = Fp.mul acc183_0 acc183_0 :=
    (mulpair acc212_0_def acc225_0_def).trans (congrArg₂ Fp.mul (by rw [← v184_def, ← v185_def, ← v186_def, ← v187_def]; exact cells_lt (acc_ltp acc183_0_def)) (by rw [← v184_def, ← v185_def, ← v186_def, ← v187_def]; exact cells_lt (acc_ltp acc183_0_def)))
  have hfin : acc225_0 = Fp.powRun [T0, T1, T2, T3] Fp.powOps5 A := by
    rw [show Fp.powOps5 = [4, 4, 4, 1, 4, 4] from rfl]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc15_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc57_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc99_0]
    rw [Fp.powRun_cons, (Fp.powStep_tbl T0 T1 T2 T3 _).2.1, ← M_acc141_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc183_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc225_0]
    rfl
  rw [← v226_def, ← v227_def, ← v228_def, ← v229_def, cells_lt (acc_ltp acc225_0_def)]; exact hfin

end Cases.Zip2005
