import Cases.Zip2005.Field.PowT.Seg18
import Cases.Zip2005.Image.Ro

/-! `pow_by_t_minus1_over2` (Fp): the prologue through `sqr(x, 129)`, then the eighteen
segments of `Cases.Zip2005.Field.PowT.Seg*`, give `Fp.powT`. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym


theorem sqrN_succ_lt (x n : Nat) : Fp.sqrN x (n + 1) < Fp.p := by
  rw [Fp.sqrN_succ]; exact Fp.sqrN_lt n (Fp.mul_lt _ _)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 20000 in
theorem pow_by_t_minus1_over2_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word)
    (x0 x1 x2 x3 : Word) (O : List Word) (hOl : O.length = 4)
    (hpc : s.pc = 0x78029d94#64) (hcode : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x450 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd : Disjoint a0 4 a1 4)
    (hd0 : Disjoint (sp - 0x450#64) 138 a0 4) (hd1 : Disjoint (sp - 0x450#64) 138 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x450#64, 138), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (Fp.powT (leLimbsToNat [x0, x1, x2, x3]))) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x450#64) 138 := hstk.frame 138 (by decide)
  obtain ⟨B0, hB0, hB0l⟩ := Region.exists_junk (sp - 0x450#64) 18 s
  obtain ⟨X1, hX1, hX1l⟩ := Region.exists_junk (sp - 0x3c0#64) 4 s
  obtain ⟨B1, hB1, hB1l⟩ := Region.exists_junk (sp - 0x3a0#64) 20 s
  obtain ⟨X2, hX2, hX2l⟩ := Region.exists_junk (sp - 0x300#64) 4 s
  obtain ⟨B2, hB2, hB2l⟩ := Region.exists_junk (sp - 0x2e0#64) 56 s
  obtain ⟨C, hC, hCl⟩ := Region.exists_junk (sp - 0x120#64) 8 s
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0xe0#64) 8 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk (sp - 0xa0#64) 8 s
  obtain ⟨S, hS, hSl⟩ := Region.exists_junk (sp - 0x60#64) 12 s
  have hokB0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x450#64) 18 := hokA.sub' 0 18 (by decide) (by bv_omega)
  have hokX1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x3c0#64) 4 := hokA.sub' 18 4 (by decide) (by bv_omega)
  have hokB1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x3a0#64) 20 := hokA.sub' 22 20 (by decide) (by bv_omega)
  have hokX2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x300#64) 4 := hokA.sub' 42 4 (by decide) (by bv_omega)
  have hokB2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2e0#64) 56 := hokA.sub' 46 56 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x120#64) 8 := hokA.sub' 102 8 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe0#64) 8 := hokA.sub' 110 8 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa0#64) 8 := hokA.sub' 118 8 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hokA.sub' 126 12 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 1104#64, 138)] s
  have L1 := fun t W => sqr_loop1 (G := G) (n := n) (P := P) (sp - 0x450#64) 128 t W
  have K : ∀ u, PowCut false s sp a0 0x7802a430#64 (Fp.powR11 (leLimbsToNat [x0, x1, x2, x3])) (Fp.powR111 (leLimbsToNat [x0, x1, x2, x3])) (Fp.powR1001 (leLimbsToNat [x0, x1, x2, x3])) (Fp.powR1101 (leLimbsToNat [x0, x1, x2, x3])) (Fp.powRun [(Fp.powR11 (leLimbsToNat [x0, x1, x2, x3])), (Fp.powR111 (leLimbsToNat [x0, x1, x2, x3])), (Fp.powR1001 (leLimbsToNat [x0, x1, x2, x3])), (Fp.powR1101 (leLimbsToNat [x0, x1, x2, x3]))] Fp.powOps0 (Fp.mul (Fp.sqrN (leLimbsToNat [x0, x1, x2, x3]) 129) (leLimbsToNat [x0, x1, x2, x3]))) u → SafeN G n P u := by
    intro u hu
    refine pow_seg1 s sp a0 _ _ _ _ _ u hstk hu (fun u h => ?_)
    refine pow_seg2 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg3 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg4 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg5 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg6 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg7 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg8 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg9 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg10 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg11 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg12 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg13 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg14 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg15 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg16 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg17 s sp a0 _ _ _ _ _ u hstk h (fun u h => ?_)
    refine pow_seg18 s sp a0 _ _ _ _ _ u hstk h hsp (by rw [hra]; exact hra1) O hOl hO hok0 hd0
      (fun v hv1 hv2 hv3 hv4 hv5 => ?_)
    exact hk v (hv1.trans hra) hv2 hv3 hv4 (by rw [Fp.powT_eq]; exact hv5)
  have hk' : ∀ (u : MachineState) (w0' w1' t00' t01' t02' t03' t10' t11' t12' t13' t20' t21' t22' t23' t30' t31' t32' t33' d0' d1' d2' d3' b0' b1' b2' b3' j0 j1 j2 j3 : Word),
      u.pc = 0x7802a430#64 → u.code = s.code → CodeAt F_78029d94.base F_78029d94.prog u →
      CodeAt F_7801bf5c.base F_7801bf5c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.getReg .x2 = sp - 1104#64 →
      u.getReg .x3 = s.getReg .x3 →
      u.getReg .x4 = s.getReg .x4 →
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
      u.getReg .x27 = s.getReg .x27 →
      Unchanged [(sp - 1104#64, 138)] s u →
      Region (sp - 1104#64) [w0', w1', t00', t01', t02', t03', t10', t11', t12', t13', t20', t21', t22', t23', t30', t31', t32', t33'] u →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 960#64) W u) →
      (∃ W : List Word, W.length = 20 ∧ Region (sp - 928#64) W u) →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 768#64) W u) →
      (∃ W : List Word, W.length = 56 ∧ Region (sp - 736#64) W u) →
      (∃ W : List Word, W.length = 8 ∧ Region (sp - 288#64) W u) →
      Region (sp - 224#64) [d0', d1', d2', d3', j0, j1, j2, j3] u →
      Region (sp - 160#64) [b0', b1', b2', b3', 11037532056220336129#64, 2469829653914515739#64, 0#64,
        4611686018427387904#64] u →
      Region (sp - 96#64) [s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23,
      s.getReg .x22, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
      s.getReg .x9, s.getReg .x8, ra] u →
      leLimbsToNat [t00', t01', t02', t03'] = (Fp.powR11 (leLimbsToNat [x0, x1, x2, x3])) →
      leLimbsToNat [t10', t11', t12', t13'] = (Fp.powR111 (leLimbsToNat [x0, x1, x2, x3])) →
      leLimbsToNat [t20', t21', t22', t23'] = (Fp.powR1001 (leLimbsToNat [x0, x1, x2, x3])) →
      leLimbsToNat [t30', t31', t32', t33'] = (Fp.powR1101 (leLimbsToNat [x0, x1, x2, x3])) →
      leLimbsToNat [d0', d1', d2', d3'] = (Fp.powRun [(Fp.powR11 (leLimbsToNat [x0, x1, x2, x3])), (Fp.powR111 (leLimbsToNat [x0, x1, x2, x3])), (Fp.powR1001 (leLimbsToNat [x0, x1, x2, x3])), (Fp.powR1101 (leLimbsToNat [x0, x1, x2, x3]))] Fp.powOps0 (Fp.mul (Fp.sqrN (leLimbsToNat [x0, x1, x2, x3]) 129) (leLimbsToNat [x0, x1, x2, x3]))) →
      [b0', b1', b2', b3'] = [d0', d1', d2', d3'] →
      SafeN G n P u := by
    intro u w0' w1' t00' t01' t02' t03' t10' t11' t12' t13' t20' t21' t22' t23' t30' t31' t32' t33' d0' d1' d2' d3' b0' b1' b2' b3' j0 j1 j2 j3 upc ucode ucA ucM ucw rx2 rx3 rx4 rx8 rx9 rx10 rx11 rx18 rx19 rx20 rx21 rx22 rx23 rx24 rx25 rx27 uU uB0 uX1 uB1 uX2 uB2 uC uD uE uS f0 f1 f2 f3 fA hbd
    exact K u ⟨w0', w1', t00', t01', t02', t03', t10', t11', t12', t13', t20', t21', t22', t23', t30', t31', t32', t33', d0', d1', d2', d3', b0', b1', b2', b3', upc, ucode, ucA, ucM, ucw, hokA, uU, rx2, rx3, rx4, rx8, rx9, rx10, rx11, rx18, rx19, rx20, rx21, rx22, (by rw [if_neg (by decide)]; exact rx23), rx24, (fun _ => rx25), rx27, uB0, uX1, uB1, uX2, uB2, uC, (by simpa using uD.take 4), ⟨[j0, j1, j2, j3], rfl, by have h := uD.shift 4; rw [show sp - 224#64 + BitVec.ofNat 64 (8 * 4) = sp - 192#64 by bv_omega] at h; simpa using h⟩, uE, (by rw [← hra] at uS; exact uS), f0, f1, f2, f3, fA, by rw [hbd]; exact fA⟩
  sym_exec [uint256_mulmod_spec, L1] stop [0x7802a430]
  sym_close hk' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  all_goals (
    have M_acc68_0 : acc68_0 = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3]) :=
      (mulpair acc47_0_def acc68_0_def).trans (congrArg₂ Fp.mul rfl rfl)
    have M_acc110_0 : acc110_0 = Fp.mul acc68_0 (leLimbsToNat [x0, x1, x2, x3]) :=
      (mulpair acc97_0_def acc110_0_def).trans (congrArg₂ Fp.mul (by rw [← v69_def, ← v70_def, ← v71_def, ← v72_def]; exact cells_lt (acc_ltp acc68_0_def)) rfl)
    have M_acc148_0 : acc148_0 = Fp.mul acc110_0 acc110_0 :=
      (mulpair acc135_0_def acc148_0_def).trans (congrArg₂ Fp.mul (by rw [← v111_def, ← v112_def, ← v113_def, ← v114_def]; exact cells_lt (acc_ltp acc110_0_def)) (by rw [← v111_def, ← v112_def, ← v113_def, ← v114_def]; exact cells_lt (acc_ltp acc110_0_def)))
    have M_acc190_0 : acc190_0 = Fp.mul acc148_0 (leLimbsToNat [x0, x1, x2, x3]) :=
      (mulpair acc177_0_def acc190_0_def).trans (congrArg₂ Fp.mul (by rw [← v149_def, ← v150_def, ← v151_def, ← v152_def]; exact cells_lt (acc_ltp acc148_0_def)) rfl)
    have M_acc228_0 : acc228_0 = Fp.mul acc190_0 acc68_0 :=
      (mulpair acc215_0_def acc228_0_def).trans (congrArg₂ Fp.mul (by rw [← v191_def, ← v192_def, ← v193_def, ← v194_def]; exact cells_lt (acc_ltp acc190_0_def)) (by rw [← v69_def, ← v70_def, ← v71_def, ← v72_def]; exact cells_lt (acc_ltp acc68_0_def)))
    have M_acc266_0 : acc266_0 = Fp.mul acc190_0 acc148_0 :=
      (mulpair acc253_0_def acc266_0_def).trans (congrArg₂ Fp.mul (by rw [← v191_def, ← v192_def, ← v193_def, ← v194_def]; exact cells_lt (acc_ltp acc190_0_def)) (by rw [← v149_def, ← v150_def, ← v151_def, ← v152_def]; exact cells_lt (acc_ltp acc148_0_def)))
    have M_acc285_0 : acc285_0 = Fp.sqrN (leLimbsToNat [x0, x1, x2, x3]) 129 := acc285_0_def.symm
    have M_acc329_0 : acc329_0 = Fp.mul acc285_0 (leLimbsToNat [x0, x1, x2, x3]) :=
      (mulpair acc316_0_def acc329_0_def).trans (congrArg₂ Fp.mul (by rw [← v286_def, ← v287_def, ← v288_def, ← v289_def]; exact cells_lt (by rw [M_acc285_0]; exact sqrN_succ_lt _ 128)) rfl)
    have M_acc371_0 : acc371_0 = Fp.mul acc329_0 acc329_0 :=
      (mulpair acc358_0_def acc371_0_def).trans (congrArg₂ Fp.mul (by rw [← v330_def, ← v331_def, ← v332_def, ← v333_def]; exact cells_lt (acc_ltp acc329_0_def)) (by rw [← v330_def, ← v331_def, ← v332_def, ← v333_def]; exact cells_lt (acc_ltp acc329_0_def)))
    have eR10 : acc68_0 = Fp.powR10 (leLimbsToNat [x0, x1, x2, x3]) := by rw [Fp.powR10]; exact M_acc68_0
    have eR11 : acc110_0 = Fp.powR11 (leLimbsToNat [x0, x1, x2, x3]) := by rw [Fp.powR11, ← eR10]; exact M_acc110_0
    have eR110 : acc148_0 = Fp.powR110 (leLimbsToNat [x0, x1, x2, x3]) := by rw [Fp.powR110, ← eR11]; exact M_acc148_0
    have eR111 : acc190_0 = Fp.powR111 (leLimbsToNat [x0, x1, x2, x3]) := by rw [Fp.powR111, ← eR110]; exact M_acc190_0
    have eR1001 : acc228_0 = Fp.powR1001 (leLimbsToNat [x0, x1, x2, x3]) := by rw [Fp.powR1001, ← eR111, ← eR10]; exact M_acc228_0
    have eR1101 : acc266_0 = Fp.powR1101 (leLimbsToNat [x0, x1, x2, x3]) := by rw [Fp.powR1101, ← eR111, ← eR110]; exact M_acc266_0
    have hfin : acc371_0 = Fp.powRun [Fp.powR11 (leLimbsToNat [x0, x1, x2, x3]), Fp.powR111 (leLimbsToNat [x0, x1, x2, x3]), Fp.powR1001 (leLimbsToNat [x0, x1, x2, x3]), Fp.powR1101 (leLimbsToNat [x0, x1, x2, x3])] Fp.powOps0 (Fp.mul (Fp.sqrN (leLimbsToNat [x0, x1, x2, x3]) 129) (leLimbsToNat [x0, x1, x2, x3])) := by
      rw [← M_acc285_0, ← M_acc329_0, show Fp.powOps0 = [4] from rfl, Fp.powRun_cons, Fp.powStep_sq, Fp.powRun_nil, ← M_acc371_0]
    first
    | (rw [← v111_def, ← v112_def, ← v113_def, ← v114_def, cells_lt (acc_ltp acc110_0_def)]; exact eR11)
    | (rw [← v191_def, ← v192_def, ← v193_def, ← v194_def, cells_lt (acc_ltp acc190_0_def)]; exact eR111)
    | (rw [← v229_def, ← v230_def, ← v231_def, ← v232_def, cells_lt (acc_ltp acc228_0_def)]; exact eR1001)
    | (rw [← v267_def, ← v268_def, ← v269_def, ← v270_def, cells_lt (acc_ltp acc266_0_def)]; exact eR1101)
    | (rw [← v372_def, ← v373_def, ← v374_def, ← v375_def, cells_lt (acc_ltp acc371_0_def)]; exact hfin)
)
end Cases.Zip2005
