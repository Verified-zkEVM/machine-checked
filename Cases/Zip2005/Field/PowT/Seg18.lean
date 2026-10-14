import Cases.Zip2005.Field.PowT.Seg17
import Cases.Zip2005.Image.Ro

/-! `pow_by_t_minus1_over2`, segment 18 of the addition chain (see `Cases.Zip2005.PowT`). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 20000 in
theorem pow_seg18 {P : Prop} (s0 : MachineState) (sp a0 : Word) (T0 T1 T2 T3 A : Nat) (t : MachineState)
    (hstk : StackOk Ro.layout 0x450 sp)
    (h : PowCut true s0 sp a0 0x7802e104#64 T0 T1 T2 T3 A t)
    (hsp0 : s0.getReg .x2 = sp) (hra1 : s0.getReg .x1 &&& ~~~1#64 = s0.getReg .x1) (O : List Word) (hOl : O.length = 4) (hO : Region a0 O s0)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd0 : Disjoint (sp - 1104#64) 138 a0 4)
    (hk : ∀ u, u.pc = s0.getReg .x1 → CalleeSaved s0 u → u.code = s0.code →
      Unchanged [(sp - 1104#64, 138), (a0, 4)] s0 u →
      Region a0 (natToLeLimbs 4 (Fp.powRun [T0, T1, T2, T3] Fp.powOps18 A)) u → Safe P u) :
    Safe P t := by
  obtain ⟨w0, w1, t00, t01, t02, t03, t10, t11, t12, t13, t20, t21, t22, t23, t30, t31, t32, t33, d0, d1, d2, d3, b0, b1, b2, b3, hpc, hcode, hcA, hcM, hcw, hok, hU0, hx2, hx3, hx4, hx8, hx9, hx10, hx11, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hB0, hX1, hB1, hX2, hB2, hC, hD1, hD2, hE, hS, eT0, eT1, eT2, eT3, eA, eB⟩ := h
  rw [if_pos rfl] at hx23
  clear hx25
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
  have hu := Unchanged.refl [(sp - 1104#64, 138), (a0, 4)] t
  have hO' := hO.of_unchanged' hU0 hOl (by simp only [List.mem_singleton, forall_eq]; exact hd0.symm)
  have hk' : ∀ u, u.pc = s0.getReg .x1 → u.code = t.code → u.getReg .x2 = sp →
      u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
      u.getReg .x8 = s0.getReg .x8 →
      u.getReg .x9 = s0.getReg .x9 →
      u.getReg .x18 = s0.getReg .x18 →
      u.getReg .x19 = s0.getReg .x19 →
      u.getReg .x20 = s0.getReg .x20 →
      u.getReg .x21 = s0.getReg .x21 →
      u.getReg .x22 = s0.getReg .x22 →
      u.getReg .x23 = s0.getReg .x23 →
      u.getReg .x24 = s0.getReg .x24 →
      u.getReg .x25 = s0.getReg .x25 →
      u.getReg .x26 = s0.getReg .x26 →
      u.getReg .x27 = t.getReg .x27 →
      Unchanged [(sp - 1104#64, 138), (a0, 4)] t u →
      Region a0 (natToLeLimbs 4 (Fp.powRun [T0, T1, T2, T3] Fp.powOps18 A)) u → Safe P u := by
    intro u upc ucode r2 r3 r4 rx8 rx9 rx18 rx19 rx20 rx21 rx22 rx23 rx24 rx25 rx26 r27 uU uR
    refine hk u upc ?_ (ucode.trans hcode) ((hU0.mono (by simp)).trans uU) uR
    intro r hr
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | assumption | exact r2.trans hsp0.symm | exact r3.trans hx3 | exact r4.trans hx4 | exact r27.trans hx27
  sym_exec [uint256_mulmod_spec]
  sym_close hk'
  have M_acc15_0 : acc15_0 = Fp.mul A A :=
    (mulpair acc2_0_def acc15_0_def).trans (congrArg₂ Fp.mul eA eB)
  have M_acc57_0 : acc57_0 = Fp.mul acc15_0 T0 :=
    (mulpair acc44_0_def acc57_0_def).trans (congrArg₂ Fp.mul (by rw [← v16_def, ← v17_def, ← v18_def, ← v19_def]; exact cells_lt (acc_ltp acc15_0_def)) eT0)
  have M_acc91_0 : acc91_0 = Fp.mul acc57_0 acc57_0 :=
    (mulpair acc78_0_def acc91_0_def).trans (congrArg₂ Fp.mul (by rw [← v58_def, ← v59_def, ← v60_def, ← v61_def]; exact cells_lt (acc_ltp acc57_0_def)) (by rw [← v58_def, ← v59_def, ← v60_def, ← v61_def]; exact cells_lt (acc_ltp acc57_0_def)))
  have hfin : acc91_0 = Fp.powRun [T0, T1, T2, T3] Fp.powOps18 A := by
    rw [show Fp.powOps18 = [4, 0, 4] from rfl]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc15_0]
    rw [Fp.powRun_cons, (Fp.powStep_tbl T0 T1 T2 T3 _).1, ← M_acc57_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc91_0]
    rfl
  rw [← hfin, ← v92_def, ← v93_def, ← v94_def, ← v95_def]; exact cells4 _

end Cases.Zip2005
