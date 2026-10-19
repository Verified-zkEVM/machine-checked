import Cases.Zip2005.Curve.IsOnCurve
import Cases.Zip2005.Image.F_78026878
import Cases.Zip2005.Image.Ro

/-!
# `EpAffine::from_xy`

`CtOption::new(EpAffine { x, y }, p.is_on_curve())`: the coordinates copied to the output and
the `is_some` byte from `is_on_curve`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_xy_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word) (O : List Word) (hOl : O.length = 9)
    (hpc : s.pc = 0x78026878#64) (hcode : CodeAt F_78026878.base F_78026878.prog s)
    (hcodeOC : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x170 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hy : Region a2 [y0, y1, y2, y3] s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hd0 : Disjoint (sp - 0x170#64) 46 a0 9) (hd1 : Disjoint (sp - 0x170#64) 46 a1 4)
    (hd2 : Disjoint (sp - 0x170#64) 46 a2 4)
    (he1 : Disjoint a0 9 a1 4) (he2 : Disjoint a0 9 a2 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x170#64, 46), (a0, 9)] s t →
      Region a0 [x0, x1, x2, x3, y0, y1, y2, y3,
        replaceByte O[8]! 0 (if (Fp.sub (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [y0, y1, y2, y3])) (Fp.mul (Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [x0, x1, x2, x3])) (leLimbsToNat [x0, x1, x2, x3])) = Fp.mul 5 Fp.R2) ∨ (x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64 ∧ y0 = 0#64 ∧ y1 = 0#64 ∧ y2 = 0#64 ∧ y3 = 0#64) then 1#8 else 0#8)] t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x170#64) 46 := hstk.frame 46 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hokW.sub' 36 10 (by decide) (by bv_omega)
  -- the frame: [0, 0x40) the affine point, saved registers
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 8 := hokF.sub' 0 8 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokF.sub' 8 2 (by decide) (by bv_omega)
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0x50#64) 8 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hu := Unchanged.refl [(sp - 0x170#64, 46), (a0, 9)] s
  have hlo := hstk.lo
  sym_exec [is_on_curve_spec]
  sym_close hk
  rw [← v40_def]
  simp only [bw_trunc8, ← Bool.decide_or, decide_eq_true_eq]

end Cases.Zip2005
