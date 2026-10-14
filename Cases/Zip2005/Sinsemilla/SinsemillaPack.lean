import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Image.F_780237dc
import Cases.Zip2005.Image.Ro

/-!
# `HashDomain::hash_to_point_inner::pack` (sinsemilla)

The affine point's two coordinates through `to_repr`, side by side: 64 bytes of canonical
`x` then canonical `y`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sinsemilla_pack_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word) (O : List Word) (hOl : O.length = 8)
    (hpc : s.pc = 0x780237dc#64) (hcode : CodeAt F_780237dc.base F_780237dc.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x60 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hy : Region a2 [y0, y1, y2, y3] s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 8)
    (hd0 : Disjoint (sp - 0x60#64) 12 a0 8) (hd1 : Disjoint (sp - 0x60#64) 12 a1 4)
    (hd2 : Disjoint (sp - 0x60#64) 12 a2 4)
    (he1 : Disjoint a0 8 a1 4) (he2 : Disjoint a0 8 a2 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x60#64, 12), (a0, 8)] s t →
      Region a0 (natToLeLimbs 4 (leLimbsToNat [x0, x1, x2, x3] * Fp.rInv % Fp.p) ++
        natToLeLimbs 4 (leLimbsToNat [y0, y1, y2, y3] * Fp.rInv % Fp.p)) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hstk.frame 12 (by decide)
  -- the frame: [8, 0x28) `x.to_repr()`, [0x28, 0x48) `y.to_repr()`, saved registers
  have hokX : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x58#64) 4 := hokW.sub' 1 4 (by decide) (by bv_omega)
  have hokY : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x38#64) 4 := hokW.sub' 5 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokW.sub' 9 3 (by decide) (by bv_omega)
  obtain ⟨FX, hFX, hFXl⟩ := Region.exists_junk (sp - 0x58#64) 4 s
  obtain ⟨FY, hFY, hFYl⟩ := Region.exists_junk (sp - 0x38#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  have hu := Unchanged.refl [(sp - 0x60#64, 12), (a0, 8)] s
  have hlo := hstk.lo
  sym_exec [fp_to_repr_spec]
  sym_close hk
  all_goals first | rfl | (sym_subst; rfl)

end Cases.Zip2005
