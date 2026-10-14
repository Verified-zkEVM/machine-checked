import Cases.Zip2005.Field.FromRepr
import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Image.F_78023864
import Cases.Zip2005.Image.Ro

/-!
# `HashDomain::hash_to_point_inner::unpack` (sinsemilla)

Two `Fp::from_repr` on the 64 bytes (`x` then `y`), each unwrapped (`assert_failed` when the
bytes are not canonical), into an affine point.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sinsemilla_unpack_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 c0 c1 c2 c3 : Word) (O : List Word) (hOl : O.length = 8)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x78023864#64) (hcode : CodeAt F_78023864.base F_78023864.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x140 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3, c0, c1, c2, c3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 8)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 8)
    (hd0 : Disjoint (sp - 0x140#64) 40 a0 8) (hd1 : Disjoint (sp - 0x140#64) 40 a1 8)
    (he1 : Disjoint a0 8 a1 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x140#64, 40), (a0, 8)] s t →
      leLimbsToNat [b0, b1, b2, b3] < Fp.p → leLimbsToNat [c0, c1, c2, c3] < Fp.p →
      Region a0 (natToLeLimbs 4 (Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2) ++
        natToLeLimbs 4 (Fp.mul (leLimbsToNat [c0, c1, c2, c3]) Fp.R2)) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64) 40 := hstk.frame 40 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x90#64) 18 := hokW.sub' 22 18 (by decide) (by bv_omega)
  -- the frame: [8, 0x28) `x`, [0x28, 0x50) the `CtOption<Fp>`, [0x50, 0x70) the bytes, saved registers
  have hokX : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x88#64) 4 := hokF.sub' 1 4 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 5 := hokF.sub' 5 5 (by decide) (by bv_omega)
  have hokY : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 4 := hokF.sub' 10 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokF.sub' 14 4 (by decide) (by bv_omega)
  obtain ⟨FX, hFX, hFXl⟩ := Region.exists_junk (sp - 0x88#64) 4 s
  obtain ⟨FC, hFC, hFCl⟩ := Region.exists_junk (sp - 0x68#64) 5 s
  obtain ⟨FY, hFY, hFYl⟩ := Region.exists_junk (sp - 0x40#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x140#64, 40), (a0, 8)] s
  have hlo := hstk.lo
  sym_exec [fp_from_repr_spec, hpaf]
  -- both `is_some` bytes are `1` on the surviving path
  rw [extractByte_replaceByte _ _ (by decide)] at v20_def v45_def
  have hx : leLimbsToNat [b0, b1, b2, b3] < Fp.p := by
    by_contra hc
    simp only [hc, ↓reduceIte] at v20_def
    subst v20_def
    exact hbr23 (by decide)
  have hy : leLimbsToNat [c0, c1, c2, c3] < Fp.p := by
    by_contra hc
    simp only [hc, ↓reduceIte] at v45_def
    subst v45_def
    exact hbr47 (by decide)
  sym_close hk
  all_goals first | exact hx | exact hy | (sym_subst; rfl)

end Cases.Zip2005
