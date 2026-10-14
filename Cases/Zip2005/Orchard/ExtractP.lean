import Cases.Zip2005.Curve.ToAffine
import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Curve.PointBytes
import Cases.Zip2005.Image.F_78020ca0
import Cases.Zip2005.Image.Ro

/-!
# `orchard::spec::extract_p`

`to_affine`, `coordinates`, and the `x` coordinate masked by `is_some` (`unwrap_or(zero)`):
since the affine identity is `(0, 0)`, the result is the affine `x` in every case.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem extract_p_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Word)
    (O : List Word) (hOl : O.length = 4)
    (hpc : s.pc = 0x78020ca0#64) (hcode : CodeAt F_78020ca0.base F_78020ca0.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeC : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x2d0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hd0 : Disjoint (sp - 0x2d0#64) 90 a0 4) (hd1 : Disjoint (sp - 0x2d0#64) 90 a1 12)
    (he1 : Disjoint a0 4 a1 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x2d0#64, 90), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).1) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2d0#64) 90 := hstk.frame 90 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa0#64) 20 := hokW.sub' 70 20 (by decide) (by bv_omega)
  -- the frame: [8, 0x50) the coordinates, [0x50, 0x90) the affine point, saved registers
  obtain ⟨FC, hFC, hFCl⟩ := Region.exists_junk (sp - 0x98#64) 9 s
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0x50#64) 8 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x98#64) 9 := hokF.sub' 1 9 (by decide) (by bv_omega)
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 8 := hokF.sub' 10 8 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokF.sub' 18 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x2d0#64, 90), (a0, 4)] s
  have hlo := hstk.lo
  sym_exec [to_affine_spec, coordinates_spec]
  sym_close hk
  sym_subst
  rw [extractByte_replaceByte _ _ (by decide)]
  simp only [and_neg_zext_if, List.getElem!_cons_zero, List.getElem!_cons_succ]
  rw [ite_list4 _ _ _ _ _ (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)]
  rfl

end Cases.Zip2005
