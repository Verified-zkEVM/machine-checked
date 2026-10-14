import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Image.F_78028ce8
import Cases.Zip2005.Image.Ro

/-!
# `<[u8; 32] as From<Fp>>::from`

A call to `to_repr` with the same arguments.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem fp_into_bytes_spec {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (x0 x1 x2 x3 : Word)
    (O : List Word) (hOl : O.length = 4)
    (hpc : s.pc = 0x78028ce8#64) (hcode : CodeAt F_78028ce8.base F_78028ce8.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hd0 : Disjoint (sp - 0x10#64) 2 a0 4) (hd1 : Disjoint (sp - 0x10#64) 2 a1 4)
    (hd : Disjoint a0 4 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (leLimbsToNat [x0, x1, x2, x3] * Fp.rInv % Fp.p)) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hu := Unchanged.refl [(sp - 0x10#64, 2), (a0, 4)] s
  have hlo := hstk.lo
  sym_exec [fp_to_repr_spec]
  sym_close hk

end Cases.Zip2005
