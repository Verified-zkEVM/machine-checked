import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Image.F_78029b18
import Cases.Zip2005.Image.Ro

/-!
# `Fp::to_le_bits`

`to_repr` into the frame, copied out: the canonical value's little-endian words (the bit view
is the same bytes).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem to_le_bits_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (x0 x1 x2 x3 : Word)
    (O : List Word) (hOl : O.length = 4)
    (hpc : s.pc = 0x78029b18#64) (hcode : CodeAt F_78029b18.base F_78029b18.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hd0 : Disjoint (sp - 0x30#64) 6 a0 4) (hd1 : Disjoint (sp - 0x30#64) 6 a1 4)
    (hd : Disjoint a0 4 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (leLimbsToNat [x0, x1, x2, x3] * Fp.rInv % Fp.p)) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 4 := hokW.sub' 0 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokW.sub' 4 2 (by decide) (by bv_omega)
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x30#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hu := Unchanged.refl [(sp - 0x30#64, 6), (a0, 4)] s
  have hlo := hstk.lo
  sym_exec [fp_to_repr_spec]
  sym_close hk
  all_goals first | rfl | (sym_subst; rfl)

end Cases.Zip2005
