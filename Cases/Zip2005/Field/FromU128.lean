import Cases.Zip2005.Field.FromRaw
import Cases.Zip2005.Image.F_78029ae8
import Cases.Zip2005.Image.Ro

/-!
# `Fp::from_u128`

`from_raw([lo, hi, 0, 0])`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem from_u128_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 lo hi : Word)
    (O : List Word) (hOl : O.length = 4)
    (hpc : s.pc = 0x78029ae8#64) (hcode : CodeAt F_78029ae8.base F_78029ae8.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x40 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = lo) (ha2 : s.getReg .x12 = hi)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hd0 : Disjoint (sp - 0x40#64) 8 a0 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x40#64, 8), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (Fp.mul (leLimbsToNat [lo, hi, 0#64, 0#64]) Fp.R2)) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 8 := hstk.frame 8 (by decide)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x28#64) 4 := hokW.sub' 3 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8#64) 1 := hokW.sub' 7 1 (by decide) (by bv_omega)
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x28#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x8#64) 1 s
  have hu := Unchanged.refl [(sp - 0x40#64, 8), (a0, 4)] s
  have hlo := hstk.lo
  sym_exec [fp_from_raw_spec]
  sym_close hk

end Cases.Zip2005
