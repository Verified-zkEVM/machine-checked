import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Image.F_78023a18
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- Poseidon's S-box on `Fp`: `out := x⁵`, in Montgomery form
    (`P128Pow5T3::sbox`, `val.pow_vartime([5])`). -/
theorem sbox_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word) (x0 x1 x2 x3 : Word)
    (hpc : s.pc = 0x78023a18#64) (hcode : CodeAt F_78023a18.base F_78023a18.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xf0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hd0 : Disjoint (sp - 0xf0#64) 30 a0 4) (hd1 : Disjoint (sp - 0xf0#64) 30 a1 4)
    (hd : Disjoint a0 4 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xf0#64, 30), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (Fp.pow5 (leLimbsToNat [x0, x1, x2, x3]))) t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨O, hO, hOlen⟩ := Region.exists_junk a0 4 s
  obtain ⟨F, hF, hFlen⟩ := Region.exists_junk (sp - 0xf0#64) 30 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xf0#64) 30 := hstk.frame 30 (by decide)
  have hu := Unchanged.refl [(sp - 0xf0#64, 30), (a0, 4)] s
  sym_exec [uint256_mulmod_spec]
  sym_close hk
  sym_subst
  simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_R, Fp.limbs_rInv, Fp.limbs_mod]
  rfl

end Cases.Zip2005
