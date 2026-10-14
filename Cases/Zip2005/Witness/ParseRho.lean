import Cases.Zip2005.Orchard.Rho
import Cases.Zip2005.Image.F_7801d360
import Cases.Zip2005.Image.Ro

/-!
# `Zip2005Witness::parse_rho`

`Option<Rho>::from(Rho::from_bytes(witness.rho))`: the 32 bytes at offset `0x4c0` of the
witness, `Rho::from_bytes` into the frame, and the `is_some` byte decides between `Some(limbs)`
(tag `1`, the four limbs behind it) and `None` (tag `0`, the rest of the output untouched).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem parse_rho_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7801d360#64) (hcode : CodeAt F_7801d360.base F_7801d360.prog s)
    (hcodeRho : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x150 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region (a1 + 0x4c0#64) [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi (a1 + 0x4c0#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x150#64) 42 a0 5) (hd_a1 : Disjoint (sp - 0x150#64) 42 (a1 + 0x4c0#64) 4)
    (he_a1 : Disjoint a0 5 (a1 + 0x4c0#64) 4)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x150#64, 42), (a0, 5)] s t →
      tag = (if leLimbsToNat [b0, b1, b2, b3] < Fp.p then 1#64 else 0#64) → L.length = 4 →
      (leLimbsToNat [b0, b1, b2, b3] < Fp.p →
        L = natToLeLimbs 4 (Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2)) →
      Region a0 (tag :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x150#64) 42 := hstk.frame 42 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 8 := hokW.sub' 34 8 (by decide) (by bv_omega)
  -- the frame: [8, 0x30) the `CtOption<Fp>`, saved registers
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x38#64) 5 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x38#64) 5 := hokF.sub' 1 5 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokF.sub' 6 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x150#64, 42), (a0, 5)] s
  have hlo := hstk.lo
  sym_exec [rho_from_bytes_spec]
  -- the `is_some` byte decides the branch
  all_goals rw [extractByte_replaceByte _ _ (by decide)] at v9_def
  all_goals by_cases hc : leLimbsToNat [b0, b1, b2, b3] < Fp.p
  all_goals simp only [hc, ↓reduceIte] at v9_def
  all_goals subst v9_def
  all_goals first
    | exact absurd hbr11 (by decide)
    | skip
  · -- `None`: the tag only
    sym_close (hk _ _ _)
    all_goals rfl
  · -- `Some`: the tag and the four limbs
    sym_close (hk _ _ _)
    all_goals first
      | rfl
      | exact (if_pos hc).symm
      | (intro _; rw [← v12_def, ← v13_def, ← v14_def, ← v15_def]
         simp only [hc, ↓reduceIte, natToLeLimbs_four, Nat.shiftRight_zero])

end Cases.Zip2005
