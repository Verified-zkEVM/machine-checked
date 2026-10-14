import Cases.Zip2005.Orchard.NullifierDerivingKey
import Cases.Zip2005.Orchard.CommitIvkRandomness
import Cases.Zip2005.Image.F_7801d2c8
import Cases.Zip2005.Image.F_7801ce6c
import Cases.Zip2005.Image.F_7801d074
import Cases.Zip2005.Image.Ro

/-!
# `Zip2005Witness::parse_nk`, `parse_rivk`, `parse_rivk_ext`

Thin wrappers: the 32 bytes at a fixed offset of the witness (`+0x440`, `+0x480`, `+0x460`)
through `NullifierDerivingKey::from_bytes` / `CommitIvkRandomness::from_bytes`, whose
`Option` result (tag, four limbs) is the output. The length argument is the constant 32.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- `parse_nk(out, w)`: `NullifierDerivingKey::from_bytes(&w[0x440..0x460])`. -/
theorem parse_nk_spec {P : Prop} (s : MachineState) (ra sp a0 w : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x7801d2c8#64) (hcode : CodeAt F_7801d2c8.base F_7801d2c8.prog s)
    (hcodeF : CodeAt F_78022848.base F_78022848.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x120 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = w)
    (hB : Region (w + 0x440#64) [b0, b1, b2, b3] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x440#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x120#64) 36 a0 5) (hdB : Disjoint (sp - 0x120#64) 36 (w + 0x440#64) 4)
    (heB : Disjoint a0 5 (w + 0x440#64) 4)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x120#64, 36), (a0, 5)] s t →
      tag = (if leLimbsToNat [b0, b1, b2, b3] < Fp.p then 1#64 else 0#64) → L.length = 4 →
      (leLimbsToNat [b0, b1, b2, b3] < Fp.p → L = natToLeLimbs 4 (Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2)) →
      Region a0 (tag :: L) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x120#64) 36 := hstk.frame 36 (by decide)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokW.sub' 34 2 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hlo := hstk.lo
  have hu := Unchanged.refl [(sp - 0x120#64, 36), (a0, 5)] s
  sym_exec [nullifier_deriving_key_from_bytes_spec, hpaf]
  have hR : Region a0 (post6_0 :: post6_1) s_10 := by
    rw [AsmVerif.RiscV.Sym.List.eq_map_range post6_1 post6_7]; exact hR1
  sym_close (hk _ post6_0 post6_1)
  all_goals first
    | simpa using post6_6
    | exact fun h => post6_8 rfl h

/-- `parse_rivk(out, w)`: `CommitIvkRandomness::from_bytes(&w[0x480..0x4a0])`. -/
theorem parse_rivk_spec {P : Prop} (s : MachineState) (ra sp a0 w : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x7801ce6c#64) (hcode : CodeAt F_7801ce6c.base F_7801ce6c.prog s)
    (hcodeF : CodeAt F_78022a74.base F_78022a74.prog s) (hcodeR : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x120 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = w)
    (hB : Region (w + 0x480#64) [b0, b1, b2, b3] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x480#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x120#64) 36 a0 5) (hdB : Disjoint (sp - 0x120#64) 36 (w + 0x480#64) 4)
    (heB : Disjoint a0 5 (w + 0x480#64) 4)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x120#64, 36), (a0, 5)] s t →
      tag = (if leLimbsToNat [b0, b1, b2, b3] < Fq.q then 1#64 else 0#64) → L.length = 4 →
      (leLimbsToNat [b0, b1, b2, b3] < Fq.q → L = natToLeLimbs 4 (Fq.mul (leLimbsToNat [b0, b1, b2, b3]) Fq.R2)) →
      Region a0 (tag :: L) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x120#64) 36 := hstk.frame 36 (by decide)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokW.sub' 34 2 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hlo := hstk.lo
  have hu := Unchanged.refl [(sp - 0x120#64, 36), (a0, 5)] s
  sym_exec [commit_ivk_randomness_from_bytes_spec, hpaf]
  have hR : Region a0 (post6_0 :: post6_1) s_10 := by
    rw [AsmVerif.RiscV.Sym.List.eq_map_range post6_1 post6_7]; exact hR1
  sym_close (hk _ post6_0 post6_1)
  all_goals first
    | simpa using post6_6
    | exact fun h => post6_8 rfl h

/-- `parse_rivk_ext(out, w)`: `CommitIvkRandomness::from_bytes(&w[0x460..0x480])`. -/
theorem parse_rivk_ext_spec {P : Prop} (s : MachineState) (ra sp a0 w : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x7801d074#64) (hcode : CodeAt F_7801d074.base F_7801d074.prog s)
    (hcodeF : CodeAt F_78022a74.base F_78022a74.prog s) (hcodeR : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x120 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = w)
    (hB : Region (w + 0x460#64) [b0, b1, b2, b3] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x460#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x120#64) 36 a0 5) (hdB : Disjoint (sp - 0x120#64) 36 (w + 0x460#64) 4)
    (heB : Disjoint a0 5 (w + 0x460#64) 4)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x120#64, 36), (a0, 5)] s t →
      tag = (if leLimbsToNat [b0, b1, b2, b3] < Fq.q then 1#64 else 0#64) → L.length = 4 →
      (leLimbsToNat [b0, b1, b2, b3] < Fq.q → L = natToLeLimbs 4 (Fq.mul (leLimbsToNat [b0, b1, b2, b3]) Fq.R2)) →
      Region a0 (tag :: L) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x120#64) 36 := hstk.frame 36 (by decide)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokW.sub' 34 2 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hlo := hstk.lo
  have hu := Unchanged.refl [(sp - 0x120#64, 36), (a0, 5)] s
  sym_exec [commit_ivk_randomness_from_bytes_spec, hpaf]
  have hR : Region a0 (post6_0 :: post6_1) s_10 := by
    rw [AsmVerif.RiscV.Sym.List.eq_map_range post6_1 post6_7]; exact hR1
  sym_close (hk _ post6_0 post6_1)
  all_goals first
    | simpa using post6_6
    | exact fun h => post6_8 rfl h

end Cases.Zip2005
