import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Curve.FromBytesUnchecked
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Image.F_78025854
import Cases.Zip2005.Image.Ro

/-!
# `EpAffine::to_curve`

`x` and `y` copied, `z = R` (the limbs of `R`, one from rodata at `0x78000370`) masked to `0`
at the affine identity `(0, 0)`, the identity test through `black_box`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem to_curve_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word) (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x78025854#64) (hcode : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x40 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a1 [x0, x1, x2, x3, y0, y1, y2, y3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 8)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x40#64) 8 a0 12) (hd1 : Disjoint (sp - 0x40#64) 8 a1 8)
    (he1 : Disjoint a0 12 a1 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x40#64, 8), (a0, 12)] s t →
      Region a0 ([x0, x1, x2, x3, y0, y1, y2, y3] ++
        natToLeLimbs 4 (if x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64 ∧ y0 = 0#64 ∧ y1 = 0#64 ∧ y2 = 0#64 ∧ y3 = 0#64 then 0 else Fp.R)) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 8 := hstk.frame 8 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hokW.sub' 2 6 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x30#64) 6 s
  -- the second limb of `R`, from rodata
  have hC : Region 0x78000370#64 [0x992c350be41914ad#64] s :=
    (hro.get 1 (by decide)).sub 46 1 (by decide) rfl
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78000370#64 1 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 1 (by decide)).sub' 46 1 (by decide) (by decide)
  have he_c : Disjoint a0 12 0x78000370#64 1 := by
    have h1 := hok0.offCode; have h2 := hok0.inMem
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_ofNat, Ro.layout_roBase, Ro.layout_textHi, SP1_MAX_MEMORY,
      Nat.reducePow, Nat.reduceMod] at h1 h2 ⊢
    omega
  have hf_c : Disjoint a1 8 0x78000370#64 1 := by
    have h1 := hok1.offCode; have h2 := hok1.inMem
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_ofNat, Ro.layout_roBase, Ro.layout_textHi, SP1_MAX_MEMORY,
      Nat.reducePow, Nat.reduceMod] at h1 h2 ⊢
    omega
  have hu := Unchanged.refl [(sp - 0x40#64, 8), (a0, 12)] s
  have hlo := hstk.lo
  sym_exec [black_box_spec]
  sym_close hk
  sym_subst
  simp only [seqz_bw, bb_bw, and_bw, and255_bw, beq_zero_decide, ← Bool.decide_and, shl2_shr2,
    bw_add_ones, decide_eq_true_eq, and_comm, and_assoc]
  split
  all_goals rfl

end Cases.Zip2005
