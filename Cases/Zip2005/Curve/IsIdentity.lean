import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Image.F_78023ec4
import Cases.Zip2005.Image.Ro

/-!
# `Ep::is_identity`

`z = 0`, limb by limb through `black_box`: the boolean word of the four `z` limbs being zero.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem is_identity_spec {P : Prop} (s : MachineState) (ra sp a0 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word)
    (hpc : s.pc = 0x78023ec4#64) (hcode : CodeAt F_78023ec4.base F_78023ec4.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = a0)
    (hp : Region a0 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] s)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12) (hd0 : Disjoint (sp - 0x30#64) 6 a0 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6)] s t →
      t.getReg .x10 = bw (decide (z0 = 0#64 ∧ z1 = 0#64 ∧ z2 = 0#64 ∧ z3 = 0#64)) → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokW.sub' 2 4 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x30#64, 6)] s
  have hlo := hstk.lo
  sym_exec [black_box_spec]
  have hfin : t.getReg .x10 = bw (decide (z0 = 0#64 ∧ z1 = 0#64 ∧ z2 = 0#64 ∧ z3 = 0#64)) := by
    rw [hx10]
    sym_subst
    simp only [seqz_bw, beq_zero_decide, bb_bw, and_bw, and255_bw, Bool.decide_and,
      Bool.and_comm, Bool.and_assoc]
  sym_close hk

end Cases.Zip2005
