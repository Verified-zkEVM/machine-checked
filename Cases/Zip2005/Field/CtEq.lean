import Cases.Zip2005.Runtime.BlackBox
import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Image.F_78028b34
import Cases.Zip2005.Image.F_7802e8ec
import Cases.Zip2005.Image.Ro

/-!
# `Fp::ct_eq`, `Fq::ct_eq`

Limb-wise `seqz (a ^^^ b)` folded with `and`, each step through `black_box`; the result is the
boolean word of the limbs being equal (the same for both fields: the code compares the
Montgomery representations as stored).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym


theorem xor_beq_zero (x y : Word) : (x ^^^ y == 0#64) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg (· ^^^ y) h
    simpa [BitVec.xor_assoc] using this
  · intro h
    subst h
    exact BitVec.xor_self

theorem beq_zero_decide (x : Word) : (x == 0#64) = decide (x = 0#64) := rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem fp_ct_eq_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word)
    (hpc : s.pc = 0x78028b34#64) (hcode : CodeAt F_78028b34.base F_78028b34.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a0 [x0, x1, x2, x3] s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hy : Region a1 [y0, y1, y2, y3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hd0 : Disjoint (sp - 0x30#64) 6 a0 4) (hd1 : Disjoint (sp - 0x30#64) 6 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6)] s t →
      t.getReg .x10 = bw (decide (x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3)) → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokW.sub' 2 4 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x30#64, 6)] s
  have hlo := hstk.lo
  sym_exec [black_box_spec]
  have hfin : t.getReg .x10 = bw (decide (x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3)) := by
    rw [hx10, ← v49_def, ← v48_def, ← v44_def, ← v43_def, ← v42_def, ← v36_def, ← v35_def,
      ← v31_def, ← v30_def, ← v29_def, ← v23_def, ← v22_def, ← v18_def, ← v17_def, ← v16_def,
      ← v10_def, ← v9_def]
    simp only [seqz_bw, xor_beq_zero, bb_bw, and_bw, and255_bw, Bool.decide_and,
      Bool.and_comm, Bool.and_assoc]
  sym_close hk

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem fq_ct_eq_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word)
    (hpc : s.pc = 0x7802e8ec#64) (hcode : CodeAt F_7802e8ec.base F_7802e8ec.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a0 [x0, x1, x2, x3] s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hy : Region a1 [y0, y1, y2, y3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hd0 : Disjoint (sp - 0x30#64) 6 a0 4) (hd1 : Disjoint (sp - 0x30#64) 6 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6)] s t →
      t.getReg .x10 = bw (decide (x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3)) → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokW.sub' 2 4 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x30#64, 6)] s
  have hlo := hstk.lo
  sym_exec [black_box_spec]
  have hfin : t.getReg .x10 = bw (decide (x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3)) := by
    rw [hx10, ← v49_def, ← v48_def, ← v44_def, ← v43_def, ← v42_def, ← v36_def, ← v35_def,
      ← v31_def, ← v30_def, ← v29_def, ← v23_def, ← v22_def, ← v18_def, ← v17_def, ← v16_def,
      ← v10_def, ← v9_def]
    simp only [seqz_bw, xor_beq_zero, bb_bw, and_bw, and255_bw, Bool.decide_and,
      Bool.and_comm, Bool.and_assoc]
  sym_close hk

end Cases.Zip2005
