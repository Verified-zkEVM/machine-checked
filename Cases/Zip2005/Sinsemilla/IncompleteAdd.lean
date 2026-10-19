import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Runtime.Memcmp
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Orchard.SpendValidatingKey
import Cases.Zip2005.Image.F_780235e8
import Cases.Zip2005.Image.F_78035f88
import Cases.Zip2005.Image.F_780360e0
import Cases.Zip2005.Image.Ro

/-!
# `HashDomain::hash_to_point_inner::incomplete_add` (sinsemilla)

Incomplete addition of two `IncompletePoint`s (a validity word and an affine point): invalid
if either input is, or if the `x` coordinates agree (`memcmp`); otherwise the accelerated
`syscall_pallas_add` on two `sp1_lib` affine points built in the frame.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem incomplete_add_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (pt qt px0 px1 px2 px3 py0 py1 py2 py3 qx0 qx1 qx2 qx3 qy0 qy1 qy2 qy3 : Word) (O : List Word) (hOl : O.length = 9)
    (hpc : s.pc = 0x780235e8#64) (hcode : CodeAt F_780235e8.base F_780235e8.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x130 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (hP : Region a1 [pt, px0, px1, px2, px3, py0, py1, py2, py3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 9)
    (hQ : Region a2 [qt, qx0, qx1, qx2, qx3, qy0, qy1, qy2, qy3] s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 9)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hd0 : Disjoint (sp - 0x130#64) 38 a0 9) (hd1 : Disjoint (sp - 0x130#64) 38 a1 9)
    (hd2 : Disjoint (sp - 0x130#64) 38 a2 9)
    (he1 : Disjoint a0 9 a1 9) (he2 : Disjoint a0 9 a2 9)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x130#64, 38), (a0, 9)] s t →
      tag = (if pt = 0#64 ∨ qt = 0#64 ∨ [px0, px1, px2, px3] = [qx0, qx1, qx2, qx3] then 0#64 else 1#64) →
      L.length = 8 →
      (pt ≠ 0#64 → qt ≠ 0#64 → [px0, px1, px2, px3] ≠ [qx0, qx1, qx2, qx3] →
        L = Accel.curveAddL Sp1.pallasP 4 [px0, px1, px2, px3, py0, py1, py2, py3] [qx0, qx1, qx2, qx3, qy0, qy1, qy2, qy3]) →
      Region a0 (tag :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 38 := hstk.frame 38 (by decide)
  -- the frame: the two affine points copied ([0, 0x40), [0x40, 0x80)), the two `sp1_lib`
  -- points ([0x80, 0xc8), [0xc8, 0x110)), saved registers
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 8 := hokW.sub' 0 8 (by decide) (by bv_omega)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xf0#64) 8 := hokW.sub' 8 8 (by decide) (by bv_omega)
  have hokPt : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 1 := hokW.sub' 16 1 (by decide) (by bv_omega)
  have hokPx : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa8#64) 8 := hokW.sub' 17 8 (by decide) (by bv_omega)
  have hokQt : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 1 := hokW.sub' 25 1 (by decide) (by bv_omega)
  have hokQx : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 8 := hokW.sub' 26 8 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokW.sub' 34 4 (by decide) (by bv_omega)
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0x130#64) 8 s
  obtain ⟨FB, hFB, hFBl⟩ := Region.exists_junk (sp - 0xf0#64) 8 s
  obtain ⟨FPt, hFPt, hFPtl⟩ := Region.exists_junk (sp - 0xb0#64) 1 s
  obtain ⟨FPx, hFPx, hFPxl⟩ := Region.exists_junk (sp - 0xa8#64) 8 s
  obtain ⟨FQt, hFQt, hFQtl⟩ := Region.exists_junk (sp - 0x68#64) 1 s
  obtain ⟨FQx, hFQx, hFQxl⟩ := Region.exists_junk (sp - 0x60#64) 8 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x130#64, 38), (a0, 9)] s
  have hlo := hstk.lo
  sym_exec [memcmp4_spec, pallas_add_spec]
  · -- `P` invalid
    have h1 := beq_iff_eq.mp hbr1
    sym_close (hk _ _ _)
    all_goals first
      | rfl
      | exact (if_pos (Or.inl h1)).symm
      | (intro h; exact absurd h1 h)
  · -- `Q` invalid
    have h3 := beq_iff_eq.mp hbr3
    sym_close (hk _ _ _)
    all_goals first
      | rfl
      | exact (if_pos (Or.inr (Or.inl h3))).symm
      | (intro _ h; exact absurd h3 h)
  · -- the `x` coordinates agree
    rw [sext32_add_zero _ post49_5] at v50_def
    have hx : [px0, px1, px2, px3] = [qx0, qx1, qx2, qx3] := post49_4.mp (by rw [v50_def]; exact beq_iff_eq.mp hbr51)
    sym_close (hk _ _ _)
    all_goals first
      | rfl
      | exact (if_pos (Or.inr (Or.inr hx))).symm
      | (intro _ _ h; exact absurd hx h)
  · -- the accelerated addition
    rw [sext32_add_zero _ post49_5] at v50_def
    have hx : [px0, px1, px2, px3] ≠ [qx0, qx1, qx2, qx3] := fun h => hbr51 (beq_iff_eq.mpr (by rw [← v50_def]; exact post49_4.mpr h))
    have h1 : pt ≠ 0#64 := fun h => hbr1 (beq_iff_eq.mpr h)
    have h3 : qt ≠ 0#64 := fun h => hbr3 (beq_iff_eq.mpr h)
    have hl : acc99_0.length = 8 := by
      rw [← acc99_0_def]; simp [Accel.curveAddL]
    sym_close (hk _ _ _)
    all_goals first
      | rfl
      | exact (if_neg (fun h => h.elim h1 (fun h' => h'.elim h3 hx))).symm
      | (intro _ _ _
         rw [← v107_def, ← v108_def, ← v109_def, ← v110_def, ← v115_def, ← v116_def, ← v117_def, ← v118_def,
           acc99_0_def]
         exact fold8 hl)

end Cases.Zip2005
