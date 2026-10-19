import Cases.Zip2005.Runtime.BlackBox
import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Image.F_78023544
import Cases.Zip2005.Image.Ro

/-!
# `IncompletePoint::bottom` (sinsemilla)

Twelve zero words (`memset`) and the `is_valid` byte `black_box(0)`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem incomplete_bottom_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 : Word) (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 : Word)
    (hpc : s.pc = 0x78023544#64) (hcode : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = a0)
    (hO : Region a0 [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12] s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 13)
    (hd0 : Disjoint (sp - 0x30#64) 6 a0 13)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6), (a0, 13)] s t →
      Region a0 (List.replicate 12 0#64 ++ [replaceByte o12 0 0#8]) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokW.sub' 2 4 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x30#64, 6), (a0, 13)] s
  have hlo := hstk.lo
  sym_exec [black_box_spec, memset96_spec]
  sym_close hk
  all_goals first | rfl | decide | (sym_subst; rfl)

end Cases.Zip2005
