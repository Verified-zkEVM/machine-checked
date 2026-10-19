import Cases.Zip2005.Runtime.BlackBox
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Image.F_780239bc
import Cases.Zip2005.Image.Ro

/-!
# `IncompletePoint::from(Ep)` (sinsemilla)

The point is copied (`memcpy` 0x60) and the `is_valid` byte set to `black_box(1)`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem incomplete_from_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 : Word)
    (hpc : s.pc = 0x780239bc#64) (hcode : CodeAt F_780239bc.base F_780239bc.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hS : Region a1 [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hO : Region a0 [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12] s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 13)
    (hd0 : Disjoint (sp - 0x30#64) 6 a0 13) (hd1 : Disjoint (sp - 0x30#64) 6 a1 12)
    (he1 : Disjoint a0 13 a1 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6), (a0, 13)] s t →
      Region a0 [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, replaceByte o12 0 1#8] t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokW.sub' 2 4 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x30#64, 6), (a0, 13)] s
  have hlo := hstk.lo
  sym_exec [black_box_spec, memcpy96_spec]
  sym_close hk
  all_goals first | rfl | decide | (sym_subst; rfl)

end Cases.Zip2005
