import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Image.F_78023d7c
import Cases.Zip2005.Image.Ro

/-!
# `Ep::conditional_select`

`subtle`'s xor-and-xor select on the twelve limbs of two points: `((b ^ a) & -choice) ^ a`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem conditional_select_spec {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word) (c : Bool)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : Word) (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x78023d7c#64) (hcode : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x20 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (ha3 : s.getReg .x13 = bw c)
    (hA : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hB : Region a2 [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11] s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x20#64) 4 a0 12) (hd1 : Disjoint (sp - 0x20#64) 4 a1 12)
    (hd2 : Disjoint (sp - 0x20#64) 4 a2 12)
    (he1 : Disjoint a0 12 a1 12) (he2 : Disjoint a0 12 a2 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x20#64, 4), (a0, 12)] s t →
      Region a0 [if c then q0 else p0, if c then q1 else p1, if c then q2 else p2, if c then q3 else p3, if c then q4 else p4, if c then q5 else p5, if c then q6 else p6, if c then q7 else p7, if c then q8 else p8, if c then q9 else p9, if c then q10 else p10, if c then q11 else p11] t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hstk.frame 4 (by decide)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hu := Unchanged.refl [(sp - 0x20#64, 4), (a0, 12)] s
  have hlo := hstk.lo
  sym_exec
  sym_close hk
  sym_subst
  simp only [sel_bw]

end Cases.Zip2005
