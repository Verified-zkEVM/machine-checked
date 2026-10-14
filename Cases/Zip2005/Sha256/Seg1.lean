/-
  Cases.Zip2005.Sha256.Seg1: segment 1 of `compress256` (see `Proof/Sha256/Sha256Compress.lean`).
-/

import AsmVerif.RiscV.Sym
import Cases.Zip2005.Image.F_780361e0
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- Segment 1: `0x78037204` to `0x780381c4`. -/
theorem compress256_seg1 {G : MachineState → Prop} {n : Nat} {P : Prop} (u : MachineState) (ra sp st blk : Word) (r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : Word)
    (J1 J3 S B : List Word) (hJ1 : J1.length = 64) (hJ3 : J3.length = 34) (hS : S.length = 4) (hB : B.length = 8)
    (hpc : u.pc = 0x78037204#64) (hcode : CodeAt F_780361e0.base F_780361e0.prog u)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi u)
    (hsp : u.getReg .x2 = sp - 0x390#64) (hstk : StackOk Ro.layout 0x390 sp)
    (hF0 : Region (sp - 0x390#64) [st] u) (hF1 : Region (sp - 0x388#64) J1 u)
    (hF2 : Region (sp - 0x188#64) [blk + 64#64] u) (hF3 : Region (sp - 0x180#64) J3 u)
    (hF3b : Region (sp - 0x70#64) [blk] u) (hF4 : Region (sp - 0x68#64) [r27, r26, r25, r24, r23, r22, r21, r20, r19, r18, r9, r8, ra] u)
    (hRS : Region st S u) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi st 4)
    (hRB : Region blk B u) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi blk 8)
    (hd1 : Disjoint (sp - 0x390#64) 114 st 4) (hd2 : Disjoint (sp - 0x390#64) 114 blk 8)
    (hd3 : Disjoint st 4 blk 8)
    (hk : ∀ v, v.pc = 0x780381c4#64 → v.code = u.code → CodeAt F_780361e0.base F_780361e0.prog v → CodeWithin Ro.layout.textLo Ro.layout.textHi v →
      v.getReg .x2 = sp + 18446744073709550704#64 → v.getReg .x3 = u.getReg .x3 → v.getReg .x4 = u.getReg .x4 →
      Unchanged [(sp - 0x390#64, 114), (st, 4)] u v →
      Region (sp - 0x390#64) [st] v → (∃ J, J.length = 64 ∧ Region (sp - 0x388#64) J v) →
      Region (sp - 0x188#64) [blk + 64#64] v → (∃ J, J.length = 34 ∧ Region (sp - 0x180#64) J v) →
      Region (sp - 0x70#64) [blk] v → Region (sp - 0x68#64) [r27, r26, r25, r24, r23, r22, r21, r20, r19, r18, r9, r8, ra] v →
      (∃ S', S'.length = 4 ∧ Region st S' v) → (∃ B', B'.length = 8 ∧ Region blk B' v) → SafeN G n P v) :
    SafeN G n P u := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x390#64) 114 := hstk.frame 114 (by decide)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x390#64) 1 := hokW.sub' 0 1 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x388#64) 64 := hokW.sub' 1 64 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x188#64) 1 := hokW.sub' 65 1 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 34 := hokW.sub' 66 34 (by decide) (by bv_omega)
  have hok3b : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x70#64) 1 := hokW.sub' 100 1 (by decide) (by bv_omega)
  have hok4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokW.sub' 101 13 (by decide) (by bv_omega)
  have hlo := hstk.lo
  have hu := Unchanged.refl [(sp - 0x390#64, 114), (st, 4)] u
  sym_exec stop [0x780381c4]
  sym_close hk

end Cases.Zip2005
