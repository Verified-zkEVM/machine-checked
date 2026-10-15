/-
  Cases.Zip2005.AddAssign

  `sp1_lib`'s `AffinePoint::add_assign` and `limbs_ref` on the nine-doubleword Pallas
  layout (tag, then `x` and `y` as four little-endian limbs each). Both panic on the
  identity (tag `0`); `add_assign` otherwise tail-calls the `PALLAS_ADD` precompile on
  the limbs.
-/

import Cases.Zip2005.Curve.Pallas
import Cases.Zip2005.Image.F_78035f88
import Cases.Zip2005.Image.F_780360e0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- `AffinePoint::add_assign` on non-identity points. -/
def addAssignW (p q : List Word) : List Word :=
  p[0]! :: Accel.curveAddL Sp1.pallasP 4 (p.drop 1) (q.drop 1)

theorem length_addAssignW (p q : List Word) : (addAssignW p q).length = 9 := by
  simp [addAssignW, length_curveAddL]

theorem add_assign_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} {sp0 : Word} (s : MachineState) (ra a0 a1 : Word)
    (p q : List Word) (hpl : p.length = 9) (hql : q.length = 9)
    (hpc : s.pc = 0x78035f88#64) (hcode : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp0 : s.getReg .x2 = sp0) (hstk0 : StackOk Ro.layout 0 sp0)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a0 p s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hq : Region a1 q s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 9)
    (hd : Disjoint a0 9 a1 9)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(a0, 9)] s t → p[0]! ≠ 0 → q[0]! ≠ 0 →
      Region a0 (addAssignW p q) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(a0, 9)] s
  sym_exec [pallas_add_spec, hpanic]
  all_goals sym_close hk
  all_goals sym_subst
  all_goals first
    | simpa using hbr1
    | simpa using hbr3
    | rw [addAssignW, drop1_9 hpl, drop1_9 hql, fold8 (length_curveAddL _ _)]

theorem limbs_ref_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} {sp0 : Word} (s : MachineState) (ra a0 : Word) (p : List Word)
    (hpl : p.length = 9)
    (hpc : s.pc = 0x780360e0#64) (hcode : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp0 : s.getReg .x2 = sp0) (hstk0 : StackOk Ro.layout 0 sp0)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0)
    (hp : Region a0 p s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [] s t → p[0]! ≠ 0 → Region a0 p t → t.getReg .x10 = a0 + 8#64 → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [] s
  sym_exec [hpanic]
  all_goals sym_close hk
  all_goals sym_subst
  all_goals simpa using hbr1

end Cases.Zip2005
