/-
  Cases.Zip2005.Pallas

  `sp1_lib`'s affine Pallas points: nine doublewords, a tag (`0` for the
  identity) then `x` and `y` as four little-endian limbs each. The group law
  goes through the `PALLAS_ADD` / `PALLAS_DOUBLE` precompiles, with the special
  cases decided by comparing limbs.
-/

import Cases.Zip2005.Runtime.Memcmp
import Cases.Zip2005.Image.F_78035fe0
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.F_780360c8
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- `AffinePoint::complete_add_assign`, on the nine-doubleword layout. -/
def completeAddW (p q : List Word) : List Word :=
  if p[0]! = 0 then q
  else if q[0]! = 0 then p
  else if p.drop 1 = q.drop 1 then p[0]! :: Accel.curveDblL Sp1.pallasP 4 (p.drop 1)
  else if (p.drop 1).take 4 = (q.drop 1).take 4 then 0 :: p.drop 1
  else p[0]! :: Accel.curveAddL Sp1.pallasP 4 (p.drop 1) (q.drop 1)

theorem length_completeAddW {p q : List Word} (hpl : p.length = 9) (hql : q.length = 9) :
    (completeAddW p q).length = 9 := by
  unfold completeAddW
  split
  · exact hql
  split
  · exact hpl
  split
  · simp [length_curveDblL]
  split
  · simp [hpl]
  · simp [length_curveAddL]

theorem fold9 {xs : List Word} (h : xs.length = 9) :
    [xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[5]!, xs[6]!, xs[7]!, xs[8]!] = xs := by
  match xs, h with
  | [_, _, _, _, _, _, _, _, _], _ => rfl

theorem drop1_9 {xs : List Word} (h : xs.length = 9) :
    xs.drop 1 = [xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[5]!, xs[6]!, xs[7]!, xs[8]!] := by
  match xs, h with
  | [_, _, _, _, _, _, _, _, _], _ => rfl

/-- `memcmp`'s result, sign-extended and tested for zero, as `complete_add_assign` does. -/
theorem sext_branch_zero {x : Word} (h : BitVec.signExtend 64 (x.truncate 32) = x)
    (hb : (BitVec.signExtend 64 (BitVec.truncate 32 x + BitVec.truncate 32 0#64) == 0#64) = true) :
    x = 0 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.setWidth_zero, BitVec.add_zero, beq_iff_eq] at hb h
  rw [← h]; exact hb

theorem sext_branch_ne {x : Word} (h : BitVec.signExtend 64 (x.truncate 32) = x)
    (hb : ¬(BitVec.signExtend 64 (BitVec.truncate 32 x + BitVec.truncate 32 0#64) == 0#64) = true) :
    x ≠ 0 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.setWidth_zero, BitVec.add_zero, beq_iff_eq] at hb h
  intro hx; apply hb; rw [← h] at hx; exact hx

section cases
variable {p q : List Word} (hpl : p.length = 9) (hql : q.length = 9)
include hpl hql

theorem cadd_dbl (hp0 : p[0]! ≠ 0) (hq0 : q[0]! ≠ 0)
    (heq : [p[1]!, p[2]!, p[3]!, p[4]!, p[5]!, p[6]!, p[7]!, p[8]!] =
      [q[1]!, q[2]!, q[3]!, q[4]!, q[5]!, q[6]!, q[7]!, q[8]!]) :
    completeAddW p q = p[0]! :: Accel.curveDblL Sp1.pallasP 4
      [p[1]!, p[2]!, p[3]!, p[4]!, p[5]!, p[6]!, p[7]!, p[8]!] := by
  rw [completeAddW, if_neg hp0, if_neg hq0, drop1_9 hpl, drop1_9 hql, if_pos heq]

theorem cadd_neg (hp0 : p[0]! ≠ 0) (hq0 : q[0]! ≠ 0)
    (hne : [p[1]!, p[2]!, p[3]!, p[4]!, p[5]!, p[6]!, p[7]!, p[8]!] ≠
      [q[1]!, q[2]!, q[3]!, q[4]!, q[5]!, q[6]!, q[7]!, q[8]!])
    (hx : [p[1]!, p[2]!, p[3]!, p[4]!] = [q[1]!, q[2]!, q[3]!, q[4]!]) :
    completeAddW p q = [(0 : Word), p[1]!, p[2]!, p[3]!, p[4]!, p[5]!, p[6]!, p[7]!, p[8]!] := by
  rw [completeAddW, if_neg hp0, if_neg hq0, drop1_9 hpl, drop1_9 hql, if_neg hne]
  exact if_pos hx

theorem cadd_add (hp0 : p[0]! ≠ 0) (hq0 : q[0]! ≠ 0)
    (hne : [p[1]!, p[2]!, p[3]!, p[4]!, p[5]!, p[6]!, p[7]!, p[8]!] ≠
      [q[1]!, q[2]!, q[3]!, q[4]!, q[5]!, q[6]!, q[7]!, q[8]!])
    (hx : [p[1]!, p[2]!, p[3]!, p[4]!] ≠ [q[1]!, q[2]!, q[3]!, q[4]!]) :
    completeAddW p q = p[0]! :: Accel.curveAddL Sp1.pallasP 4
      [p[1]!, p[2]!, p[3]!, p[4]!, p[5]!, p[6]!, p[7]!, p[8]!]
      [q[1]!, q[2]!, q[3]!, q[4]!, q[5]!, q[6]!, q[7]!, q[8]!] := by
  rw [completeAddW, if_neg hp0, if_neg hq0, drop1_9 hpl, drop1_9 hql, if_neg hne]
  exact if_neg hx

end cases

set_option maxHeartbeats 20000000 in
theorem complete_add_assign_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word)
    (p q : List Word) (hpl : p.length = 9) (hql : q.length = 9)
    (hpc : s.pc = 0x78035fe0#64) (hcode : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x20 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a0 p s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hq : Region a1 q s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 9)
    (hd0 : Disjoint (sp - 0x20#64) 4 a0 9) (hd1 : Disjoint (sp - 0x20#64) 4 a1 9)
    (hd : Disjoint a0 9 a1 9)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x20#64, 4), (a0, 9)] s t → (completeAddW p q).length = 9 →
      Region a0 (completeAddW p q) t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hF, hFlen⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hstk.frame 4 (by decide)
  have hu := Unchanged.refl [(sp - 0x20#64, 4), (a0, 9)] s
  sym_exec [memcmp8_spec, memcmp4_spec, pallas_add_spec, pallas_double_spec]
  all_goals sym_close hk
  all_goals try exact length_completeAddW hpl hql
  all_goals sym_subst
  · -- `self` is the identity: `other` was copied over it
    rw [completeAddW, if_pos (by simpa using hbr6)]; exact fold9 hql
  · -- `other` is the identity
    rw [completeAddW, if_neg (by simpa using hbr6), if_pos (by simpa using hbr8)]; exact fold9 hpl
  · -- equal points: doubled
    replace hbr6 : p[0]! ≠ 0 := by simpa using hbr6
    replace hbr8 : q[0]! ≠ 0 := by simpa using hbr8
    rw [cadd_dbl hpl hql hbr6 hbr8 (post17_4.mp (sext_branch_zero post17_5 hbr19)),
      fold8 (length_curveDblL _)]
  · -- equal x, different points: the identity
    replace hbr6 : p[0]! ≠ 0 := by simpa using hbr6
    replace hbr8 : q[0]! ≠ 0 := by simpa using hbr8
    rw [cadd_neg hpl hql hbr6 hbr8 (fun h => sext_branch_ne post17_5 hbr19 (post17_4.mpr h))
      (post25_4.mp (sext_branch_zero post25_5 hbr27))]
    rfl
  · -- the general case: the precompile's chord
    replace hbr6 : p[0]! ≠ 0 := by simpa using hbr6
    replace hbr8 : q[0]! ≠ 0 := by simpa using hbr8
    rw [cadd_add hpl hql hbr6 hbr8 (fun h => sext_branch_ne post17_5 hbr19 (post17_4.mpr h))
      (fun h => sext_branch_ne post25_5 hbr27 (post25_4.mpr h)), fold8 (length_curveAddL _ _)]

/-- `AffinePoint::double`, on the nine-doubleword layout. -/
def doubleW (p : List Word) : List Word :=
  if p[0]! = 0 then p else p[0]! :: Accel.curveDblL Sp1.pallasP 4 (p.drop 1)

theorem length_doubleW {p : List Word} (hpl : p.length = 9) : (doubleW p).length = 9 := by
  unfold doubleW
  split
  · exact hpl
  · simp [length_curveDblL]

theorem double_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 : Word) (p : List Word)
    (hpl : p.length = 9)
    (hpc : s.pc = 0x780360c8#64) (hcode : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0)
    (hp : Region a0 p s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(a0, 9)] s t → (doubleW p).length = 9 → Region a0 (doubleW p) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(a0, 9)] s
  sym_exec [pallas_double_spec]
  all_goals sym_close hk
  all_goals try exact length_doubleW hpl
  all_goals sym_subst
  · rw [doubleW, if_pos (by simpa using hbr1)]; exact fold9 hpl
  · rw [doubleW, if_neg (by simpa using hbr1), drop1_9 hpl, fold8 (length_curveDblL _)]

end Cases.Zip2005
