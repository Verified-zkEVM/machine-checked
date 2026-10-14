/-
  Cases.Zip2005.EpModel

  The guest's Jacobian point arithmetic on Pallas as functions over `Nat` representatives
  (Montgomery form, `Cases.Zip2005.Fp`). `dblJ` is `pasta_curves`' `Ep::double` (`dbl-2009-l`,
  `a = 0`) followed by `conditional_select(&tmp, &identity, self.is_identity())`, where
  `identity` is `(0, 0, 0)` and `is_identity` is `z == 0`.
-/

import Cases.Zip2005.Field.FpSub

namespace Cases.Zip2005.Fp

/-- `Ep::double` on representatives. -/
def dblJ (X Y Z : Nat) : Nat × Nat × Nat :=
  let a := mul X X
  let b := mul Y Y
  let c := mul b b
  let d := add X b
  let d := mul d d
  let d := sub (sub d a) c
  let d := add d d
  let e := add (add a a) a
  let f := mul e e
  let z3 := mul Z Y
  let z3 := add z3 z3
  let x3 := sub f (add d d)
  let c := add c c
  let c := add c c
  let c := add c c
  let y3 := sub (mul e (sub d x3)) c
  if Z = 0 then (0, 0, 0) else (x3, y3, z3)

/-- The general case of `Ep::add` (`add-2007-bl`) from the six products the guest computes
first: `z1z1 = Z1²`, `z2z2 = Z2²`, `u1 = X1·z2z2`, `u2 = X2·z1z1`, `s1 = Y1·z2z2·Z2`,
`s2 = Y2·z1z1·Z1`. -/
def addJ_main (Z1 Z2 z1z1 z2z2 u1 u2 s1 s2 : Nat) : Nat × Nat × Nat :=
  let h := sub u2 u1
  let i := mul (add h h) (add h h)
  let j := mul h i
  let r := sub s2 s1
  let r := add r r
  let v := mul u1 i
  let x3 := sub (sub (sub (mul r r) j) v) v
  let s1 := mul s1 j
  let s1 := add s1 s1
  let y3 := sub (mul r (sub v x3)) s1
  let z3 := sub (sub (mul (add Z1 Z2) (add Z1 Z2)) z1z1) z2z2
  let z3 := mul z3 h
  (x3, y3, z3)

/-- `Ep::add` on representatives: identity operands copied through, equal `x`s double or give
the identity, otherwise `addJ_main`. -/
def addJ (X1 Y1 Z1 X2 Y2 Z2 : Nat) : Nat × Nat × Nat :=
  if Z1 = 0 then (X2, Y2, Z2) else
  if Z2 = 0 then (X1, Y1, Z1) else
  let z1z1 := mul Z1 Z1
  let z2z2 := mul Z2 Z2
  let u1 := mul X1 z2z2
  let u2 := mul X2 z1z1
  let s1 := mul (mul Y1 z2z2) Z2
  let s2 := mul (mul Y2 z1z1) Z1
  if u1 = u2 then (if s1 = s2 then dblJ X1 Y1 Z1 else (0, 0, 0)) else
  addJ_main Z1 Z2 z1z1 z2z2 u1 u2 s1 s2

/-- `addJ_main`, one equation per machine step. -/
theorem addJ_main_eq {Z1 Z2 z1z1 z2z2 u1 u2 s1 s2 h h2 i j r0 r v r2 x3a x3b x3 sj sj2 vx rvx y3 zz zz2 za zb z3 : Nat}
    (hh : h = sub u2 u1) (hh2 : h2 = add h h) (hi : i = mul h2 h2) (hj : j = mul h i)
    (hr0 : r0 = sub s2 s1) (hr : r = add r0 r0) (hv : v = mul u1 i) (hr2 : r2 = mul r r)
    (hx3a : x3a = sub r2 j) (hx3b : x3b = sub x3a v) (hx3 : x3 = sub x3b v)
    (hsj : sj = mul s1 j) (hsj2 : sj2 = add sj sj) (hvx : vx = sub v x3) (hrvx : rvx = mul r vx)
    (hy3 : y3 = sub rvx sj2) (hzz : zz = add Z1 Z2) (hzz2 : zz2 = mul zz zz) (hza : za = sub zz2 z1z1)
    (hzb : zb = sub za z2z2) (hz3 : z3 = mul zb h) :
    addJ_main Z1 Z2 z1z1 z2z2 u1 u2 s1 s2 = (x3, y3, z3) := by
  subst hh hh2 hi hj hr0 hr hv hr2 hx3a hx3b hx3 hsj hsj2 hvx hrvx hy3 hzz hzz2 hza hzb hz3
  rfl

theorem add_lt (a b : Nat) : add a b < p := Nat.mod_lt _ p_pos

/-- The five outcomes of `addJ`, one lemma each. -/
theorem addJ_z1_zero {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h : Z1 = 0) : addJ X1 Y1 Z1 X2 Y2 Z2 = (X2, Y2, Z2) := by
  simp only [addJ, if_pos h]

theorem addJ_z2_zero {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h1 : Z1 ≠ 0) (h2 : Z2 = 0) :
    addJ X1 Y1 Z1 X2 Y2 Z2 = (X1, Y1, Z1) := by
  simp only [addJ, if_neg h1, if_pos h2]

theorem addJ_identity {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0)
    (hu : mul X1 (mul Z2 Z2) = mul X2 (mul Z1 Z1))
    (hs : mul (mul Y1 (mul Z2 Z2)) Z2 ≠ mul (mul Y2 (mul Z1 Z1)) Z1) :
    addJ X1 Y1 Z1 X2 Y2 Z2 = (0, 0, 0) := by
  simp only [addJ, if_neg h1, if_neg h2, if_pos hu, if_neg hs]

theorem addJ_double {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0)
    (hu : mul X1 (mul Z2 Z2) = mul X2 (mul Z1 Z1))
    (hs : mul (mul Y1 (mul Z2 Z2)) Z2 = mul (mul Y2 (mul Z1 Z1)) Z1) :
    addJ X1 Y1 Z1 X2 Y2 Z2 = dblJ X1 Y1 Z1 := by
  simp only [addJ, if_neg h1, if_neg h2, if_pos hu, if_pos hs]

theorem addJ_general {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h1 : Z1 ≠ 0) (h2 : Z2 ≠ 0)
    (hu : mul X1 (mul Z2 Z2) ≠ mul X2 (mul Z1 Z1)) :
    addJ X1 Y1 Z1 X2 Y2 Z2 = addJ_main Z1 Z2 (mul Z1 Z1) (mul Z2 Z2) (mul X1 (mul Z2 Z2))
      (mul X2 (mul Z1 Z1)) (mul (mul Y1 (mul Z2 Z2)) Z2) (mul (mul Y2 (mul Z1 Z1)) Z1) := by
  simp only [addJ, if_neg h1, if_neg h2, if_neg hu]

end Cases.Zip2005.Fp
