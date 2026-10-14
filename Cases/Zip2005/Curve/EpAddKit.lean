/-
  Cases.Zip2005.EpAddKit

  Small-context lemmas for `Ep::add`: the guest's byte-flag idioms (`z == 0` and `u1 == u2` as
  `sltiu`/`and` chains) as `bw (decide _)`, how a branch on such a flag reads, and the three
  twelve-limb output shapes (`(X, Y, Z)` copied through, the identity, `Ep::double`'s result).
-/

import Cases.Zip2005.Curve.EpModel
import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Curve.IsOnCurve

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

theorem bw_beq_zero (b : Bool) : ((bw b == 0#64) = true) ↔ b = false := by
  cases b <;> decide

theorem bw_bne_one (b : Bool) : ((bw b != 1#64) = true) ↔ b = false := by
  cases b <;> decide

/-- `beqz` on a flag: the branch taken means the property fails. -/
theorem flag_ne_of_beq_zero {P : Prop} [Decidable P] {r : Word} (h : r = bw (decide P))
    (hbr : (r == 0#64) = true) : ¬P := by
  rw [h] at hbr; exact decide_eq_false_iff_not.mp ((bw_beq_zero _).mp hbr)

theorem flag_of_not_beq_zero {P : Prop} [Decidable P] {r : Word} (h : r = bw (decide P))
    (hbr : ¬(r == 0#64) = true) : P := by
  rw [h] at hbr; by_contra hn; exact hbr ((bw_beq_zero _).mpr (decide_eq_false hn))

/-- `bne r, 1` on a flag: the branch taken means the property fails. -/
theorem flag_ne_of_bne_one {P : Prop} [Decidable P] {r : Word} (h : r = bw (decide P))
    (hbr : (r != 1#64) = true) : ¬P := by
  rw [h] at hbr; exact decide_eq_false_iff_not.mp ((bw_bne_one _).mp hbr)

theorem flag_of_not_bne_one {P : Prop} [Decidable P] {r : Word} (h : r = bw (decide P))
    (hbr : ¬(r != 1#64) = true) : P := by
  rw [h] at hbr; by_contra hn; exact hbr ((bw_bne_one _).mpr (decide_eq_false hn))

/-- `is_identity`: four `sltiu x, 1` folded with `and`, byte-narrowed at each step. -/
theorem zero4_flag {z0 z1 z2 z3 v18 v23 v24 v28 v29 v34 v35 v39 v40 v45 v46 v50 v51 v55 : Word}
    (h18 : (if z0.ult 1#64 = true then 1#64 else 0#64) = v18)
    (h23 : BitVec.zeroExtend 64 (BitVec.truncate 8 v18) = v23)
    (h24 : (if z1.ult 1#64 = true then 1#64 else 0#64) = v24)
    (h28 : BitVec.zeroExtend 64 (BitVec.truncate 8 v24) &&& v23 = v28)
    (h29 : v28 &&& 255#64 = v29)
    (h34 : BitVec.zeroExtend 64 (BitVec.truncate 8 v29) = v34)
    (h35 : (if z2.ult 1#64 = true then 1#64 else 0#64) = v35)
    (h39 : BitVec.zeroExtend 64 (BitVec.truncate 8 v35) &&& v34 = v39)
    (h40 : v39 &&& 255#64 = v40)
    (h45 : BitVec.zeroExtend 64 (BitVec.truncate 8 v40) = v45)
    (h46 : (if z3.ult 1#64 = true then 1#64 else 0#64) = v46)
    (h50 : BitVec.zeroExtend 64 (BitVec.truncate 8 v46) &&& v45 = v50)
    (h51 : v50 &&& 255#64 = v51)
    (h55 : BitVec.zeroExtend 64 (BitVec.truncate 8 v51) &&& 255#64 = v55) :
    v55 = bw (decide (leLimbsToNat [z0, z1, z2, z3] = 0)) := by
  have hid : (z3 = 0#64 ∧ z2 = 0#64 ∧ z1 = 0#64 ∧ z0 = 0#64) ↔ leLimbsToNat [z0, z1, z2, z3] = 0 := by
    rw [limbs_zero4]; constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h3, h2, h1⟩
  subst h18 h23 h24 h28 h29 h34 h35 h39 h40 h45 h46 h50 h51 h55
  simp only [seqz_bw, bb_bw, and_bw, and255_bw, beq_zero_decide, ← Bool.decide_and]
  rw [decide_eq_decide.mpr hid]

/-- `ct_eq` of two limb vectors: four `xor; sltiu x, 1` folded with `and`. -/
theorem eq4_flag {a0 a1 a2 a3 b0 b1 b2 b3 x0 c0 e0 x1 c1 e1 f1 g1 x2 c2 e2 f2 g2 x3 c3 e3 f3 r : Word}
    (hx0 : a0 ^^^ b0 = x0) (hc0 : (if x0.ult 1#64 = true then 1#64 else 0#64) = c0)
    (he0 : BitVec.zeroExtend 64 (BitVec.truncate 8 c0) = e0)
    (hx1 : a1 ^^^ b1 = x1) (hc1 : (if x1.ult 1#64 = true then 1#64 else 0#64) = c1)
    (he1 : BitVec.zeroExtend 64 (BitVec.truncate 8 c1) &&& e0 = e1) (hf1 : e1 &&& 255#64 = f1)
    (hg1 : BitVec.zeroExtend 64 (BitVec.truncate 8 f1) = g1)
    (hx2 : a2 ^^^ b2 = x2) (hc2 : (if x2.ult 1#64 = true then 1#64 else 0#64) = c2)
    (he2 : BitVec.zeroExtend 64 (BitVec.truncate 8 c2) &&& g1 = e2) (hf2 : e2 &&& 255#64 = f2)
    (hg2 : BitVec.zeroExtend 64 (BitVec.truncate 8 f2) = g2)
    (hx3 : a3 ^^^ b3 = x3) (hc3 : (if x3.ult 1#64 = true then 1#64 else 0#64) = c3)
    (he3 : BitVec.zeroExtend 64 (BitVec.truncate 8 c3) &&& g2 = e3) (hf3 : e3 &&& 255#64 = f3)
    (hr : BitVec.zeroExtend 64 (BitVec.truncate 8 f3) &&& 255#64 = r) :
    r = bw (decide (leLimbsToNat [b0, b1, b2, b3] = leLimbsToNat [a0, a1, a2, a3])) := by
  subst hx0 hc0 he0 hx1 hc1 he1 hf1 hg1 hx2 hc2 he2 hf2 hg2 hx3 hc3 he3 hf3 hr
  simp only [seqz_bw, bb_bw, and_bw, and255_bw, xor_beq_zero, ← Bool.decide_and]
  rw [decide_eq_decide.mpr (limbs4_eq_iff b0 b1 b2 b3 a0 a1 a2 a3)]

/-- Twelve limbs written from a triple of canonical limb vectors. -/
theorem triple_limbs (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Word) :
    natToLeLimbs 4 (leLimbsToNat [a0, a1, a2, a3], leLimbsToNat [b0, b1, b2, b3],
        leLimbsToNat [c0, c1, c2, c3]).1 ++
      natToLeLimbs 4 (leLimbsToNat [a0, a1, a2, a3], leLimbsToNat [b0, b1, b2, b3],
        leLimbsToNat [c0, c1, c2, c3]).2.1 ++
      natToLeLimbs 4 (leLimbsToNat [a0, a1, a2, a3], leLimbsToNat [b0, b1, b2, b3],
        leLimbsToNat [c0, c1, c2, c3]).2.2 =
      [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3] := by
  have ea : natToLeLimbs 4 (leLimbsToNat [a0, a1, a2, a3]) = [a0, a1, a2, a3] :=
    natToLeLimbs_leLimbsToNat _
  have eb : natToLeLimbs 4 (leLimbsToNat [b0, b1, b2, b3]) = [b0, b1, b2, b3] :=
    natToLeLimbs_leLimbsToNat _
  have ec : natToLeLimbs 4 (leLimbsToNat [c0, c1, c2, c3]) = [c0, c1, c2, c3] :=
    natToLeLimbs_leLimbsToNat _
  show natToLeLimbs 4 (leLimbsToNat [a0, a1, a2, a3]) ++ natToLeLimbs 4 (leLimbsToNat [b0, b1, b2, b3]) ++
    natToLeLimbs 4 (leLimbsToNat [c0, c1, c2, c3]) = _
  rw [ea, eb, ec]; rfl

/-- The identity `(0, 0, 0)` as twelve limbs. -/
theorem zero_triple :
    natToLeLimbs 4 ((0, 0, 0) : Nat × Nat × Nat).1 ++ natToLeLimbs 4 ((0, 0, 0) : Nat × Nat × Nat).2.1 ++
      natToLeLimbs 4 ((0, 0, 0) : Nat × Nat × Nat).2.2 = List.replicate 12 0#64 := by
  decide

/-- `memset`'s result read back cell by cell. -/
theorem replicate_cells (A : List Word) (hA : List.replicate 12 0#64 = A) :
    [A[0]!, A[1]!, A[2]!, A[3]!, A[4]!, A[5]!, A[6]!, A[7]!, A[8]!, A[9]!, A[10]!, A[11]!] =
      List.replicate 12 0#64 := by
  subst hA; rfl

end Cases.Zip2005
