/-
  Cases.Zip2005.ScalarMul

  `pasta_curves::sp1_pallas::zkvm::mul`: double-and-add over the 255 low bits
  of the scalar's canonical bytes, on `sp1_lib`'s nine-doubleword affine points.
  The accumulator starts at a fixed point `Q` (read-only data) and is offset
  by `-Q` at the end, so that the loop never adds the identity. Each round adds
  the base into a copy, `limbs_ref`s both (a panic on the identity), selects
  with a mask on the bit, forces the tag to 1, and doubles the base.
-/

import Cases.Zip2005.Curve.Pallas
import Cases.Zip2005.Curve.ToAffine
import Cases.Zip2005.Image.F_78031be8
import Cases.Zip2005.Image.F_780360e0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-- One round of the loop on `(acc, base)` with bit `b`. -/
def mulStep (b : Bool) (acc base : List Word) : List Word × List Word :=
  (1#64 :: (if b then (completeAddW acc base).drop 1 else acc.drop 1), doubleW base)

/-- `n` rounds from bit `i`. -/
def mulLoop (bits : Nat → Bool) : Nat → Nat → List Word → List Word → List Word × List Word
  | _, 0, acc, base => (acc, base)
  | i, n + 1, acc, base =>
    mulLoop bits (i + 1) n (mulStep (bits i) acc base).1 (mulStep (bits i) acc base).2

/-- No round of the loop meets the identity (which would panic in `limbs_ref`). -/
def mulOk (bits : Nat → Bool) : Nat → Nat → List Word → List Word → Prop
  | _, 0, _, _ => True
  | i, n + 1, acc, base =>
    (completeAddW acc base)[0]! ≠ 0 ∧
      mulOk bits (i + 1) n (mulStep (bits i) acc base).1 (mulStep (bits i) acc base).2

theorem length_mulLoop (bits : Nat → Bool) :
    ∀ n i (acc base : List Word), acc.length = 9 → base.length = 9 →
      (mulLoop bits i n acc base).1.length = 9 ∧ (mulLoop bits i n acc base).2.length = 9
  | 0, _, _, _, ha, hb => ⟨ha, hb⟩
  | n + 1, i, acc, base, ha, hb => by
    refine length_mulLoop bits n (i + 1) _ _ ?_ (length_doubleW hb)
    simp only [mulStep, List.length_cons]
    split
    · rw [List.length_drop, length_completeAddW ha hb]
    · rw [List.length_drop, ha]

/-- Bit `i` of the little-endian scalar bytes in `S`. -/
def scalarBit (S : List Word) (i : Nat) : Bool :=
  (extractByte S[i / 64]! (i / 8 % 8)).getLsbD (i % 8)

theorem and7 (i : Nat) : (BitVec.ofNat 64 i &&& 7#64).toNat % 64 = i % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bitW (S : List Word) (i : Nat) (hi : i < 18446744073709551616) :
    BitVec.zeroExtend 64 (extractByte S[i % 18446744073709551616 / 8 / 8]! (i % 18446744073709551616 / 8 % 8)) >>>
      ((BitVec.ofNat 64 i &&& 7#64).toNat % 64) &&& 1#64 = if scalarBit S i then 1#64 else 0#64 := by
  rw [and7, Nat.mod_eq_of_lt hi, Nat.div_div_eq_div_mul]
  unfold scalarBit
  generalize extractByte S[i / (8 * 8)]! (i / 8 % 8) = b
  have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize i % 8 = k at hk ⊢
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  by_cases h0 : j = 0
  · subst h0
    have hk64 : k < 64 := by omega
    cases h : b.getLsbD k <;> simp [h, hk64]
  · cases h : b.getLsbD k <;> simp [h0]

theorem sel_bit (x y : Word) (b : Bool) :
    (x &&& -(if b then 1#64 else 0#64) ||| y &&& ((if b then 1#64 else 0#64) + 18446744073709551615#64)) =
      if b then x else y := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [show -(0#64) = 0#64 from rfl, BitVec.and_zero, BitVec.zero_or, BitVec.zero_add,
      show (18446744073709551615#64 : Word) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
  · simp only [if_true]
    rw [show -(1#64) = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      show (1#64 : Word) + 18446744073709551615#64 = 0#64 by decide, BitVec.and_zero, BitVec.or_zero]
theorem acc_step (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Word) {base : List Word} (hbl : base.length = 9)
    (b : Bool) :
    [1#64, if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[1]! else a1,
      if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[2]! else a2,
      if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[3]! else a3,
      if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[4]! else a4,
      if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[5]! else a5,
      if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[6]! else a6,
      if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[7]! else a7,
      if b then (completeAddW [a0, a1, a2, a3, a4, a5, a6, a7, a8] base)[8]! else a8] =
      (mulStep b [a0, a1, a2, a3, a4, a5, a6, a7, a8] base).1 := by
  have hT := length_completeAddW (p := [a0, a1, a2, a3, a4, a5, a6, a7, a8]) rfl hbl
  cases b
  · rfl
  · simp only [mulStep, if_true, drop1_9 hT]

theorem base_step {base : List Word} (hbl : base.length = 9) (b : Bool) (acc : List Word) :
    [(doubleW base)[0]!, (doubleW base)[1]!, (doubleW base)[2]!, (doubleW base)[3]!,
      (doubleW base)[4]!, (doubleW base)[5]!, (doubleW base)[6]!, (doubleW base)[7]!,
      (doubleW base)[8]!] = (mulStep b acc base).2 :=
  fold9 (length_doubleW hbl)

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 10000 in
/-- The loop at its body (`0x78031ef8`) with `a0 = i` and `m` rounds left, up to
    its exit (`0x78032034`). -/
theorem mul_loop {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (sp : Word) (S : List Word) (c : Word → Option Instr)
    (g3 g4 g8 g24 g25 g26 g27 : Word)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = c →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u) :
    ∀ m i (t : MachineState) (acc base : List Word), i + m = 255 → 1 ≤ m →
      acc.length = 9 → base.length = 9 →
      t.pc = 0x78031ef8#64 → t.code = c → CodeAt F_78031be8.base F_78031be8.prog t →
      CodeAt F_78035fe0.base F_78035fe0.prog t → CodeAt F_7803f54c.base F_7803f54c.prog t →
      CodeAt F_7801b4d8.base F_7801b4d8.prog t → CodeAt F_7801bf3c.base F_7801bf3c.prog t →
      CodeAt F_7801bf4c.base F_7801bf4c.prog t → CodeAt F_780360c8.base F_780360c8.prog t →
      CodeAt F_780360e0.base F_780360e0.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      RoImage Ro.layout t → Run.HeapAt L t →
      t.getReg .x2 = sp → StackOk Ro.layout 0x20 sp →
      t.getReg .x3 = g3 → t.getReg .x4 = g4 → t.getReg .x8 = g8 → t.getReg .x24 = g24 →
      t.getReg .x25 = g25 → t.getReg .x26 = g26 → t.getReg .x27 = g27 →
      t.getReg .x10 = BitVec.ofNat 64 i → t.getReg .x18 = 1#64 →
      t.getReg .x19 = sp + 0x130#64 → t.getReg .x21 = 255#64 →
      Region (sp + 0xa0#64) base t → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa0#64) 9 →
      Region (sp + 0xe8#64) acc t → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xe8#64) 9 →
      Region (sp + 0x130#64) S t → S.length = 4 → RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x130#64) 4 →
      (∃ T : List Word, T.length = 9 ∧ Region (sp + 0x150#64) T t) →
      RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x150#64) 9 →
      (∃ F : List Word, F.length = 4 ∧ Region (sp - 0x20#64) F t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 →
      (∀ u, u.pc = 0x78032034#64 → u.code = c →
        u.getReg .x2 = sp → u.getReg .x3 = g3 → u.getReg .x4 = g4 →
        u.getReg .x8 = g8 → u.getReg .x24 = g24 → u.getReg .x25 = g25 → u.getReg .x26 = g26 →
        u.getReg .x27 = g27 →
        Unchanged [(sp - 0x20#64, 4), (sp + 0xa0#64, 9), (sp + 0xe8#64, 9), (sp + 0x150#64, 9)] t u →
        (mulLoop (scalarBit S) i m acc base).2.length = 9 →
        (mulLoop (scalarBit S) i m acc base).1.length = 9 →
        Region (sp + 0xa0#64) (mulLoop (scalarBit S) i m acc base).2 u →
        Region (sp + 0xe8#64) (mulLoop (scalarBit S) i m acc base).1 u →
        mulOk (scalarBit S) i m acc base → RoImage Ro.layout u → Run.HeapAt L u →
        SafeN G n P u) →
      SafeN G n P t := by
  intro m
  induction m with
  | zero => intro i t acc base hm hm1; omega
  | succ m ih =>
    intro i t acc base hm hm1 hal hbl hpc hc hcode hcodeA hcodeCmp hcodeCpy hcodeAdd hcodeDbl
      hcodeD hcodeL hcw hro hheap hsp hstk h3 h4 h8 h24 h25 h26 h27 h10 h18 h19 h21 hB hokB hA hokA hS hSl
      hokS hTex hokT hFex hokF hk
    obtain ⟨T, hTl, hT⟩ := hTex
    obtain ⟨F, hFl, hF⟩ := hFex
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, rfl⟩ : ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8,
        acc = [a0, a1, a2, a3, a4, a5, a6, a7, a8] := by
      match acc, hal with
      | [a0, a1, a2, a3, a4, a5, a6, a7, a8], _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    obtain ⟨s0, s1, s2, s3, rfl⟩ : ∃ s0 s1 s2 s3, S = [s0, s1, s2, s3] := by
      match S, hSl with
      | [s0, s1, s2, s3], _ => exact ⟨_, _, _, _, rfl⟩
    have hi : i < 255 := by omega
    have hsucc : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add i 1).symm
    have hu := Unchanged.refl [(sp - 0x20#64, 4), (sp + 0xa0#64, 9), (sp + 0xe8#64, 9),
      (sp + 0x150#64, 9)] t
    sym_exec [complete_add_assign_spec, double_spec, hpanic] stop [0x78031ef8, 0x78032034]
    · sym_close ih (i + 1) _
      all_goals sym_subst
      all_goals (rw [Bn.ne_lit (i + 1) 255 (by omega) (by omega)] at hbr135
                 simp only [decide_eq_true_eq] at hbr135)
      · omega
      · intro u hp hc r2 r3 r4 r8 r24 r25 r26 r27 hU hlb hla hRb hRa hok hro' hh'
        simp only [bitW _ i (by omega : i < 18446744073709551616), sel_bit, fold9 hbl,
          acc_step _ _ _ _ _ _ _ _ _ hbl,
          base_step hbl (scalarBit [s0, s1, s2, s3] i) [a0, a1, a2, a3, a4, a5, a6, a7, a8]]
          at hRa hRb hok hbr77 hla hlb
        exact hk u hp hc r2 r3 r4 r8 r24 r25 r26 r27 (hunch.trans hU) hlb hla hRb hRa
          ⟨by simpa using hbr77, hok⟩ hro' hh'
    · sym_close hk
      all_goals sym_subst
      all_goals (rw [Bn.ne_lit (i + 1) 255 (by omega) (by omega)] at hbr135
                 simp only [decide_eq_true_eq, Decidable.not_not] at hbr135
                 obtain rfl : m = 0 := by omega)
      · exact (length_mulLoop _ 1 i _ _ rfl hbl).2
      · exact (length_mulLoop _ 1 i _ _ rfl hbl).1
      · rw [fold9 hbl]; exact base_step hbl _ _
      · rw [bitW _ i (by omega)]
        simp only [sel_bit]
        rw [fold9 hbl]; exact acc_step _ _ _ _ _ _ _ _ _ hbl _
      · rw [fold9 hbl] at hbr77
        exact ⟨by simpa using hbr77, trivial⟩

end Cases.Zip2005
