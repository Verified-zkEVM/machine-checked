/-
  Cases.Zip2005.FpInvert

  `Fp::invert`: `pow_vartime` with the exponent `p - 2`, over the four limbs
  of the exponent most significant first. Each limb is a loop of 64
  square-and-multiply steps (`Fp.sqmul`), proved by induction on the bits
  left; the accumulator lives at `sp+0x18`, the operands of the two mulmod
  calls a step makes at `sp+0x38 … sp+0x98`.
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Runtime.BlackBox
import Cases.Zip2005.Image.F_78028d04
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- The loop over limb 1 of `p - 2` (`s3`), at its body with `s9 = j`: bits
    `j-2, …, 0` are left. -/
theorem inv_loop3 {G : MachineState → Prop} {n : Nat} {P : Prop} (sp xp : Word) (x0 x1 x2 x3 : Word) :
    ∀ m j (t : MachineState) (A : Nat), j - 1 = m → 2 ≤ j → j ≤ 65 →
      t.pc = 0x78029050#64 → CodeAt F_78028d04.base F_78028d04.prog t →
      CodeAt F_7801bf5c.base F_7801bf5c.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      t.getReg .x2 = sp → t.getReg .x8 = 11037532056220336129#64 → t.getReg .x9 = xp →
      t.getReg .x18 = sp + 0x78#64 → t.getReg .x19 = 2469829653914515739#64 →
      t.getReg .x20 = 1#64 → t.getReg .x21 = 8127635680764926565#64 →
      t.getReg .x22 = 12438865661331504215#64 → t.getReg .x23 = 14933811601259063721#64 →
      t.getReg .x25 = BitVec.ofNat 64 j → t.getReg .x26 = 1#64 →
      t.getReg .x27 = 4611686018427387904#64 →
      A < Fp.p →
      Region (sp + 0x10#64) [2445952672640170197#64] t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x10#64) 1 →
      Region (sp + 0x18#64) (natToLeLimbs 4 A) t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x18#64) 4 →
      (∃ Wk : List Word, Wk.length = 12 ∧ Region (sp + 0x38#64) Wk t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x38#64) 12 →
      Region xp [x0, x1, x2, x3] t → RegionOk Ro.layout.textLo Ro.layout.textHi xp 4 →
      Disjoint (sp + 0x18#64) 4 (sp + 0x38#64) 12 → Disjoint (sp + 0x10#64) 1 (sp + 0x38#64) 12 →
      Disjoint (sp + 0x10#64) 1 (sp + 0x18#64) 4 → Disjoint xp 4 (sp + 0x38#64) 12 →
      Disjoint xp 4 (sp + 0x18#64) 4 →
      (∀ u, u.pc = 0x780291cc#64 → u.code = t.code →
        u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
        u.getReg .x2 = sp → u.getReg .x8 = 11037532056220336129#64 → u.getReg .x9 = xp →
        u.getReg .x18 = sp + 0x78#64 → u.getReg .x19 = 2469829653914515739#64 →
        u.getReg .x20 = 1#64 → u.getReg .x21 = 8127635680764926565#64 →
        u.getReg .x22 = 12438865661331504215#64 → u.getReg .x23 = 14933811601259063721#64 →
        Unchanged [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t u →
        Region (sp + 0x18#64) (natToLeLimbs 4
          (Fp.powBits (leLimbsToNat [x0, x1, x2, x3]) 2469829653914515739 (j - 1) A)) u →
        Fp.powBits (leLimbsToNat [x0, x1, x2, x3]) 2469829653914515739 (j - 1) A < Fp.p →
        SafeN G n P u) →
      SafeN G n P t := by
  intro m
  induction m with
  | zero => intro j t A hm hj; omega
  | succ m ih =>
    intro j t A hm hj hj' hpc hcode hcodeM hcw hsp h8 h9 h18 h19 h20 h21 h22 h23 h25 h26 h27
      hA hlo hoklo hacc hokacc hWex hokW hx hokx hd1 hd2 hd3 hd4 hd5 hk
    obtain ⟨Wk, hWl, hW⟩ := hWex
    obtain rfl : j = m + 2 := by omega
    have hAl : leLimbsToNat (natToLeLimbs 4 A) = A :=
      leLimbsToNat_natToLeLimbs 4 A (lt_trans hA Fp.p_lt)
    have hu := Unchanged.refl [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t
    sym_exec [uint256_mulmod_spec] stop [0x78029050, 0x780291cc]
    · -- bit clear, exit: bit 0 of the limb is set
      sym_close hk
      all_goals try (exact Fp.powBits_lt _ _ hA)
      all_goals sym_subst
      rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr50
      obtain rfl : m = 0 := by simp at hbr50; omega
      rw [Bn.bit_test 2469829653914515739 (by decide) (0 + 2) (by omega) (by omega),
          show 0 + 2 - 2 = 0 by omega] at hbr48
      exact absurd hbr48 (by decide)
    · -- bit clear, next bit
      sym_close ih (m + 1) _ (Fp.mul A A)
      all_goals sym_subst
      · rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr50; simp at hbr50; omega
      · rw [hx25, Bn.ofNat_pred (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega]
      · exact Fp.mul_lt _ _
      · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
      · rw [Bn.bit_test 2469829653914515739 (by decide) (m + 2) (by omega) (by omega),
          show m + 2 - 2 = m by omega] at hbr48
        have hbit : Nat.testBit 2469829653914515739 m = false := by
          revert hbr48; cases Nat.testBit 2469829653914515739 m <;> intro h <;> first | rfl | exact absurd h (by decide)
        intro u hp hc g3 g4 r2 r8 r9 r18 r19 r20 r21 r22 r23 hU hR _
        refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r8 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBits_lt _ _ hA)
        rw [show m + 2 - 1 = m + 1 by omega, Fp.powBits, hbit]
        rw [show m + 1 - 1 = m by omega] at hR
        rw [show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A false = Fp.mul A A from if_neg (by decide)]
        exact hR
    · -- bit set, exit
      sym_close hk
      all_goals try (exact Fp.powBits_lt _ _ hA)
      all_goals sym_subst
      rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr100
      obtain rfl : m = 0 := by simp at hbr100; omega
      rw [show 0 + 2 - 1 = 0 + 1 by omega, Fp.powBits, Fp.powBits,
        show Nat.testBit 2469829653914515739 0 = true by decide,
        show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A true =
          Fp.mul (Fp.mul A A) (leLimbsToNat [x0, x1, x2, x3]) from if_pos rfl]
      simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
    · -- bit set, next bit
      sym_close ih (m + 1) _ (Fp.mul (Fp.mul A A) (leLimbsToNat [x0, x1, x2, x3]))
      all_goals sym_subst
      · rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr100; simp at hbr100; omega
      · rw [hx25, Bn.ofNat_pred (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega]
      · exact Fp.mul_lt _ _
      · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
      · rw [Bn.bit_test 2469829653914515739 (by decide) (m + 2) (by omega) (by omega),
          show m + 2 - 2 = m by omega] at hbr48
        have hbit : Nat.testBit 2469829653914515739 m = true := by
          revert hbr48; cases Nat.testBit 2469829653914515739 m <;> intro h <;> first | rfl | exact absurd h (by decide)
        intro u hp hc g3 g4 r2 r8 r9 r18 r19 r20 r21 r22 r23 hU hR _
        refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r8 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBits_lt _ _ hA)
        rw [show m + 2 - 1 = m + 1 by omega, Fp.powBits, hbit]
        rw [show m + 1 - 1 = m by omega] at hR
        rw [show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A true =
          Fp.mul (Fp.mul A A) (leLimbsToNat [x0, x1, x2, x3]) from if_pos rfl]
        exact hR

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- The loop over limb 0 of `p - 2` (`s10`), at its body with `s9 = j`: bits
    `j-2, …, 0` are left. -/
theorem inv_loop4 {G : MachineState → Prop} {n : Nat} {P : Prop} (sp xp : Word) (x0 x1 x2 x3 : Word) :
    ∀ m j (t : MachineState) (A : Nat), j - 1 = m → 2 ≤ j → j ≤ 65 →
      t.pc = 0x780291fc#64 → CodeAt F_78028d04.base F_78028d04.prog t →
      CodeAt F_7801bf5c.base F_7801bf5c.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      t.getReg .x2 = sp → t.getReg .x8 = 11037532056220336129#64 → t.getReg .x9 = xp →
      t.getReg .x18 = sp + 0x78#64 → t.getReg .x19 = 2469829653914515739#64 →
      t.getReg .x20 = 1#64 → t.getReg .x21 = 8127635680764926565#64 →
      t.getReg .x22 = 12438865661331504215#64 → t.getReg .x23 = 14933811601259063721#64 →
      t.getReg .x25 = BitVec.ofNat 64 j → t.getReg .x26 = 11037532056220336127#64 →
      t.getReg .x27 = 4611686018427387904#64 →
      A < Fp.p →
      Region (sp + 0x10#64) [2445952672640170197#64] t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x10#64) 1 →
      Region (sp + 0x18#64) (natToLeLimbs 4 A) t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x18#64) 4 →
      (∃ Wk : List Word, Wk.length = 12 ∧ Region (sp + 0x38#64) Wk t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x38#64) 12 →
      Region xp [x0, x1, x2, x3] t → RegionOk Ro.layout.textLo Ro.layout.textHi xp 4 →
      Disjoint (sp + 0x18#64) 4 (sp + 0x38#64) 12 → Disjoint (sp + 0x10#64) 1 (sp + 0x38#64) 12 →
      Disjoint (sp + 0x10#64) 1 (sp + 0x18#64) 4 → Disjoint xp 4 (sp + 0x38#64) 12 →
      Disjoint xp 4 (sp + 0x18#64) 4 →
      (∀ u, u.pc = 0x78029378#64 → u.code = t.code →
        u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
        u.getReg .x2 = sp → u.getReg .x8 = 11037532056220336129#64 → u.getReg .x9 = xp →
        u.getReg .x18 = sp + 0x78#64 → u.getReg .x19 = 2469829653914515739#64 →
        u.getReg .x20 = 1#64 → u.getReg .x21 = 8127635680764926565#64 →
        u.getReg .x22 = 12438865661331504215#64 → u.getReg .x23 = 14933811601259063721#64 →
        Unchanged [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t u →
        Region (sp + 0x18#64) (natToLeLimbs 4
          (Fp.powBits (leLimbsToNat [x0, x1, x2, x3]) 11037532056220336127 (j - 1) A)) u →
        Fp.powBits (leLimbsToNat [x0, x1, x2, x3]) 11037532056220336127 (j - 1) A < Fp.p →
        SafeN G n P u) →
      SafeN G n P t := by
  intro m
  induction m with
  | zero => intro j t A hm hj; omega
  | succ m ih =>
    intro j t A hm hj hj' hpc hcode hcodeM hcw hsp h8 h9 h18 h19 h20 h21 h22 h23 h25 h26 h27
      hA hlo hoklo hacc hokacc hWex hokW hx hokx hd1 hd2 hd3 hd4 hd5 hk
    obtain ⟨Wk, hWl, hW⟩ := hWex
    obtain rfl : j = m + 2 := by omega
    have hAl : leLimbsToNat (natToLeLimbs 4 A) = A :=
      leLimbsToNat_natToLeLimbs 4 A (lt_trans hA Fp.p_lt)
    have hu := Unchanged.refl [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t
    sym_exec [uint256_mulmod_spec] stop [0x780291fc, 0x78029378]
    · -- bit clear, exit: bit 0 of the limb is set
      sym_close hk
      all_goals try (exact Fp.powBits_lt _ _ hA)
      all_goals sym_subst
      rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr51
      obtain rfl : m = 0 := by simp at hbr51; omega
      rw [Bn.bit_test 11037532056220336127 (by decide) (0 + 2) (by omega) (by omega),
          show 0 + 2 - 2 = 0 by omega] at hbr48
      exact absurd hbr48 (by decide)
    · -- bit clear, next bit
      sym_close ih (m + 1) _ (Fp.mul A A)
      all_goals sym_subst
      · rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr51; simp at hbr51; omega
      · rw [hx25, Bn.ofNat_pred (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega]
      · exact Fp.mul_lt _ _
      · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
      · rw [Bn.bit_test 11037532056220336127 (by decide) (m + 2) (by omega) (by omega),
          show m + 2 - 2 = m by omega] at hbr48
        have hbit : Nat.testBit 11037532056220336127 m = false := by
          revert hbr48; cases Nat.testBit 11037532056220336127 m <;> intro h <;> first | rfl | exact absurd h (by decide)
        intro u hp hc g3 g4 r2 r8 r9 r18 r19 r20 r21 r22 r23 hU hR _
        refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r8 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBits_lt _ _ hA)
        rw [show m + 2 - 1 = m + 1 by omega, Fp.powBits, hbit]
        rw [show m + 1 - 1 = m by omega] at hR
        rw [show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A false = Fp.mul A A from if_neg (by decide)]
        exact hR
    · -- bit set, exit
      sym_close hk
      all_goals try (exact Fp.powBits_lt _ _ hA)
      all_goals sym_subst
      rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr101
      obtain rfl : m = 0 := by simp at hbr101; omega
      rw [show 0 + 2 - 1 = 0 + 1 by omega, Fp.powBits, Fp.powBits,
        show Nat.testBit 11037532056220336127 0 = true by decide,
        show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A true =
          Fp.mul (Fp.mul A A) (leLimbsToNat [x0, x1, x2, x3]) from if_pos rfl]
      simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
    · -- bit set, next bit
      sym_close ih (m + 1) _ (Fp.mul (Fp.mul A A) (leLimbsToNat [x0, x1, x2, x3]))
      all_goals sym_subst
      · rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr101; simp at hbr101; omega
      · rw [hx25, Bn.ofNat_pred (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega]
      · exact Fp.mul_lt _ _
      · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
      · rw [Bn.bit_test 11037532056220336127 (by decide) (m + 2) (by omega) (by omega),
          show m + 2 - 2 = m by omega] at hbr48
        have hbit : Nat.testBit 11037532056220336127 m = true := by
          revert hbr48; cases Nat.testBit 11037532056220336127 m <;> intro h <;> first | rfl | exact absurd h (by decide)
        intro u hp hc g3 g4 r2 r8 r9 r18 r19 r20 r21 r22 r23 hU hR _
        refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r8 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBits_lt _ _ hA)
        rw [show m + 2 - 1 = m + 1 by omega, Fp.powBits, hbit]
        rw [show m + 1 - 1 = m by omega] at hR
        rw [show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A true =
          Fp.mul (Fp.mul A A) (leLimbsToNat [x0, x1, x2, x3]) from if_pos rfl]
        exact hR

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- The loop over limb 2 of `p - 2`, which is zero: squarings only. The body,
    at `s0 = j`, has bits `j-2, …, 0` left. -/
theorem inv_loop2 {G : MachineState → Prop} {n : Nat} {P : Prop} (sp xp : Word) (x0 x1 x2 x3 : Word) :
    ∀ m j (t : MachineState) (A : Nat), j - 1 = m → 2 ≤ j → j ≤ 65 →
      t.pc = 0x78028f7c#64 → CodeAt F_78028d04.base F_78028d04.prog t →
      CodeAt F_7801bf5c.base F_7801bf5c.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      t.getReg .x2 = sp → t.getReg .x8 = BitVec.ofNat 64 j → t.getReg .x9 = xp →
      t.getReg .x18 = sp + 0x78#64 → t.getReg .x19 = 2469829653914515739#64 →
      t.getReg .x20 = 1#64 → t.getReg .x21 = 8127635680764926565#64 →
      t.getReg .x22 = 12438865661331504215#64 → t.getReg .x23 = 14933811601259063721#64 →
      t.getReg .x24 = 1#64 → t.getReg .x25 = 1#64 → t.getReg .x26 = 11037532056220336129#64 →
      t.getReg .x27 = 4611686018427387904#64 →
      A < Fp.p →
      Region (sp + 0x10#64) [2445952672640170197#64] t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x10#64) 1 →
      Region (sp + 0x18#64) (natToLeLimbs 4 A) t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x18#64) 4 →
      (∃ Wk : List Word, Wk.length = 12 ∧ Region (sp + 0x38#64) Wk t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x38#64) 12 →
      Disjoint (sp + 0x18#64) 4 (sp + 0x38#64) 12 → Disjoint (sp + 0x10#64) 1 (sp + 0x38#64) 12 →
      Disjoint (sp + 0x10#64) 1 (sp + 0x18#64) 4 →
      (∀ u, u.pc = 0x78029028#64 → u.code = t.code →
        u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
        u.getReg .x2 = sp → u.getReg .x9 = xp →
        u.getReg .x18 = sp + 0x78#64 → u.getReg .x19 = 2469829653914515739#64 →
        u.getReg .x20 = 1#64 → u.getReg .x21 = 8127635680764926565#64 →
        u.getReg .x22 = 12438865661331504215#64 → u.getReg .x23 = 14933811601259063721#64 →
        Unchanged [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t u →
        Region (sp + 0x18#64) (natToLeLimbs 4
          (Fp.powBits (leLimbsToNat [x0, x1, x2, x3]) 0 (j - 1) A)) u →
        Fp.powBits (leLimbsToNat [x0, x1, x2, x3]) 0 (j - 1) A < Fp.p →
        SafeN G n P u) →
      SafeN G n P t := by
  intro m
  induction m with
  | zero => intro j t A hm hj; omega
  | succ m ih =>
    intro j t A hm hj hj' hpc hcode hcodeM hcw hsp h8 h9 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
      hA hlo hoklo hacc hokacc hWex hokW hd1 hd2 hd3 hk
    obtain ⟨Wk, hWl, hW⟩ := hWex
    obtain rfl : j = m + 2 := by omega
    have hAl : leLimbsToNat (natToLeLimbs 4 A) = A :=
      leLimbsToNat_natToLeLimbs 4 A (lt_trans hA Fp.p_lt)
    have hu := Unchanged.refl [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t
    sym_exec [uint256_mulmod_spec] stop [0x78028f7c, 0x78029028]
    · -- exit
      sym_close hk
      all_goals try (exact Fp.powBits_lt _ _ hA)
      all_goals sym_subst
      rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr46
      obtain rfl : m = 0 := by simp at hbr46; omega
      rw [show 0 + 2 - 1 = 0 + 1 by omega, Fp.powBits, Fp.powBits, Nat.zero_testBit,
        show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A false = Fp.mul A A from if_neg (by decide)]
      simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
    · -- next bit
      sym_close ih (m + 1) _ (Fp.mul A A)
      all_goals sym_subst
      · rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr46; simp at hbr46; omega
      · rw [hx8, Bn.ofNat_pred (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega]
      · exact Fp.mul_lt _ _
      · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
      · intro u hp hc g3 g4 r2 r9 r18 r19 r20 r21 r22 r23 hU hR _
        refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBits_lt _ _ hA)
        rw [show m + 2 - 1 = m + 1 by omega, Fp.powBits, Nat.zero_testBit]
        rw [show m + 1 - 1 = m by omega] at hR
        rw [show Fp.sqmul (leLimbsToNat [x0, x1, x2, x3]) A false = Fp.mul A A from if_neg (by decide)]
        exact hR

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- The loop over limb 3 of `p - 2`, which is `2^62`, at its body with
    `s9 = j` and the started flag `s4 = f`: `pow_vartime` proper
    (`Fp.powBitsV`), since the first set bit is in this limb. -/
theorem inv_loop1 {G : MachineState → Prop} {n : Nat} {P : Prop} (sp xp : Word) (x0 x1 x2 x3 : Word) :
    ∀ m j (t : MachineState) (A : Nat) (f : Bool), j - 1 = m → 2 ≤ j → j ≤ 65 →
      (f = false → 64 ≤ j) →
      t.pc = 0x78028dd4#64 → CodeAt F_78028d04.base F_78028d04.prog t →
      CodeAt F_7801bf5c.base F_7801bf5c.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      t.getReg .x2 = sp → t.getReg .x8 = 11037532056220336129#64 → t.getReg .x9 = xp →
      t.getReg .x18 = sp + 0x78#64 → t.getReg .x19 = 2469829653914515739#64 →
      t.getReg .x20 = BitVec.ofNat 64 f.toNat → t.getReg .x21 = 8127635680764926565#64 →
      t.getReg .x22 = 12438865661331504215#64 → t.getReg .x23 = 14933811601259063721#64 →
      t.getReg .x24 = 1#64 → t.getReg .x25 = BitVec.ofNat 64 j → t.getReg .x26 = 64#64 →
      t.getReg .x27 = 4611686018427387904#64 →
      A < Fp.p →
      Region (sp + 0x10#64) [2445952672640170197#64] t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x10#64) 1 →
      Region (sp + 0x18#64) (natToLeLimbs 4 A) t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x18#64) 4 →
      (∃ Wk : List Word, Wk.length = 12 ∧ Region (sp + 0x38#64) Wk t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x38#64) 12 →
      Region xp [x0, x1, x2, x3] t → RegionOk Ro.layout.textLo Ro.layout.textHi xp 4 →
      Disjoint (sp + 0x18#64) 4 (sp + 0x38#64) 12 → Disjoint (sp + 0x10#64) 1 (sp + 0x38#64) 12 →
      Disjoint (sp + 0x10#64) 1 (sp + 0x18#64) 4 → Disjoint xp 4 (sp + 0x38#64) 12 →
      Disjoint xp 4 (sp + 0x18#64) 4 →
      (∀ u, u.pc = 0x78028f50#64 → u.code = t.code →
        u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
        u.getReg .x2 = sp → u.getReg .x9 = xp →
        u.getReg .x18 = sp + 0x78#64 → u.getReg .x19 = 2469829653914515739#64 →
        u.getReg .x20 = 1#64 → u.getReg .x21 = 8127635680764926565#64 →
        u.getReg .x22 = 12438865661331504215#64 → u.getReg .x23 = 14933811601259063721#64 →
        Unchanged [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t u →
        Region (sp + 0x18#64) (natToLeLimbs 4
          (Fp.powBitsV (leLimbsToNat [x0, x1, x2, x3]) 4611686018427387904 (j - 1) A f)) u →
        Fp.powBitsV (leLimbsToNat [x0, x1, x2, x3]) 4611686018427387904 (j - 1) A f < Fp.p →
        SafeN G n P u) →
      SafeN G n P t := by
  intro m
  induction m with
  | zero => intro j t A f hm hj; omega
  | succ m ih =>
    intro j t A f hm hj hj' hf hpc hcode hcodeM hcw hsp h8 h9 h18 h19 h20 h21 h22 h23 h24 h25 h26
      h27 hA hlo hoklo hacc hokacc hWex hokW hx hokx hd1 hd2 hd3 hd4 hd5 hk
    obtain ⟨Wk, hWl, hW⟩ := hWex
    obtain rfl : j = m + 2 := by omega
    have hAl : leLimbsToNat (natToLeLimbs 4 A) = A :=
      leLimbsToNat_natToLeLimbs 4 A (lt_trans hA Fp.p_lt)
    have hu := Unchanged.refl [(sp + 0x18#64, 4), (sp + 0x38#64, 12)] t
    cases f
    · -- not started: `j` is 65 or 64
      obtain rfl | rfl : m = 63 ∨ m = 62 := by have := hf rfl; omega
      · simp only [Bool.toNat_false] at h20
        sym_exec [uint256_mulmod_spec] stop [0x78028dd4, 0x78028f50]
        sym_close ih 64 _ A false
        · intro u hp hc g3 g4 r2 r9 r18 r19 r20 r21 r22 r23 hU hR _
          refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBitsV_lt _ _ _ hA)
          rw [show 63 + 2 - 1 = 63 + 1 from rfl, Fp.powBitsV_clear A false (by rw [Fp.testBit_2pow62]; decide), if_neg (by decide)]
          rw [show 64 - 1 = 63 from rfl] at hR
          exact hR
      · simp only [Bool.toNat_false] at h20
        sym_exec [uint256_mulmod_spec] stop [0x78028dd4, 0x78028f50]
        sym_close ih 63 _ (Fp.mul A (leLimbsToNat [x0, x1, x2, x3])) true
        all_goals sym_subst
        · exact Fp.mul_lt _ _
        · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
        · intro u hp hc g3 g4 r2 r9 r18 r19 r20 r21 r22 r23 hU hR _
          refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBitsV_lt _ _ _ hA)
          rw [show 62 + 2 - 1 = 62 + 1 from rfl, Fp.powBitsV_set A false (by rw [Fp.testBit_2pow62]; decide), if_neg (by decide)]
          rw [show 63 - 1 = 62 from rfl] at hR
          exact hR
    · simp only [Bool.toNat_true] at h20
      sym_exec [uint256_mulmod_spec] stop [0x78028dd4, 0x78028f50]
      · sym_close hk
        all_goals try (exact Fp.powBitsV_lt _ _ _ hA)
        all_goals sym_subst
        rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr47
        obtain rfl : m = 0 := by simp at hbr47; omega
        rw [show 0 + 2 - 1 = 0 + 1 from rfl, Fp.powBitsV_clear A true (by rw [Fp.testBit_2pow62]; decide),
          if_pos rfl]
        simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
      · sym_close ih (m + 1) _ (Fp.mul A A) true
        all_goals sym_subst
        · rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr47; simp at hbr47; omega
        · intro h; cases h
        · rw [hx25, Bn.ofNat_pred (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega]
        · exact Fp.mul_lt _ _
        · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
        · have hm62 : m ≠ 62 := by rw [Bn.ne_lit (m + 2) 64 (by omega) (by omega)] at hbr45; simp at hbr45; omega
          intro u hp hc g3 g4 r2 r9 r18 r19 r20 r21 r22 r23 hU hR _
          refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBitsV_lt _ _ _ hA)
          rw [show m + 2 - 1 = m + 1 by omega, Fp.powBitsV_clear A true (by rw [Fp.testBit_2pow62]; simpa using hm62), if_pos rfl]
          rw [show m + 1 - 1 = m by omega] at hR
          exact hR
      · sym_subst
        rw [Bn.ne_lit (m + 2) 64 (by omega) (by omega)] at hbr45
        rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr98
        simp at hbr45 hbr98; omega
      · sym_close ih (m + 1) _ (Fp.mul (Fp.mul A A) (leLimbsToNat [x0, x1, x2, x3])) true
        all_goals sym_subst
        · rw [Bn.ult_dec (m + 2) (by omega) (by omega)] at hbr98; simp at hbr98; omega
        · intro h; cases h
        · rw [hx25, Bn.ofNat_pred (m + 2) (by omega) (by omega), show m + 2 - 1 = m + 1 by omega]
        · exact Fp.mul_lt _ _
        · simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hAl]; rfl
        · have hm62 : m = 62 := by rw [Bn.ne_lit (m + 2) 64 (by omega) (by omega)] at hbr45; simp at hbr45; omega
          intro u hp hc g3 g4 r2 r9 r18 r19 r20 r21 r22 r23 hU hR _
          refine hk u hp (hc.trans hcode) (g3.trans hx3) (g4.trans hx4) r2 r9 r18 r19 r20 r21 r22 r23 (hunch.trans hU) ?_ (Fp.powBitsV_lt _ _ _ hA)
          rw [show m + 2 - 1 = m + 1 by omega, Fp.powBitsV_set A true (by rw [Fp.testBit_2pow62, hm62]; rfl), if_pos rfl]
          rw [show m + 1 - 1 = m by omega] at hR
          exact hR

theorem ult_one (x : Word) : x.ult 1#64 = decide (x = 0#64) := by
  rw [BitVec.ult_eq_decide]
  congr 1
  apply propext
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [Bn.toNat_ofNat'] at *; omega
  · intro h; subst h; decide

theorem leLimbs4_eq_zero (x0 x1 x2 x3 : Word) :
    leLimbsToNat [x0, x1, x2, x3] = 0 ↔ x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64 := by
  simp only [leLimbsToNat_cons, leLimbsToNat_nil]
  have e : ∀ x : Word, x = 0#64 ↔ x.toNat = 0 := fun x =>
    ⟨fun h => by subst h; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
  rw [e x0, e x1, e x2, e x3]
  omega

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 10000 in
/-- `Fp::invert`: `CtOption { value: x^(p-2), is_some: x ≠ 0 }` at `a0`. -/
theorem fp_invert_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word) (x0 x1 x2 x3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x78028d04#64) (hcode : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x110 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hokx : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x110#64) 34 a0 5) (hd1 : Disjoint (sp - 0x110#64) 34 a1 4)
    (hd : Disjoint a0 5 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x110#64, 34), (a0, 5)] s t →
      Region a0 (natToLeLimbs 4 (Fp.invert (leLimbsToNat [x0, x1, x2, x3])) ++
        [replaceByte O[4]! 0 (if leLimbsToNat [x0, x1, x2, x3] = 0 then 0#8 else 1#8)]) t →
      SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x100#64) 2 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0xf0#64) 1 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0xe8#64) 4 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0xc8#64) 12 s
  obtain ⟨F4, hF4, hF4l⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  obtain ⟨FB, hFB, hFBl⟩ := Region.exists_junk (sp - 0x110#64) 2 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 34 := hstk.frame 34 (by decide)
  have hokF0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x100#64) 2 := hokF.sub' 2 2 (by decide) (by bv_omega)
  have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xf0#64) 1 := hokF.sub' 4 1 (by decide) (by bv_omega)
  have hokF2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe8#64) 4 := hokF.sub' 5 4 (by decide) (by bv_omega)
  have hokF3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xc8#64) 12 := hokF.sub' 9 12 (by decide) (by bv_omega)
  have hokF4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 21 13 (by decide) (by bv_omega)
  have hokFB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 2 := hokF.sub' 0 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x110#64, 34), (a0, 5)] s
  have hstkB : StackOk Ro.layout 0x10 (sp + 18446744073709551360#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp + 18446744073709551360#64).toNat = sp.toNat - 256 := by
      rw [BitVec.toNat_add, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  have L1 := fun t => inv_loop1 (G := G) (n := n) (P := P) (sp - 256#64) a1 x0 x1 x2 x3 64 65 t Fp.R false rfl
    (by decide) (by decide) (fun _ => by decide)
  have L2 := fun t A => inv_loop2 (G := G) (n := n) (P := P) (sp - 256#64) a1 x0 x1 x2 x3 64 65 t A rfl
    (by decide) (by decide)
  have L3 := fun t A => inv_loop3 (G := G) (n := n) (P := P) (sp - 256#64) a1 x0 x1 x2 x3 64 65 t A rfl
    (by decide) (by decide)
  have L4 := fun t A => inv_loop4 (G := G) (n := n) (P := P) (sp - 256#64) a1 x0 x1 x2 x3 64 65 t A rfl
    (by decide) (by decide)
  sym_exec [uint256_mulmod_spec, black_box_spec, L1, L2, L3, L4]
  sym_close hk
  sym_subst
  rw [show ∀ (a b c d e : Word), [a, b, c, d, e] = [a, b, c, d] ++ [e] from fun _ _ _ _ _ => rfl,
    cells4]
  refine congrArg₂ (· ++ ·) rfl ?_
  · -- the `is_some` byte: `x ≠ 0`
    refine congrArg (fun b => [replaceByte O[4]! 0 b]) ?_
    simp only [leLimbs4_eq_zero, ult_one]
    by_cases h0 : x0 = 0#64 <;> by_cases h1 : x1 = 0#64 <;> by_cases h2 : x2 = 0#64 <;>
      by_cases h3 : x3 = 0#64 <;>
      simp only [h0, h1, h2, h3, decide_true, decide_false, and_true,
        and_false, if_true, if_false, Bool.false_eq_true] <;> decide

end Cases.Zip2005
