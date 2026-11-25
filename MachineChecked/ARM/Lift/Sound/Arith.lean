/-
  MachineChecked.ARM.Lift.Sound.Arith

  The lift of AArch64 against arm64-semantics: multiplication, unsigned division and the
  shifts by a register.

  ## Main results

  * `dataProc3_sound`: the multiplications
  * `shiftv_sound`: the shifts by a register
  * `udiv_sound`: unsigned division. Signed division is not proved yet.
-/

import MachineChecked.ARM.Lift.Sound.Basic

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- The low half of a difference. -/
theorem setWidth32_sub (a b : BitVec 64) :
    (a - b).setWidth 32 = a.setWidth 32 - b.setWidth 32 := by
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ (by decide),
    BitVec.setWidth_neg_of_le (by decide), ← BitVec.sub_eq_add_neg]

/-- **`madd`, `msub`, and the long and the high multiplications.** The long and the high
    ones are of 64 bits. -/
theorem dataProc3_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.DataProc3Op)
    {dst rn rm ra : Arm64.Reg} (hd : Wf dst) (hrn : Wf rn) (hrm : Wf rm) (hra : Wf ra)
    (hw : w = .W64 ∨ op = .MADD ∨ op = .MSUB) :
    ∃ r', run (wr dst (match op with
        | .MADD => trunc w (add (rdw w ra) (.bin .mul (rdw w rn) (rdw w rm)))
        | .MSUB => trunc w (sub (rdw w ra) (.bin .mul (rdw w rn) (rdw w rm)))
        | .SMADDL => add (rd ra) (.bin .mul (s32 (rd rn)) (s32 (rd rm)))
        | .SMSUBL => sub (rd ra) (.bin .mul (s32 (rd rn)) (s32 (rd rm)))
        | .UMADDL => add (rd ra) (.bin .mul (z32 (rd rn)) (z32 (rd rm)))
        | .UMSUBL => sub (rd ra) (.bin .mul (z32 (rd rn)) (z32 (rd rm)))
        | .SMULH => .bin .mulh (rd rn) (rd rm)
        | .UMULH => .bin .mulhu (rd rn) (rd rm))) regs m = some (r', m) ∧
      Agree r' m (Arm64.execDataProc3 w op dst rn rm ra s) := by
  refine result_sound h hd w ?_
  have e1 := rd_eval h hrn; have e2 := rd_eval h hrm; have e3 := rd_eval h hra
  have f1 := rdw_eval h w hrn; have f2 := rdw_eval h w hrm; have f3 := rdw_eval h w hra
  cases w
  · rcases hw with hw | rfl | rfl
    · cases hw
    all_goals
      simp [Expr.eval, BinOp.eval, f1, f2, f3, Arm64.State.readReg, Arm64.State.readReg32,
        BitVec.setWidth_mul, BitVec.setWidth_add, setWidth32_sub]
  · cases op <;>
      simp [Expr.eval, BinOp.eval, e1, e2, e3, f1, f2, f3, Arm64.State.readReg,
        Arm64.State.readReg32]

/-- **The shifts by a register.** -/
theorem shiftv_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.DataProc2Op)
    {dst rn rm : Arm64.Reg} (hd : Wf dst) (hrn : Wf rn) (hrm : Wf rm)
    (hop : op ≠ .UDIV ∧ op ≠ .SDIV) :
    ∃ r', run (wr dst (
        let a := rdw w rn
        let amount := band (rdw w rm) (num (w.bits - 1))
        match op with
        | .UDIV => band (.bin .divu a (rdw w rm)) (.un .neg (nonZero (rdw w rm)))
        | .SDIV => trunc w (band (.bin .div (signed w a) (signed w (rdw w rm)))
            (.un .neg (nonZero (rdw w rm))))
        | .LSLV => trunc w (.bin .shl a amount)
        | .LSRV => .bin .lshr a amount
        | .ASRV => trunc w (.bin .ashr (signed w a) amount)
        | .RORV => trunc w (bor (.bin .lshr a amount)
            (.bin .shl a (band (sub (num w.bits) amount) (num (w.bits - 1))))))) regs m =
        some (r', m) ∧
      Agree r' m (Arm64.execDataProc2 w op dst rn rm s) := by
  refine result_sound h hd w ?_
  have f1 := rdw_eval h w hrn; have f2 := rdw_eval h w hrm
  have w1 := rdw_width (regs := regs) w rn; have w2 := rdw_width (regs := regs) w rm
  rw [f1] at w1; rw [f2] at w2
  generalize s.readReg w rn = x at f1 w1
  generalize s.readReg w rm = y at f2 w2
  cases w
  · have w1 := w1 rfl
    clear w2
    obtain ⟨k, hk, hk'⟩ : ∃ k : BitVec 64, y.toNat % 32 = k.toNat ∧ k < 32#64 :=
      ⟨BitVec.ofNat 64 (y.toNat % 32), by simp; omega, by
        rw [BitVec.lt_def, BitVec.toNat_ofNat]; simp; omega⟩
    have hkn : k.toNat < 32 := hk'
    have e : y.toNat &&& 31 = k.toNat := (Nat.and_two_pow_sub_one_eq_mod _ 5).trans hk
    obtain ⟨j, hj, e'⟩ : ∃ j : BitVec 64, j = (32#64 - k) &&& 31#64 ∧
        (2 ^ 64 - k.toNat + 32) % 2 ^ 64 &&& 31 = j.toNat := by
      refine ⟨_, rfl, ?_⟩
      rw [BitVec.toNat_and, BitVec.toNat_sub]; rfl
    obtain ⟨i, hi, e''⟩ : ∃ i : BitVec 64, i = 32#64 - k ∧ 32 - k.toNat = i.toNat :=
      ⟨_, rfl, by bv_omega⟩
    cases op
    case UDIV => exact absurd rfl hop.1
    case SDIV => exact absurd rfl hop.2
    all_goals
      simp [Expr.eval, BinOp.eval, f1, f2, RegWidth.bits, Arm64.shift32, e, hk, e', e'',
        BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hkn]
    all_goals bv_decide
  · clear w1 w2
    obtain ⟨k, hk, hk'⟩ : ∃ k : BitVec 64, y.toNat % 64 = k.toNat ∧ k < 64#64 :=
      ⟨BitVec.ofNat 64 (y.toNat % 64), by simp; omega, by
        rw [BitVec.lt_def, BitVec.toNat_ofNat]; simp; omega⟩
    have hkn : k.toNat < 64 := hk'
    have e : y.toNat &&& 63 = k.toNat := (Nat.and_two_pow_sub_one_eq_mod _ 6).trans hk
    obtain ⟨j, hj, e'⟩ : ∃ j : BitVec 64, j = (64#64 - k) &&& 63#64 ∧
        (2 ^ 64 - k.toNat + 64) % 2 ^ 64 &&& 63 = j.toNat := by
      refine ⟨_, rfl, ?_⟩
      rw [BitVec.toNat_and, BitVec.toNat_sub]; rfl
    obtain ⟨i, hi, e''⟩ : ∃ i : BitVec 64, i = 64#64 - k ∧ 64 - k.toNat = i.toNat :=
      ⟨_, rfl, by bv_omega⟩
    cases op
    case UDIV => exact absurd rfl hop.1
    case SDIV => exact absurd rfl hop.2
    all_goals
      simp [Expr.eval, BinOp.eval, f1, f2, RegWidth.bits, Arm64.shift64, e, hk, e', e'',
        BitVec.rotateRight, BitVec.rotateRightAux, Nat.mod_eq_of_lt hkn]
    all_goals bv_decide

/-- Division by zero gives zero, at 64 bits. -/
theorem udiv64 (x y : BitVec 64) :
    (if y == 0#64 then BitVec.allOnes 64 else x / y) &&& -(if (0#64).ult y then 1#64 else 0#64) =
      if y == 0#64 then 0#64 else x / y := by
  by_cases h : y = 0#64
  · simp [h]
  · have h1 : (0#64).ult y = true := by bv_decide
    simp only [h, h1, beq_iff_eq, ite_false, ite_true]
    generalize x / y = z
    bv_decide

/-- Division by zero gives zero, at 32 bits. -/
theorem udiv32 (x y : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64)
    (hy : y = (y.setWidth 32).setWidth 64) :
    (if y == 0#64 then BitVec.allOnes 64 else x / y) &&& -(if (0#64).ult y then 1#64 else 0#64) =
      (if y.setWidth 32 == 0#32 then 0#32 else x.setWidth 32 / y.setWidth 32).setWidth 64 := by
  rw [udiv64]
  by_cases h : y = 0#64
  · simp [h]
  · have h2 : y.setWidth 32 ≠ 0#32 := by bv_decide
    simp only [h, h2, beq_iff_eq, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [hx, hy]
    have := Nat.lt_of_le_of_lt (Nat.div_le_self (x.toNat % 4294967296) (y.toNat % 4294967296))
      (Nat.mod_lt _ (by decide : 0 < 4294967296))
    have hx' : x.toNat % 4294967296 % 18446744073709551616 = x.toNat % 4294967296 :=
      Nat.mod_eq_of_lt (by omega)
    have hy' : y.toNat % 4294967296 % 18446744073709551616 = y.toNat % 4294967296 :=
      Nat.mod_eq_of_lt (by omega)
    simp [hx', hy']
    exact (Nat.mod_eq_of_lt (Nat.lt_trans this (by decide : 4294967296 < 2 ^ 64))).symm

/-- **`udiv`.** -/
theorem udiv_sound (h : Agree regs m s) (w : RegWidth) {dst rn rm : Arm64.Reg} (hd : Wf dst)
    (hrn : Wf rn) (hrm : Wf rm) :
    ∃ r', run (wr dst (band (.bin .divu (rdw w rn) (rdw w rm))
        (.un .neg (nonZero (rdw w rm))))) regs m = some (r', m) ∧
      Agree r' m (Arm64.execDataProc2 w .UDIV dst rn rm s) := by
  refine result_sound h hd w ?_
  have f1 := rdw_eval h w hrn; have f2 := rdw_eval h w hrm
  have w1 := rdw_width (regs := regs) w rn; have w2 := rdw_width (regs := regs) w rm
  rw [f1] at w1; rw [f2] at w2
  generalize s.readReg w rn = x at f1 w1
  generalize s.readReg w rm = y at f2 w2
  have e : (band (.bin .divu (rdw w rn) (rdw w rm)) (.un .neg (nonZero (rdw w rm))) : E).eval
      regs = (if y == 0#64 then BitVec.allOnes 64 else x / y) &&&
        -(if (0#64).ult y then 1#64 else 0#64) := by
    simp [Expr.eval, BinOp.eval, UnOp.eval, nonZero, f1, f2]
  rw [e]
  cases w
  · rw [udiv32 x y (w1 rfl) (w2 rfl)]
    simp
  · rw [udiv64]

end MachineChecked.ARM.Lift
