/-
  MachineChecked.ARM.Lift.Sound.Move

  The lift of AArch64 against arm64-semantics: the instructions that move a value, an
  address, or one of two values by a condition.

  ## Main results

  * `cond_eval`: a condition is worth what the machine finds it to hold
  * `nop_sound`, `adr_sound`, `moveWide_sound`, `condSelect_sound`
-/

import MachineChecked.ARM.Lift.Sound.Basic

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- **A condition**: 1 if it holds of the machine's flags, 0 if not. -/
theorem cond_eval (h : Agree regs m s) (c : Arm64.CondCode) :
    (cond c).eval regs = flag (Arm64.ConditionHolds c s.pstate) := by
  obtain ⟨-, -, hn, hz, hc, hv, -⟩ := h
  cases c <;> simp only [cond, eval_reg, eval_flip, eval_band, eval_bor, eval_bxor, eval_num,
    hn, hz, hc, hv, Arm64.ConditionHolds] <;>
    cases s.pstate.n <;> cases s.pstate.z <;> cases s.pstate.c <;> cases s.pstate.v <;> decide

/-- **`nop`.** -/
theorem nop_sound (h : Agree regs m s) :
    ∃ r', run [] regs m = some (r', m) ∧ Agree r' m s.advancePC :=
  ⟨regs, rfl, h.advancePC⟩

/-- **`adr` and `adrp`.** -/
theorem adr_sound (h : Agree regs m s) {dst : Arm64.Reg} (hd : Wf dst) (page : Bool)
    (off : BitVec 64) :
    ∃ r', run (wr dst (.imm ((if page then s.pc &&& ~~~0xfff#64 else s.pc) + off))) regs m =
        some (r', m) ∧
      Agree r' m (s.writeReg64 dst
        ((if page then s.pc &&& 0xfffffffffffff000#64 else s.pc) + off)).advancePC := by
  obtain ⟨r', h1, h2⟩ := result_run h hd (e := .imm ((if page then s.pc &&& ~~~0xfff#64
    else s.pc) + off)) rfl
  exact ⟨r', h1, h2.advancePC⟩

/-- A 16-bit immediate at its place. -/
theorem ofNat_mul_pow (x : BitVec 16) (k : Nat) :
    BitVec.ofNat 64 (x.toNat * 2 ^ k) = x.zeroExtend 64 <<< k := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq]

/-- The mask of a 16-bit immediate at its place. -/
theorem mask_pow (k : Nat) : BitVec.ofNat 64 (0xffff * 2 ^ k) = 0xffff#64 <<< k :=
  ofNat_mul_pow 0xffff#16 k

/-- **`movz`, `movn`, `movk`**: the shift is 0, 16, 32 or 48, and below the width. -/
theorem moveWide_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.MoveWideOp)
    {dst : Arm64.Reg} (hd : Wf dst) (imm16 : BitVec 16) {hw : Nat}
    (hhw : hw = 0 ∨ hw = 16 ∨ (w = .W64 ∧ (hw = 32 ∨ hw = 48))) :
    ∃ r', run (wr dst (match op with
        | .MOVZ => num (imm16.toNat * 2 ^ hw)
        | .MOVN => trunc w (bnot (num (imm16.toNat * 2 ^ hw)))
        | .MOVK => bor (band (rdw w dst) (trunc w (bnot (num (0xffff * 2 ^ hw)))))
            (num (imm16.toNat * 2 ^ hw)))) regs m = some (r', m) ∧
      Agree r' m (Arm64.execMoveWide w op dst imm16 hw s) := by
  have hr := rdw_eval h w hd
  have hwd := rdw_width (regs := regs) w dst
  rw [hr] at hwd
  refine result_sound h hd w ?_
  have hv := ofNat_mul_pow imm16 hw
  have hm := mask_pow hw
  have e : ∀ o : Arm64.MoveWideOp, Expr.eval regs (match o with
      | .MOVZ => num (imm16.toNat * 2 ^ hw)
      | .MOVN => trunc w (bnot (num (imm16.toNat * 2 ^ hw)))
      | .MOVK => bor (band (rdw w dst) (trunc w (bnot (num (0xffff * 2 ^ hw)))))
          (num (imm16.toNat * 2 ^ hw))) =
      match o with
      | .MOVZ => imm16.zeroExtend 64 <<< hw
      | .MOVN => if w = .W32 then ((~~~(imm16.zeroExtend 64 <<< hw)).setWidth 32).setWidth 64
          else ~~~(imm16.zeroExtend 64 <<< hw)
      | .MOVK => s.readReg w dst &&& (if w = .W32 then
          ((~~~(0xffff#64 <<< hw)).setWidth 32).setWidth 64 else ~~~(0xffff#64 <<< hw)) |||
          imm16.zeroExtend 64 <<< hw := by
    intro o; cases o <;> simp only [eval_num, eval_trunc, eval_bnot, eval_bor, eval_band, hv, hm, hr]
  rw [e]
  clear e hv hm hr
  cases w
  · have hwd := hwd rfl
    generalize s.readReg .W32 dst = old at hwd
    rcases hhw with rfl | rfl | ⟨hc, -⟩
    · cases op <;> simp <;> bv_decide
    · cases op <;> simp <;> bv_decide
    · cases hc
  · generalize s.readReg .W64 dst = old
    generalize imm16.zeroExtend 64 = i
    rcases hhw with rfl | rfl | ⟨-, rfl | rfl⟩ <;> cases op <;> simp

/-- The bitwise choice between two values by a flag. -/
theorem choose_flag (t : Bool) (a b : BitVec 64) :
    b ^^^ ((a ^^^ b) &&& -flag t) = if t then a else b := by
  cases t <;> simp only [flag] <;> bv_decide

@[simp] theorem eval_choose (c a b : E) :
    (choose c a b).eval regs = b.eval regs ^^^ ((a.eval regs ^^^ b.eval regs) &&& -c.eval regs) :=
  rfl

/-- **`csel`, `csinc`, `csinv`, `csneg`.** -/
theorem condSelect_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.CondSelectOp)
    {dst rn rm : Arm64.Reg} (hd : Wf dst) (hrn : Wf rn) (hrm : Wf rm) (c : Arm64.CondCode) :
    ∃ r', run (wr dst (choose (cond c) (rdw w rn) (match op with
        | .CSEL => rdw w rm
        | .CSINC => trunc w (add (rdw w rm) (num 1))
        | .CSINV => trunc w (bnot (rdw w rm))
        | .CSNEG => trunc w (.un .neg (rdw w rm))))) regs m = some (r', m) ∧
      Agree r' m (Arm64.execCondSelect w op dst rn rm c s) := by
  refine result_sound h hd w ?_
  have hxw := rdw_width (regs := regs) w rn
  have hyw := rdw_width (regs := regs) w rm
  rw [eval_choose, cond_eval h c, choose_flag]
  rw [rdw_eval h w hrn] at hxw ⊢
  have hy := rdw_eval h w hrm
  generalize s.readReg w rn = x at hxw
  generalize s.readReg w rm = y at hy hyw
  cases Arm64.ConditionHolds c s.pstate <;> cases w <;> cases op <;>
    simp [hy, UnOp.eval, Expr.eval] <;> first | exact hxw rfl | (have := hyw rfl; bv_decide)

end MachineChecked.ARM.Lift
