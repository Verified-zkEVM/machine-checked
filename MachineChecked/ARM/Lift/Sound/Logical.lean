/-
  MachineChecked.ARM.Lift.Sound.Logical

  The lift of AArch64 against arm64-semantics: the logical instructions, with an immediate
  and a shifted register, and the flags where the instruction sets them.

  ## Main results

  * `logical_run`: the operations of a logical instruction
  * `logicalImm_sound`, `logicalShift_sound`: the two instructions
-/

import MachineChecked.ARM.Lift.Sound.Basic

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- **A logical operation**, with its flags if it sets them. `a` and `b` are operands of the
    width. -/
theorem logical_run (h : Agree regs m s) (w : RegWidth) (op : Arm64.LogicalOp)
    {dst : Arm64.Reg} (hd : Wf dst) {a b : E}
    (hx : w = .W32 → a.eval regs = ((a.eval regs).setWidth 32).setWidth 64)
    (hy : w = .W32 → b.eval regs = ((b.eval regs).setWidth 32).setWidth 64) :
    ∃ os, ops.logical w op dst a b = some os ∧ ∃ r', run os regs m = some (r', m) ∧
      Agree r' m (
        let p := Arm64.evalLogical w op (a.eval regs) (b.eval regs) s.pstate
        match p.2 with
        | some ps => (s.writeReg w dst p.1).setPState ps
        | none => s.writeReg w dst p.1) := by
  refine ⟨_, rfl, ?_⟩
  generalize hxe : a.eval regs = x at hx
  generalize hye : b.eval regs = y at hy
  cases w
  · have hx := hx rfl
    have hy := hy rfl
    cases op
    case ANDS =>
      have := flags_run h hd (e := band a b) (en := bit (.reg .t0) 31) (ez := isZero (.reg .t0))
        (ec := num 0) (ev := num 0)
        (r := ((x &&& y).truncate 32).zeroExtend 64)
        (ps := { n := ((x &&& y).truncate 32).msb, z := (x &&& y).truncate 32 == 0#32,
                 c := false, v := false })
        (by simp only [eval_band, hxe, hye]; bv_decide)
        (fun R hs ht => by
          simp only [eval_bit, eval_reg, eval_isZero, eval_num, ht, flag]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide)
      simpa [Arm64.evalLogical, Arm64.State.writeReg, RegWidth.bits, setNZ, trunc] using this
    case BICS =>
      have := flags_run h hd (e := band a (z32 (bnot b))) (en := bit (.reg .t0) 31)
        (ez := isZero (.reg .t0)) (ec := num 0) (ev := num 0)
        (r := ((x &&& ~~~y).truncate 32).zeroExtend 64)
        (ps := { n := ((x &&& ~~~y).truncate 32).msb, z := (x &&& ~~~y).truncate 32 == 0#32,
                 c := false, v := false })
        (by simp only [eval_band, eval_z32, eval_bnot, hxe, hye]; bv_decide)
        (fun R hs ht => by
          simp only [eval_bit, eval_reg, eval_isZero, eval_num, ht, flag]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide)
      simpa [Arm64.evalLogical, Arm64.State.writeReg, RegWidth.bits, setNZ, trunc] using this
    all_goals
      refine result_run h hd ?_
      simp [hxe, hye, Arm64.evalLogical]
      try bv_decide
  · cases op
    case ANDS =>
      have := flags_run h hd (e := band a b) (en := bit (.reg .t0) 63) (ez := isZero (.reg .t0))
        (ec := num 0) (ev := num 0)
        (ps := { n := (x &&& y).msb, z := x &&& y == 0#64, c := false, v := false })
        (by simp [hxe, hye]; rfl)
        (fun R hs ht => by
          simp only [eval_bit, eval_reg, eval_isZero, eval_num, ht, flag]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide)
      simpa [Arm64.evalLogical, Arm64.State.writeReg, RegWidth.bits, setNZ, trunc] using this
    case BICS =>
      have := flags_run h hd (e := band a (bnot b)) (en := bit (.reg .t0) 63)
        (ez := isZero (.reg .t0)) (ec := num 0) (ev := num 0)
        (ps := { n := (x &&& ~~~y).msb, z := x &&& ~~~y == 0#64, c := false, v := false })
        (by simp [hxe, hye]; rfl)
        (fun R hs ht => by
          simp only [eval_bit, eval_reg, eval_isZero, eval_num, ht, flag]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide)
      simpa [Arm64.evalLogical, Arm64.State.writeReg, RegWidth.bits, setNZ, trunc] using this
    all_goals
      refine result_run h hd ?_
      simp [hxe, hye, Arm64.evalLogical]

/-- At 32 bits a logical operation reads the low half of its second operand. -/
theorem evalLogical_low (op : Arm64.LogicalOp) (x y : BitVec 64) (ps : Arm64.PState) :
    Arm64.evalLogical .W32 op x (y &&& 0xffffffff#64) ps = Arm64.evalLogical .W32 op x y ps := by
  cases op <;> simp [Arm64.evalLogical] <;> bv_decide

/-- **`and`, `orr`, `eor`, `ands` with an immediate.** -/
theorem logicalImm_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.LogicalOp)
    {dst rn : Arm64.Reg} (hd : Wf dst) (hn : Wf rn) (mask : BitVec 64) :
    ∃ os, ops.logical w op dst (rdw w rn)
        (.imm (if w = .W32 then mask &&& 0xffffffff#64 else mask)) = some os ∧
      ∃ r', run os regs m = some (r', m) ∧
        Agree r' m (Arm64.execLogicalImm w op dst rn mask s) := by
  obtain ⟨os, ho, r', h1, h2⟩ := logical_run h w op hd (rdw_width w rn)
    (b := .imm (if w = .W32 then mask &&& 0xffffffff#64 else mask))
    (fun hw => by subst hw; simp; bv_decide)
  refine ⟨os, ho, r', h1, ?_⟩
  rw [rdw_eval h w hn] at h2
  cases w
  · simp only [eval_imm, ite_true, evalLogical_low] at h2
    exact h2.advancePC
  · exact h2.advancePC

/-- **The logical instructions with a shifted register.** -/
theorem logicalShift_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.LogicalOp)
    {dst rn rm : Arm64.Reg} (hd : Wf dst) (hrn : Wf rn) (hrm : Wf rm) (ty : Arm64.ShiftType)
    {n : Nat} (hn : n < w.bits) :
    ∃ os, ops.logical w op dst (rdw w rn) (shifted w ty n rm) = some os ∧
      ∃ r', run os regs m = some (r', m) ∧
        Agree r' m (Arm64.execLogicalShift w op dst rn rm ty n s) := by
  have hb := shifted_eval h w ty hn hrm
  obtain ⟨os, ho, r', h1, h2⟩ := logical_run h w op hd (rdw_width w rn)
    (b := shifted w ty n rm) (fun hw => by rw [hb]; subst hw; simp [Arm64.shiftVal])
  refine ⟨os, ho, r', h1, ?_⟩
  rw [hb, rdw_eval h w hrn] at h2
  exact h2.advancePC

end MachineChecked.ARM.Lift
