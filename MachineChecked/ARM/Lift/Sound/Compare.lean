/-
  MachineChecked.ARM.Lift.Sound.Compare

  The lift of AArch64 against arm64-semantics: the conditional comparisons, which set the
  flags of a comparison if a condition holds and given flags if not.

  ## Main results

  * `condCompare_run`: the operations of a conditional comparison
  * `condCompareReg_sound`, `condCompareImm_sound`: the two instructions
-/

import MachineChecked.ARM.Lift.Sound.AddSub
import MachineChecked.ARM.Lift.Sound.Move

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- A flag kept if the condition in `t1` holds, and set to `k` if not. -/
theorem keep_eval {R : Reg → BitVec 64} {f : Reg} {t p : Bool} (ht : R .t1 = flag t)
    (hf : R f = flag p) (k : Bool) :
    (choose (.reg .t1) (.reg f) (num (if k then 1 else 0)) : E).eval R =
      flag (if t then p else k) := by
  simp only [eval_choose, eval_reg, eval_num, ht, hf]
  cases t <;> cases p <;> cases k <;> decide

/-- **A conditional comparison.** `a` and `b` are operands of the width that read machine
    registers only. -/
theorem condCompare_run (h : Agree regs m s) (w : RegWidth) (isSub : Bool) {a b : E}
    (ha : Pure a) (hb : Pure b)
    (hx : w = .W32 → a.eval regs = ((a.eval regs).setWidth 32).setWidth 64)
    (hy : w = .W32 → b.eval regs = ((b.eval regs).setWidth 32).setWidth 64)
    (nzcv : BitVec 4) (c : Arm64.CondCode) :
    ∃ r', run (ops.condCompare w isSub a b nzcv c) regs m = some (r', m) ∧
      Agree r' m (s.setPState (if Arm64.ConditionHolds c s.pstate
        then addSubPs w isSub (a.eval regs) (b.eval regs) else Arm64.PState.ofBits4 nzcv)) := by
  generalize ht : Arm64.ConditionHolds c s.pstate = t
  generalize hps : addSubPs w isSub (a.eval regs) (b.eval regs) = ps
  let R0 := updReg (updReg regs .t1 (flag t)) .t0 (addSubVal w isSub (a.eval regs) (b.eval regs))
  let R1 := updReg R0 .nf (flag ps.n)
  let R2 := updReg R1 .zf (flag ps.z)
  let R3 := updReg R2 .cf (flag ps.c)
  let R4 := updReg R3 .vf (flag ps.v)
  let R5 := updReg R4 .nf (flag (if t then ps.n else nzcv.getLsbD 3))
  let R6 := updReg R5 .zf (flag (if t then ps.z else nzcv.getLsbD 2))
  let R7 := updReg R6 .cf (flag (if t then ps.c else nzcv.getLsbD 1))
  let R8 := updReg R7 .vf (flag (if t then ps.v else nzcv.getLsbD 0))
  have s0 : Same regs R0 := (Same.rfl.upd rfl _).upd rfl _
  have s1 : Same regs R1 := s0.upd rfl _
  have s2 : Same regs R2 := s1.upd rfl _
  have s3 : Same regs R3 := s2.upd rfl _
  have s8 : Same regs R8 := ((((s3.upd rfl _).upd rfl _).upd rfl _).upd rfl _).upd rfl _
  have F := fun R hs ht => addSubFlags_eval (R := R) w isSub ha hb hx hy hs ht
  simp only [hps] at F
  have ea : a.eval (updReg regs .t1 (flag t)) = a.eval regs := ha _ _ (Same.rfl.upd rfl _)
  have eb : b.eval (updReg regs .t1 (flag t)) = b.eval regs := hb _ _ (Same.rfl.upd rfl _)
  refine ⟨R8, ?_, ?_⟩
  · simp only [ops.condCompare, addSubFlags, setNZ, List.cons_append, List.nil_append, run_set,
      cond_eval h c, ht, addSubVal_eval, ea, eb]
    rw [(F R0 s0 rfl).1, (F R1 s1 rfl).2.1, (F R2 s2 rfl).2.2.1, (F R3 s3 rfl).2.2.2,
      keep_eval (R := R4) (f := .nf) (t := t) (p := ps.n) rfl rfl,
      keep_eval (R := R5) (f := .zf) (t := t) (p := ps.z) rfl rfl,
      keep_eval (R := R6) (f := .cf) (t := t) (p := ps.c) rfl rfl,
      keep_eval (R := R7) (f := .vf) (t := t) (p := ps.v) rfl rfl]
    rfl
  · have := h.of_same s8 (if t then ps else Arm64.PState.ofBits4 nzcv)
      (by cases t <;> rfl) (by cases t <;> rfl) (by cases t <;> rfl) (by cases t <;> rfl)
    exact this

/-- The machine's conditional comparison, by the flags of the comparison. -/
theorem execCondCompare_eq (w : RegWidth) (isSub isImm : Bool) (rn rm : Arm64.Reg)
    (rhs : BitVec 64) (nzcv : BitVec 4) (c : Arm64.CondCode) (s : Arm64.State) :
    Arm64.execCondCompare w isSub isImm rn rhs rm nzcv c s =
      (s.setPState (if Arm64.ConditionHolds c s.pstate
        then addSubPs w isSub (s.readReg w rn) (if isImm then rhs else s.readReg w rm)
        else Arm64.PState.ofBits4 nzcv)).advancePC := by
  cases ht : Arm64.ConditionHolds c s.pstate <;> cases w <;> cases isSub <;>
    simp [ht, Arm64.evalAddSub, addSubPs]

/-- **`ccmp`, `ccmn` with a register.** -/
theorem condCompareReg_sound (h : Agree regs m s) (w : RegWidth) (isSub : Bool)
    {rn rm : Arm64.Reg} (hrn : Wf rn) (hrm : Wf rm) (nzcv : BitVec 4) (c : Arm64.CondCode) :
    ∃ r', run (ops.condCompare w isSub (rdw w rn) (rdw w rm) nzcv c) regs m = some (r', m) ∧
      Agree r' m (Arm64.execCondCompare w isSub false rn 0#64 rm nzcv c s) := by
  obtain ⟨r', h1, h2⟩ := condCompare_run h w isSub (pure_rdw w rn) (pure_rdw w rm)
    (rdw_width w rn) (rdw_width w rm) nzcv c
  rw [rdw_eval h w hrn, rdw_eval h w hrm] at h2
  exact ⟨r', h1, by rw [execCondCompare_eq]; exact h2.advancePC⟩

/-- **`ccmp`, `ccmn` with an immediate.** -/
theorem condCompareImm_sound (h : Agree regs m s) (w : RegWidth) (isSub : Bool)
    {rn : Arm64.Reg} (hrn : Wf rn) (imm5 : BitVec 5) (nzcv : BitVec 4) (c : Arm64.CondCode) :
    ∃ r', run (ops.condCompare w isSub (rdw w rn) (num imm5.toNat) nzcv c) regs m =
        some (r', m) ∧
      Agree r' m (Arm64.execCondCompare w isSub true rn (imm5.zeroExtend 64) .xzr nzcv c s) := by
  have hb : (num imm5.toNat : E).eval regs = imm5.zeroExtend 64 := by simp
  obtain ⟨r', h1, h2⟩ := condCompare_run h w isSub (pure_rdw w rn) (Pure.imm _)
    (rdw_width w rn) (b := num imm5.toNat) (fun _ => by rw [hb]; bv_decide) nzcv c
  rw [rdw_eval h w hrn, hb] at h2
  exact ⟨r', h1, by rw [execCondCompare_eq]; exact h2.advancePC⟩

end MachineChecked.ARM.Lift
