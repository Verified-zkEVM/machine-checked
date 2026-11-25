/-
  MachineChecked.ARM.Lift.Sound.AddSub

  The lift of AArch64 against arm64-semantics: addition and subtraction, with an immediate, a
  shifted register and an extended register, and the flags where the instruction sets them.

  ## Main results

  * `sub64`, `add64`, `sub32`, `add32`: the flags as the lift computes them are the machine's
  * `addSub_run`: the operations of an addition or a subtraction
  * `addSubImm_sound`, `addSubShift_sound`, `addSubExt_sound`: the three instructions
-/

import MachineChecked.ARM.Lift.Sound.Basic

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-! ## Addition and subtraction -/

/-- **`x - y` at 64 bits**: the result and the flags, as the lift computes them. -/
theorem sub64 (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x (~~~y) true).1 = x - y ∧
    flag (Arm64.AddWithCarry64 x (~~~y) true).2.n = (x - y) >>> 63 &&& 1#64 ∧
    flag (Arm64.AddWithCarry64 x (~~~y) true).2.z = (if (x - y).ult 1#64 then 1#64 else 0#64) ∧
    flag (Arm64.AddWithCarry64 x (~~~y) true).2.c = (if x.ult y then 1#64 else 0#64) ^^^ 1#64 ∧
    flag (Arm64.AddWithCarry64 x (~~~y) true).2.v =
      ((x ^^^ y) &&& (x ^^^ (x - y))) >>> 63 &&& 1#64 := by
  simp only [Arm64.AddWithCarry64, flag]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- **`x + y` at 64 bits**: the result and the flags, as the lift computes them. -/
theorem add64 (x y : BitVec 64) :
    (Arm64.AddWithCarry64 x y false).1 = x + y ∧
    flag (Arm64.AddWithCarry64 x y false).2.n = (x + y) >>> 63 &&& 1#64 ∧
    flag (Arm64.AddWithCarry64 x y false).2.z = (if (x + y).ult 1#64 then 1#64 else 0#64) ∧
    flag (Arm64.AddWithCarry64 x y false).2.c = (if (x + y).ult x then 1#64 else 0#64) ∧
    flag (Arm64.AddWithCarry64 x y false).2.v =
      ((x ^^^ (x + y)) &&& (y ^^^ (x + y))) >>> 63 &&& 1#64 := by
  simp only [Arm64.AddWithCarry64, flag]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- **`x - y` at 32 bits**, of values of 32 bits: `r` is the result, zero-extended. -/
theorem sub32 (x y : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64)
    (hy : y = (y.setWidth 32).setWidth 64) :
    let p := Arm64.AddWithCarry32 (x.truncate 32) (~~~(y.truncate 32)) true
    let r := ((x - y).setWidth 32).setWidth 64
    p.1.zeroExtend 64 = r ∧
    flag p.2.n = r >>> 31 &&& 1#64 ∧
    flag p.2.z = (if r.ult 1#64 then 1#64 else 0#64) ∧
    flag p.2.c = (if x.ult y then 1#64 else 0#64) ^^^ 1#64 ∧
    flag p.2.v = ((x ^^^ y) &&& (x ^^^ r)) >>> 31 &&& 1#64 := by
  simp only [Arm64.AddWithCarry32, flag]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- **`x + y` at 32 bits**, of values of 32 bits: `r` is the result, zero-extended. -/
theorem add32 (x y : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64)
    (hy : y = (y.setWidth 32).setWidth 64) :
    let p := Arm64.AddWithCarry32 (x.truncate 32) (y.truncate 32) false
    let r := ((x + y).setWidth 32).setWidth 64
    p.1.zeroExtend 64 = r ∧
    flag p.2.n = r >>> 31 &&& 1#64 ∧
    flag p.2.z = (if r.ult 1#64 then 1#64 else 0#64) ∧
    flag p.2.c = (x + y) >>> 32 &&& 1#64 ∧
    flag p.2.v = ((x ^^^ r) &&& (y ^^^ r)) >>> 31 &&& 1#64 := by
  simp only [Arm64.AddWithCarry32, flag]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- The flags of `x + y` or `x - y` at a width. -/
def addSubPs (w : RegWidth) (isSub : Bool) (x y : BitVec 64) : Arm64.PState :=
  match w, isSub with
  | .W32, true => (Arm64.AddWithCarry32 (x.truncate 32) (~~~(y.truncate 32)) true).2
  | .W32, false => (Arm64.AddWithCarry32 (x.truncate 32) (y.truncate 32) false).2
  | .W64, true => (Arm64.AddWithCarry64 x (~~~y) true).2
  | .W64, false => (Arm64.AddWithCarry64 x y false).2

/-- `x + y` or `x - y` at a width. -/
def addSubVal (w : RegWidth) (isSub : Bool) (x y : BitVec 64) : BitVec 64 :=
  match w, isSub with
  | .W32, true => ((x - y).setWidth 32).setWidth 64
  | .W32, false => ((x + y).setWidth 32).setWidth 64
  | .W64, true => x - y
  | .W64, false => x + y

theorem addSubVal_eval (w : RegWidth) (isSub : Bool) (a b : E) :
    (trunc w (if isSub then sub a b else add a b)).eval regs =
      addSubVal w isSub (a.eval regs) (b.eval regs) := by
  cases w <;> cases isSub <;> simp [addSubVal]

/-- **The flags of an addition or a subtraction**, the result being in `t0`: each of the four
    expressions is worth the machine's flag. -/
theorem addSubFlags_eval (w : RegWidth) (isSub : Bool) {a b : E} (ha : Pure a) (hb : Pure b)
    (hx : w = .W32 → a.eval regs = ((a.eval regs).setWidth 32).setWidth 64)
    (hy : w = .W32 → b.eval regs = ((b.eval regs).setWidth 32).setWidth 64)
    {R : Reg → BitVec 64} (hs : Same regs R)
    (ht : R .t0 = addSubVal w isSub (a.eval regs) (b.eval regs)) :
    let ps := addSubPs w isSub (a.eval regs) (b.eval regs)
    (bit (.reg .t0) (w.bits - 1) : E).eval R = flag ps.n ∧
    (isZero (.reg .t0) : E).eval R = flag ps.z ∧
    (if isSub then Build.flip (.bin .ult a b)
      else if w = .W32 then bit (add a b) 32 else .bin .ult (.reg .t0) a : E).eval R = flag ps.c ∧
    (bit (if isSub then band (bxor a b) (bxor a (.reg .t0))
      else band (bxor a (.reg .t0)) (bxor b (.reg .t0))) (w.bits - 1) : E).eval R = flag ps.v := by
  have ea := ha _ _ hs
  have eb := hb _ _ hs
  generalize a.eval regs = x at hx ht ea ⊢
  generalize b.eval regs = y at hy ht eb ⊢
  cases w <;> cases isSub <;> simp only [addSubVal] at ht
  · obtain ⟨-, hn, hz, hc, hv⟩ := add32 x y (hx rfl) (hy rfl)
    simp [RegWidth.bits, addSubPs, ht, ea, eb, hn, hz, hc, hv]
  · obtain ⟨-, hn, hz, hc, hv⟩ := sub32 x y (hx rfl) (hy rfl)
    simp [RegWidth.bits, addSubPs, ht, ea, eb, hn, hz, hc, hv]
  · obtain ⟨-, hn, hz, hc, hv⟩ := add64 x y
    simp [RegWidth.bits, addSubPs, ht, ea, eb, hn, hz, hc, hv]
  · obtain ⟨-, hn, hz, hc, hv⟩ := sub64 x y
    simp [RegWidth.bits, addSubPs, ht, ea, eb, hn, hz, hc, hv]

/-- **An addition or a subtraction**, with its flags if it sets them: the operations run, and
    the registers stand for the machine state with the result and the flags written. `a` and
    `b` are operands of the width that read machine registers only. -/
theorem addSub_run (h : Agree regs m s) (w : RegWidth) (op : Arm64.AddSubOp) {dst : Arm64.Reg}
    (hd : Wf dst) {a b : E} (ha : Pure a) (hb : Pure b)
    (hx : w = .W32 → a.eval regs = ((a.eval regs).setWidth 32).setWidth 64)
    (hy : w = .W32 → b.eval regs = ((b.eval regs).setWidth 32).setWidth 64) :
    ∃ r', run (addSub w (op matches .SUB | .SUBS) op.setsFlags dst a b) regs m = some (r', m) ∧
      Agree r' m (
        let p := Arm64.evalAddSub w op (a.eval regs) (b.eval regs) none
        match p.2 with
        | some ps => (s.writeReg w dst p.1).setPState ps
        | none => s.writeReg w dst p.1) := by
  generalize hxe : a.eval regs = x at hx
  generalize hye : b.eval regs = y at hy
  cases op <;> cases w
  · simp only [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc]
    refine result_run h hd ?_
    simp [hxe, hye, Arm64.AddWithCarry32]
    bv_decide
  · simp only [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc]
    refine result_run h hd ?_
    simp [hxe, hye, Arm64.AddWithCarry64]
    bv_decide
  · obtain ⟨h0, hn, hz, hc, hv⟩ := add32 x y (hx rfl) (hy rfl)
    have := flags_run h hd (e := (z32 (add a b))) (en := (bit (.reg .t0) 31)) (ez := (isZero (.reg .t0)))
      (ec := (bit (add a b) 32))
      (ev := (bit (band (bxor a (.reg .t0)) (bxor b (.reg .t0))) 31))
      (ps := (Arm64.AddWithCarry32 (x.truncate 32) (y.truncate 32) false).2)
      (by simp [hxe, hye]; rfl)
      (fun R hs ht => by
        simp [ha _ _ hs, hb _ _ hs, ht, hxe, hye, hn, hz, hc, hv])
    simpa [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc, addSubFlags, setNZ,
      Arm64.State.writeReg, h0, RegWidth.bits] using this
  · obtain ⟨h0, hn, hz, hc, hv⟩ := add64 x y 
    have := flags_run h hd (e := (add a b)) (en := (bit (.reg .t0) 63)) (ez := (isZero (.reg .t0)))
      (ec := (.bin .ult (.reg .t0) a))
      (ev := (bit (band (bxor a (.reg .t0)) (bxor b (.reg .t0))) 63))
      (ps := (Arm64.AddWithCarry64 x y false).2)
      (by simp [hxe, hye]; rfl)
      (fun R hs ht => by
        simp [ha _ _ hs, hb _ _ hs, ht, hxe, hye, hn, hz, hc, hv])
    simpa [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc, addSubFlags, setNZ,
      Arm64.State.writeReg, h0, RegWidth.bits] using this
  · simp only [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc]
    refine result_run h hd ?_
    simp [hxe, hye, Arm64.AddWithCarry32]
    bv_decide
  · simp only [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc]
    refine result_run h hd ?_
    simp [hxe, hye, Arm64.AddWithCarry64]
    bv_decide
  · obtain ⟨h0, hn, hz, hc, hv⟩ := sub32 x y (hx rfl) (hy rfl)
    have := flags_run h hd (e := (z32 (sub a b))) (en := (bit (.reg .t0) 31)) (ez := (isZero (.reg .t0)))
      (ec := (Build.flip (.bin .ult a b)))
      (ev := (bit (band (bxor a b) (bxor a (.reg .t0))) 31))
      (ps := (Arm64.AddWithCarry32 (x.truncate 32) (~~~(y.truncate 32)) true).2)
      (by simp [hxe, hye]; rfl)
      (fun R hs ht => by
        simp [ha _ _ hs, hb _ _ hs, ht, hxe, hye, hn, hz, hc, hv])
    simpa [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc, addSubFlags, setNZ,
      Arm64.State.writeReg, h0, RegWidth.bits] using this
  · obtain ⟨h0, hn, hz, hc, hv⟩ := sub64 x y 
    have := flags_run h hd (e := (sub a b)) (en := (bit (.reg .t0) 63)) (ez := (isZero (.reg .t0)))
      (ec := (Build.flip (.bin .ult a b)))
      (ev := (bit (band (bxor a b) (bxor a (.reg .t0))) 63))
      (ps := (Arm64.AddWithCarry64 x (~~~y) true).2)
      (by simp [hxe, hye]; rfl)
      (fun R hs ht => by
        simp [ha _ _ hs, hb _ _ hs, ht, hxe, hye, hn, hz, hc, hv])
    simpa [addSub, Arm64.AddSubOp.setsFlags, Arm64.evalAddSub, trunc, addSubFlags, setNZ,
      Arm64.State.writeReg, h0, RegWidth.bits] using this

/-- **`add`, `adds`, `sub`, `subs` with an immediate.** -/
theorem addSubImm_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.AddSubOp)
    {dst rn : Arm64.Reg} (hd : Wf dst) (hn : Wf rn) (imm12 : BitVec 12) (shift12 : Bool) :
    ∃ r', run (addSub w (op matches .SUB | .SUBS) op.setsFlags dst (rdw w rn)
        (num (if shift12 then imm12.toNat * 4096 else imm12.toNat))) regs m = some (r', m) ∧
      Agree r' m (Arm64.execAddSubImm w op dst rn imm12 shift12 s) := by
  have hb : (Expr.imm (BitVec.ofNat 64 (if shift12 then imm12.toNat * 4096 else imm12.toNat))
      : E).eval regs = if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64 := by
    cases shift12 <;> simp <;> bv_omega
  obtain ⟨r', h1, h2⟩ := addSub_run h w op hd (pure_rdw w rn) (Pure.imm _) (rdw_width w rn)
    (fun _ => by rw [hb]; cases shift12 <;> simp <;> bv_decide)
  refine ⟨r', h1, ?_⟩
  rw [hb, rdw_eval h w hn] at h2
  exact h2.advancePC

/-- **`add`, `adds`, `sub`, `subs` with a shifted register.** -/
theorem addSubShift_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.AddSubOp)
    {dst rn rm : Arm64.Reg} (hd : Wf dst) (hrn : Wf rn) (hrm : Wf rm) (ty : Arm64.ShiftType)
    {n : Nat} (hn : n < w.bits) :
    ∃ r', run (addSub w (op matches .SUB | .SUBS) op.setsFlags dst (rdw w rn)
        (shifted w ty n rm)) regs m = some (r', m) ∧
      Agree r' m (Arm64.execAddSubShift w op dst rn rm ty n s) := by
  have hb := shifted_eval h w ty hn hrm
  obtain ⟨r', h1, h2⟩ := addSub_run h w op hd (pure_rdw w rn) (pure_shifted w ty n rm)
    (rdw_width w rn) (fun hw => by rw [hb]; subst hw; simp [Arm64.shiftVal])
  refine ⟨r', h1, ?_⟩
  rw [hb, rdw_eval h w hrn] at h2
  exact h2.advancePC

/-- **`add`, `adds`, `sub`, `subs` with an extended register.** -/
theorem addSubExt_sound (h : Agree regs m s) (w : RegWidth) (op : Arm64.AddSubOp)
    {dst rn rm : Arm64.Reg} (hd : Wf dst) (hrn : Wf rn) (hrm : Wf rm) (ext : Arm64.ExtendType)
    {n : Nat} (hn : n < 64) :
    ∃ r', run (addSub w (op matches .SUB | .SUBS) op.setsFlags dst (rdw w rn)
        (trunc w (extended ext n rm))) regs m = some (r', m) ∧
      Agree r' m (Arm64.execAddSubExt w op dst rn rm ext n s) := by
  have hb := extended_eval h w ext hn hrm
  obtain ⟨r', h1, h2⟩ := addSub_run h w op hd (pure_rdw w rn)
    (pure_trunc w (pure_extended ext n rm))
    (rdw_width w rn) (fun hw => by rw [hb]; subst hw; simp [Arm64.extendVal])
  refine ⟨r', h1, ?_⟩
  rw [hb, rdw_eval h w hrn] at h2
  exact h2.advancePC

end MachineChecked.ARM.Lift
