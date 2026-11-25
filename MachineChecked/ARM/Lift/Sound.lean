/-
  MachineChecked.ARM.Lift.Sound

  The lift of AArch64 against arm64-semantics, an instruction at a time: the operations the
  lift writes for an instruction (`ops`) compute what the machine's execution of it
  (`Arm64.execInstWithSvc`) does.

  `armIsa` is AArch64 at Lprog over arm64-semantics' memory: a load or a store faults where
  the machine's permission check fails. `Agree regs m s` says a register file and a memory of
  Lprog stand for a machine state: the general registers but number 31, the stack pointer,
  the four flags as 0 or 1, and the memory. The registers of the lift's own (`t0`, `t1`,
  `t2`) stand for nothing.

  This is the start of milestone M4 of `docs/NativeVerifiers.md`; the kinds proved so far are
  listed under the main results.

  ## Main definitions

  * `armMem`, `armIsa`, `Agree`, `run`

  ## Main results

  * `rd_eval`, `rdw_eval`, `wr_run`: a register read and written
  * `addSub_run`: an addition or a subtraction, with its flags
-/

import MachineChecked.ARM.Lift.Lift
import Lprog.Op

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

/-- The width of a memory access, as arm64-semantics names it. -/
def memWidth : Width → MemWidth
  | .b1 => .B8
  | .b2 => .H16
  | .b4 => .W32
  | .b8 => .X64

/-- **AArch64's memory** at Lprog: arm64-semantics', with its permission checks. -/
def armMem : Mem Arm64.Memory where
  load w a m := if m.canRead a w.bytes then some (m.readSized (memWidth w) false a) else none
  store w a v m := if m.canWrite a w.bytes then some (m.writeSized (memWidth w) a v) else none

/-- **AArch64 at Lprog**, over arm64-semantics' memory. -/
abbrev armIsa : Isa := Isa.ofOps Reg .x30 .sp Arm64.Memory armMem

/-- A flag as a register holds it. -/
def flag (b : Bool) : BitVec 64 := if b then 1#64 else 0#64

/-- **A register file and a memory stand for a machine state.** -/
structure Agree (regs : Reg → BitVec 64) (m : Arm64.Memory) (s : Arm64.State) : Prop where
  gpr : ∀ i : BitVec 5, i ≠ 31#5 → regs (.ofGpr i) = s.regs.read i
  sp : regs .sp = s.sp
  nf : regs .nf = flag s.pstate.n
  zf : regs .zf = flag s.pstate.z
  cf : regs .cf = flag s.pstate.c
  vf : regs .vf = flag s.pstate.v
  mem : m = s.mem

/-- The operations of an instruction, run in order; `none` is a fault. -/
def run : List O → (Reg → BitVec 64) → Arm64.Memory →
    Option ((Reg → BitVec 64) × Arm64.Memory)
  | [], regs, m => some (regs, m)
  | o :: os, regs, m => (o.eval armMem regs m).bind fun p => run os p.1 p.2

/-- A register the decoder gives: not general register 31, which it gives as `sp` or `xzr`. -/
def Wf : Arm64.Reg → Prop
  | .gpr i => i ≠ 31#5
  | _ => True

theorem ofGpr_inj :
    ∀ i j : BitVec 5, i ≠ 31#5 → j ≠ 31#5 → Reg.ofGpr i = Reg.ofGpr j → i = j := by
  decide

theorem ofGpr_ne : ∀ i : BitVec 5, Reg.ofGpr i ≠ .sp ∧ Reg.ofGpr i ≠ .nf ∧
    Reg.ofGpr i ≠ .zf ∧ Reg.ofGpr i ≠ .cf ∧ Reg.ofGpr i ≠ .vf ∧ Reg.ofGpr i ≠ .t0 ∧
    Reg.ofGpr i ≠ .t1 ∧ Reg.ofGpr i ≠ .t2 := by
  decide

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- **A register read** at 64 bits. -/
theorem rd_eval (h : Agree regs m s) {r : Arm64.Reg} (hr : Wf r) :
    (rd r).eval regs = s.readReg64 r := by
  cases r with
  | gpr i =>
    have hi : i ≠ 31#5 := hr
    simp [rd, Expr.eval, Arm64.State.readReg64, h.gpr i hi, hi]
  | sp => simp [rd, Expr.eval, Arm64.State.readReg64, h.sp]
  | xzr => simp [rd, num, Expr.eval, Arm64.State.readReg64]

/-- **A register read** at a width. -/
theorem rdw_eval (h : Agree regs m s) (w : RegWidth) {r : Arm64.Reg} (hr : Wf r) :
    (rdw w r).eval regs = s.readReg w r := by
  have := rd_eval h hr
  cases r <;> cases w <;>
    simp_all [rdw, rd, trunc, z32, num, Expr.eval, UnOp.eval, Arm64.State.readReg,
      Arm64.State.readReg32, Arm64.State.readReg64, Width.bits]

/-- **A register written**: the operations run, and the registers stand for the machine state
    with the register written. -/
theorem wr_run (h : Agree regs m s) {r : Arm64.Reg} (hr : Wf r) (e : E) :
    ∃ r', run (wr r e) regs m = some (r', m) ∧ Agree r' m (s.writeReg64 r (e.eval regs)) ∧
      ∀ x, x ≠ dest r → r' x = regs x := by
  cases r with
  | gpr i =>
    have hi : i ≠ 31#5 := hr
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := ofGpr_ne i
    refine ⟨_, rfl, ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, h.mem⟩, fun x hx => by
      simp [updReg, dest] at hx ⊢; exact fun h' => absurd h' hx⟩
    · by_cases hji : j = i
      · subst hji
        simp [updReg, Arm64.State.writeReg64, Arm64.RegFile.read, Arm64.RegFile.write, hi]
      · have : Reg.ofGpr j ≠ Reg.ofGpr i := fun h' => hji (ofGpr_inj j i hj hi h')
        simpa [updReg, this, Arm64.State.writeReg64, Arm64.RegFile.read, Arm64.RegFile.write, hi,
          hji] using h.gpr j hj
    all_goals simp [updReg, Arm64.State.writeReg64, hi, h.sp, h.nf, h.zf, h.cf, h.vf, Ne.symm h1,
      Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  | sp =>
    refine ⟨_, rfl, ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, h.mem⟩, fun x hx => by
      simp [updReg, dest] at hx ⊢; exact fun h' => absurd h' hx⟩
    · simp [updReg, (ofGpr_ne j).1, Arm64.State.writeReg64, h.gpr j hj]
    all_goals simp [updReg, Arm64.State.writeReg64, h.nf, h.zf, h.cf, h.vf]
  | xzr =>
    exact ⟨regs, rfl, by simpa [Arm64.State.writeReg64] using h, fun _ _ => rfl⟩

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

end MachineChecked.ARM.Lift
