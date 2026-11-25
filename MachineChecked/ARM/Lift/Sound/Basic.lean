/-
  MachineChecked.ARM.Lift.Sound.Basic

  The lift of AArch64 against arm64-semantics: what the proofs of each kind of instruction
  share.

  `armIsa` is AArch64 at Lprog over arm64-semantics' memory: a load or a store faults where
  the machine's permission check fails. `Agree regs m s` says a register file and a memory of
  Lprog stand for a machine state: the general registers but number 31, the stack pointer,
  the four flags as 0 or 1, and the memory. The registers of the lift's own (`t0`, `t1`,
  `t2`) stand for nothing. `run` runs the operations of an instruction. An operand is `Pure`
  if it reads machine registers only, so that it is worth the same after the lift's own
  registers and the flags are written.

  ## Main definitions

  * `armMem`, `armIsa`, `Agree`, `run`, `Wf`, `Pure`

  ## Main results

  * `rd_eval`, `rdw_eval`, `wr_run`: a register read and written
  * `shifted_eval`, `extended_eval`: the operands of the data instructions
  * `Agree.scratch`, `Agree.flags`: the lift's own registers and the flags written
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

/-! ## What the expressions the lift builds are worth -/

section eval
variable (a b c : E) (n : Nat)

@[simp] theorem eval_reg (x : Reg) : (Expr.reg x).eval regs = regs x := rfl
@[simp] theorem eval_imm (v : BitVec 64) : (Expr.imm v : E).eval regs = v := rfl
@[simp] theorem eval_num : (num n : E).eval regs = BitVec.ofNat 64 n := rfl
@[simp] theorem eval_add : (add a b).eval regs = a.eval regs + b.eval regs := rfl
@[simp] theorem eval_sub : (sub a b).eval regs = a.eval regs - b.eval regs := rfl
@[simp] theorem eval_band : (band a b).eval regs = a.eval regs &&& b.eval regs := rfl
@[simp] theorem eval_bor : (bor a b).eval regs = a.eval regs ||| b.eval regs := rfl
@[simp] theorem eval_bxor : (bxor a b).eval regs = a.eval regs ^^^ b.eval regs := rfl
@[simp] theorem eval_bnot : (bnot a).eval regs = ~~~a.eval regs := rfl
@[simp] theorem eval_z32 : (z32 a).eval regs = ((a.eval regs).setWidth 32).setWidth 64 := rfl
@[simp] theorem eval_s32 : (s32 a).eval regs = ((a.eval regs).setWidth 32).signExtend 64 := rfl
@[simp] theorem eval_ult :
    (Expr.bin .ult a b).eval regs = if (a.eval regs).ult (b.eval regs) then 1#64 else 0#64 := rfl

@[simp] theorem eval_shl : (shl a n).eval regs = a.eval regs <<< (n % 2 ^ 64) := by
  unfold shl; split <;> simp_all [Expr.eval, BinOp.eval, num]

@[simp] theorem eval_lshr : (lshr a n).eval regs = a.eval regs >>> (n % 2 ^ 64) := by
  unfold lshr; split <;> simp_all [Expr.eval, BinOp.eval, num]

@[simp] theorem eval_ashr : (ashr a n).eval regs = (a.eval regs).sshiftRight (n % 2 ^ 64) := by
  unfold ashr; split <;> simp_all [Expr.eval, BinOp.eval, num]

@[simp] theorem eval_bit : (bit a n).eval regs = a.eval regs >>> (n % 2 ^ 64) &&& 1#64 := by
  simp [bit]

@[simp] theorem eval_isZero :
    (isZero a).eval regs = if (a.eval regs).ult 1#64 then 1#64 else 0#64 := rfl

@[simp] theorem eval_flip : (Build.flip a).eval regs = a.eval regs ^^^ 1#64 := rfl

@[simp] theorem eval_trunc (w : RegWidth) : (trunc w a).eval regs =
    if w = .W32 then ((a.eval regs).setWidth 32).setWidth 64 else a.eval regs := by
  unfold trunc; split <;> simp

end eval

/-! ## Running, and what an operand reads -/

theorem run_append (a b : List O) :
    run (a ++ b) regs m = (run a regs m).bind fun p => run b p.1 p.2 := by
  induction a generalizing regs m with
  | nil => rfl
  | cons o os ih =>
    simp only [List.cons_append, run]
    cases o.eval armMem regs m <;> simp [ih]

@[simp] theorem run_set (d : Reg) (e : E) (os : List O) :
    run (.set d e :: os) regs m = run os (updReg regs d (e.eval regs)) m := rfl

/-- The registers of the lift's own, and the flags. -/
def Own : Reg → Bool
  | .t0 | .t1 | .t2 | .nf | .zf | .cf | .vf => true
  | _ => false

/-- Two register files with the same machine registers. -/
def Same (regs regs' : Reg → BitVec 64) : Prop := ∀ x, Own x = false → regs' x = regs x

theorem Same.rfl : Same regs regs := fun _ _ => _root_.rfl

theorem Same.upd {regs' : Reg → BitVec 64} (h : Same regs regs') {x : Reg} (hx : Own x = true)
    (v : BitVec 64) : Same regs (updReg regs' x v) := fun y hy => by
  have : y ≠ x := fun e => by simp [e, hx] at hy
  simp [updReg, this, h y hy]

/-- **An operand that reads machine registers only**: not the lift's own, nor the flags. -/
def Pure (e : E) : Prop := ∀ regs regs', Same regs regs' → e.eval regs' = e.eval regs

theorem Pure.imm (v : BitVec 64) : Pure (.imm v) := fun _ _ _ => rfl

theorem Pure.un (op : UnOp) {e : E} (h : Pure e) : Pure (.un op e) := fun r r' hs => by
  simp [Expr.eval, h r r' hs]

theorem Pure.bin (op : BinOp) {a b : E} (ha : Pure a) (hb : Pure b) : Pure (.bin op a b) :=
  fun r r' hs => by simp [Expr.eval, ha r r' hs, hb r r' hs]

theorem pure_rd (r : Arm64.Reg) : Pure (rd r) := by
  cases r with
  | gpr i =>
    obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := ofGpr_ne i
    exact fun _ _ hs => hs _ (by revert h2 h3 h4 h5 h6 h7 h8; cases Reg.ofGpr i <;> simp [Own])
  | sp => exact fun _ _ hs => hs _ rfl
  | xzr => exact Pure.imm _

theorem pure_trunc (w : RegWidth) {e : E} (h : Pure e) : Pure (trunc w e) := by
  unfold trunc; split
  · exact h.un _
  · exact h

theorem pure_rdw (w : RegWidth) (r : Arm64.Reg) : Pure (rdw w r) := by
  cases r <;> first | exact Pure.imm _ | exact pure_trunc w (pure_rd _)

/-- The registers stand for the same machine state when the lift's own are written. -/
theorem Agree.scratch (h : Agree regs m s) {x : Reg} (hx : x = .t0 ∨ x = .t1 ∨ x = .t2)
    (v : BitVec 64) : Agree (updReg regs x v) m s := by
  have hne : ∀ y, Own y = false → y ≠ x := by
    rintro y hy rfl; rcases hx with rfl | rfl | rfl <;> simp [Own] at hy
  have hg : ∀ i, Own (Reg.ofGpr i) = false := by decide
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, h.mem⟩
  · simp [updReg, hne _ (hg i), h.gpr i hi]
  all_goals rcases hx with rfl | rfl | rfl <;>
    simp [updReg, h.sp, h.nf, h.zf, h.cf, h.vf]

/-- The registers stand for the machine state with its flags set, when the flags are
    written. -/
theorem Agree.flags (h : Agree regs m s) (ps : Arm64.PState) :
    Agree (updReg (updReg (updReg (updReg regs .nf (flag ps.n)) .zf (flag ps.z)) .cf (flag ps.c))
      .vf (flag ps.v)) m (s.setPState ps) := by
  have hg : ∀ i, Own (Reg.ofGpr i) = false := by decide
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, h.mem⟩
  · have := hg i
    have h1 : Reg.ofGpr i ≠ .nf := by rintro e; simp [e, Own] at this
    have h2 : Reg.ofGpr i ≠ .zf := by rintro e; simp [e, Own] at this
    have h3 : Reg.ofGpr i ≠ .cf := by rintro e; simp [e, Own] at this
    have h4 : Reg.ofGpr i ≠ .vf := by rintro e; simp [e, Own] at this
    simpa [updReg, h1, h2, h3, h4, Arm64.State.setPState] using h.gpr i hi
  all_goals simp [updReg, Arm64.State.setPState, h.sp]

/-- The registers stand for the machine state with its flags set, whatever was written to
    the lift's own registers, when the flags hold the new values. -/
theorem Agree.of_same (h : Agree regs m s) {R : Reg → BitVec 64} (hs : Same regs R)
    (ps : Arm64.PState) (hn : R .nf = flag ps.n) (hz : R .zf = flag ps.z)
    (hc : R .cf = flag ps.c) (hv : R .vf = flag ps.v) : Agree R m (s.setPState ps) :=
  ⟨fun i hi => (hs _ (by revert i; decide)).trans (h.gpr i hi), (hs _ rfl).trans h.sp, hn, hz,
    hc, hv, h.mem⟩

theorem Agree.advancePC (h : Agree regs m s) : Agree regs m s.advancePC :=
  ⟨h.gpr, h.sp, h.nf, h.zf, h.cf, h.vf, h.mem⟩

/-! ## The two shapes of a data instruction -/

/-- **A result written**, the flags left: the operations of an instruction that computes `e`
    into `dst`. -/
theorem result_run (h : Agree regs m s) {dst : Arm64.Reg} (hd : Wf dst) {e : E} {v : BitVec 64}
    (he : e.eval regs = v) :
    ∃ r', run (wr dst e) regs m = some (r', m) ∧ Agree r' m (s.writeReg64 dst v) := by
  obtain ⟨r', h1, h2, -⟩ := wr_run h hd e
  exact ⟨r', h1, he ▸ h2⟩

/-- **A result written at a width**, and the machine a step on. -/
theorem result_sound (h : Agree regs m s) {dst : Arm64.Reg} (hd : Wf dst) {e : E} (w : RegWidth)
    {res : BitVec 64}
    (he : e.eval regs = match w with | .W32 => (res.truncate 32).zeroExtend 64 | .W64 => res) :
    ∃ r', run (wr dst e) regs m = some (r', m) ∧
      Agree r' m (s.writeReg w dst res).advancePC := by
  obtain ⟨r', h1, h2⟩ := result_run h hd he
  exact ⟨r', h1, h2.advancePC⟩

/-- **A result and the flags written**: the result goes to `t0`, each flag is computed from
    the operands and `t0`, and `t0` goes to `dst`. -/
theorem flags_run (h : Agree regs m s) {dst : Arm64.Reg} (hd : Wf dst) {e en ez ec ev : E}
    {r : BitVec 64} {ps : Arm64.PState} (he : e.eval regs = r)
    (hf : ∀ R, Same regs R → R .t0 = r → en.eval R = flag ps.n ∧ ez.eval R = flag ps.z ∧
      ec.eval R = flag ps.c ∧ ev.eval R = flag ps.v) :
    ∃ r', run (.set .t0 e :: .set .nf en :: .set .zf ez :: .set .cf ec :: .set .vf ev ::
        wr dst (.reg .t0)) regs m = some (r', m) ∧
      Agree r' m ((s.writeReg64 dst r).setPState ps) := by
  obtain ⟨r', h1, h2, -⟩ := wr_run ((h.scratch (.inl rfl) r).flags ps) hd (.reg .t0)
  refine ⟨r', ?_, by
    simpa [Expr.eval, updReg, Arm64.State.setPState, Arm64.State.writeReg64] using h2⟩
  have s0 : Same regs (updReg regs .t0 r) := Same.rfl.upd rfl r
  have s1 := s0.upd (x := .nf) rfl (flag ps.n)
  have s2 := s1.upd (x := .zf) rfl (flag ps.z)
  have s3 := s2.upd (x := .cf) rfl (flag ps.c)
  simp only [run_set, he]
  rw [(hf _ s0 rfl).1, (hf _ s1 rfl).2.1, (hf _ s2 rfl).2.2.1, (hf _ s3 rfl).2.2.2]
  exact h1

/-! ## Operands -/

/-- A read at a width is of the width. -/
theorem rdw_width (w : RegWidth) (r : Arm64.Reg) (hw : w = .W32) :
    (rdw w r).eval regs = (((rdw w r).eval regs).setWidth 32).setWidth 64 := by
  subst hw; cases r <;> simp [rdw]

theorem pure_shl {e : E} (h : Pure e) (n : Nat) : Pure (shl e n) := by
  unfold shl; split
  · exact h
  · exact h.bin _ (Pure.imm _)

theorem pure_lshr {e : E} (h : Pure e) (n : Nat) : Pure (lshr e n) := by
  unfold lshr; split
  · exact h
  · exact h.bin _ (Pure.imm _)

theorem pure_ashr {e : E} (h : Pure e) (n : Nat) : Pure (ashr e n) := by
  unfold ashr; split
  · exact h
  · exact h.bin _ (Pure.imm _)

theorem pure_signed (w : RegWidth) {e : E} (h : Pure e) : Pure (signed w e) := by
  unfold signed; split
  · exact h.un _
  · exact h

theorem pure_shifted (w : RegWidth) (ty : Arm64.ShiftType) (n : Nat) (r : Arm64.Reg) :
    Pure (shifted w ty n r) := by
  have hx := pure_rdw w r
  unfold shifted
  split
  · exact hx
  · cases ty
    · exact pure_trunc w (pure_shl hx n)
    · exact pure_lshr hx n
    · exact pure_trunc w (pure_ashr (pure_signed w hx) n)
    · exact pure_trunc w ((pure_lshr hx n).bin _ (pure_shl hx _))

theorem pure_extended (ext : Arm64.ExtendType) (n : Nat) (r : Arm64.Reg) :
    Pure (extended ext n r) := by
  have hx := pure_rd r
  unfold extended
  cases ext <;> exact pure_shl (by first | exact hx | exact hx.un _) n

@[simp] theorem eval_signed (w : RegWidth) (a : E) : (signed w a).eval regs =
    if w = .W32 then ((a.eval regs).setWidth 32).signExtend 64 else a.eval regs := by
  unfold signed; split <;> simp

/-- **A register shifted by a constant** below the width. -/
theorem shifted_eval (h : Agree regs m s) (w : RegWidth) (ty : Arm64.ShiftType) {n : Nat}
    (hn : n < w.bits) {r : Arm64.Reg} (hr : Wf r) :
    (shifted w ty n r).eval regs = Arm64.shiftVal w (s.readReg w r) ty n := by
  rw [← rdw_eval h w hr]
  have hw := rdw_width (regs := regs) w r
  obtain ⟨x, hx⟩ : ∃ x, (rdw w r).eval regs = x := ⟨_, rfl⟩
  rw [hx] at hw ⊢
  unfold shifted
  by_cases h0 : n = 0
  · subst h0
    cases w <;> cases ty <;>
      simp [Arm64.shiftVal, Arm64.shift32, Arm64.shift64, hx, BitVec.rotateRight,
        BitVec.rotateRightAux] <;> exact hw rfl
  · have hb : w.bits ≤ 64 := by cases w <;> simp [RegWidth.bits]
    obtain ⟨k, rfl, hk⟩ : ∃ k : BitVec 64, n = k.toNat ∧ k.toNat < w.bits :=
      ⟨BitVec.ofNat 64 n, by simp; omega, by simp; omega⟩
    simp only [h0, ite_false]
    cases w
    · have hw := hw rfl
      simp only [RegWidth.bits] at hk
      have hk' : k < 32#64 := by bv_omega
      obtain ⟨j, hj, e⟩ : ∃ j : BitVec 64, j = 32#64 - k ∧ 32 - k.toNat = j.toNat :=
        ⟨_, rfl, by bv_omega⟩
      cases ty <;>
        simp [Arm64.shiftVal, Arm64.shift32, Nat.mod_eq_of_lt hk, RegWidth.bits, hx,
          Nat.mod_eq_of_lt (show k.toNat < 2 ^ 64 by omega), BitVec.rotateRight,
          BitVec.rotateRightAux, e, Nat.mod_eq_of_lt j.isLt] <;> bv_decide
    · simp only [RegWidth.bits] at hk
      have hk' : k < 64#64 := by bv_omega
      obtain ⟨j, hj, e⟩ : ∃ j : BitVec 64, j = 64#64 - k ∧ 64 - k.toNat = j.toNat :=
        ⟨_, rfl, by bv_omega⟩
      cases ty <;>
        simp [Arm64.shiftVal, Arm64.shift64, Nat.mod_eq_of_lt hk, RegWidth.bits, hx,
          Nat.mod_eq_of_lt (show k.toNat < 2 ^ 64 by omega), BitVec.rotateRight,
          BitVec.rotateRightAux, e, Nat.mod_eq_of_lt j.isLt] <;> bv_decide

/-- **A register extended and shifted left.** -/
theorem extended_eval (h : Agree regs m s) (w : RegWidth) (ext : Arm64.ExtendType) {n : Nat}
    (hn : n < 64) {r : Arm64.Reg} (hr : Wf r) :
    (trunc w (extended ext n r)).eval regs = Arm64.extendVal w (s.readReg64 r) ext n := by
  rw [← rd_eval h hr]
  have e : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  cases w <;> cases ext <;> simp [extended, Arm64.extendVal, UnOp.eval, Expr.eval, Width.bits, e]

end MachineChecked.ARM.Lift
