/-
  MachineChecked.ARM.Lift.Sound.Memory

  The lift of AArch64 against arm64-semantics: loads and stores.

  A load or a store of the lift faults where the machine's permission check fails, so where
  the operations run the machine does not fault on a permission. The machine faults also on a
  stack pointer that is not aligned, when it is the base of the access: that is a
  hypothesis here (`Aligned`). With write-back, the register loaded or stored is not the
  base (`Apart`): the architecture leaves that case unpredictable.

  ## Main results

  * `ldr_sound`
-/

import MachineChecked.ARM.Lift.Sound.Basic

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth AddrMode)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-! ## Running a load and a store -/

theorem memWidth_width (sz : MemWidth) : memWidth (width sz) = sz := by cases sz <;> rfl

theorem bytes_width (sz : MemWidth) : (width sz).bytes = sz.bytes := by cases sz <;> rfl

/-- A sign-extended load is the machine's signed read. -/
theorem sext_read (mem : Arm64.Memory) (sz : MemWidth) (sgn : Bool) (a : BitVec 64) :
    (if sgn then (UnOp.sext (width sz)).eval (mem.readSized sz false a)
      else mem.readSized sz false a) = mem.readSized sz sgn a := by
  cases sgn <;> cases sz <;>
    simp [Arm64.Memory.readSized, UnOp.eval, width, Width.bits]

theorem run_cons (o : O) (os : List O) :
    run (o :: os) regs m = (o.eval armMem regs m).bind fun p => run os p.1 p.2 := rfl

theorem run_load (d : Reg) (sz : MemWidth) (sgn : Bool) (a : E) (os : List O) :
    run (.load d (width sz) sgn a :: os) regs m =
      if m.canRead (a.eval regs) sz.bytes then
        run os (updReg regs d (m.readSized sz sgn (a.eval regs))) m
      else none := by
  have e := sext_read m sz sgn (a.eval regs)
  rw [run_cons]
  simp only [Op.eval, armMem, memWidth_width, bytes_width]
  by_cases hc : m.canRead (a.eval regs) sz.bytes = true <;> simp [hc, e]

theorem run_store (sz : MemWidth) (a e : E) (os : List O) :
    run (.store (width sz) a e :: os) regs m =
      if m.canWrite (a.eval regs) sz.bytes then
        run os regs (m.writeSized sz (a.eval regs) (e.eval regs))
      else none := by
  rw [run_cons]
  simp only [Op.eval, armMem, memWidth_width, bytes_width]
  by_cases hc : m.canWrite (a.eval regs) sz.bytes = true <;> simp [hc]

/-! ## Registers -/

/-- The register a load goes to holds the value, and the registers stand for the machine
    state with the register written. -/
theorem Agree.dest (h : Agree regs m s) {r : Arm64.Reg} (hr : Wf r) (v : BitVec 64) :
    Agree (updReg regs (dest r) v) m (s.writeReg64 r v) := by
  cases r with
  | xzr => exact h.scratch (.inl rfl) v
  | gpr i =>
    obtain ⟨r', h1, h2, -⟩ := wr_run h hr (r := .gpr i) (.imm v)
    cases h1; exact h2
  | sp =>
    obtain ⟨r', h1, h2, -⟩ := wr_run h hr (r := .sp) (.imm v)
    cases h1; exact h2

theorem Agree.setMem (h : Agree regs m s) (m' : Arm64.Memory) : Agree regs m' (s.setMem m') :=
  ⟨h.gpr, h.sp, h.nf, h.zf, h.cf, h.vf, rfl⟩

/-- Writes of two registers that are not the same one commute. -/
theorem writeReg64_comm (s : Arm64.State) {a b : Arm64.Reg} (hab : a ≠ b) (u v : BitVec 64) :
    (s.writeReg64 a u).writeReg64 b v = (s.writeReg64 b v).writeReg64 a u := by
  cases a <;> cases b <;> simp_all [Arm64.State.writeReg64]
  rename_i i j
  by_cases hi : i = 31#5 <;> by_cases hj : j = 31#5 <;>
    simp [hi, hj, Arm64.RegFile.write]
  funext k
  by_cases h1 : k = i <;> by_cases h2 : k = j <;> simp_all

/-- A register read after another is written. -/
theorem readReg64_writeReg64 (s : Arm64.State) {a b : Arm64.Reg} (hab : a ≠ b) (hb : Wf b)
    (v : BitVec 64) : (s.writeReg64 a v).readReg64 b = s.readReg64 b := by
  cases a <;> cases b <;>
    simp_all [Arm64.State.writeReg64, Arm64.State.readReg64, Wf, Arm64.RegFile.read,
      Arm64.RegFile.write]
  split
  · rfl
  · simp [Ne.symm hab]

theorem readReg64_same (s : Arm64.State) {a : Arm64.Reg} (ha : Wf a) (hz : a ≠ .xzr)
    (v : BitVec 64) : (s.writeReg64 a v).readReg64 a = v := by
  cases a <;> simp_all [Arm64.State.writeReg64, Arm64.State.readReg64, Wf, Arm64.RegFile.read,
    Arm64.RegFile.write]

/-! ## Addressing modes -/

/-- The registers of a mode are ones the decoder gives, its base is not the zero register, and
    its shift is below 64. -/
def WfMode : AddrMode → Prop
  | .Offset b _ | .UnscaledOffset b _ | .PostIndex b _ => Wf b
  | .PreIndex b _ => Wf b ∧ b ≠ .xzr
  | .RegOffset b i _ n => Wf b ∧ Wf i ∧ n < 64

/-- The base of a mode that writes it back. -/
def writeback : AddrMode → Option Arm64.Reg
  | .PreIndex b _ | .PostIndex b _ => some b
  | _ => none

/-- The machine state after what a mode does before the access. -/
def preState (s : Arm64.State) : AddrMode → Arm64.State
  | .PreIndex b off => s.writeReg64 b (s.readReg64 b + off)
  | _ => s

/-- The machine state `s2` after what a mode does after the access; `s` is the state before
    the instruction. -/
def postState (s s2 : Arm64.State) : AddrMode → Arm64.State
  | .PostIndex b off => s2.writeReg64 b (s.readReg64 b + off)
  | _ => s2

/-- **Before the access**: the operations run, and the address is the machine's. -/
theorem address_pre (h : Agree regs m s) {mode : AddrMode} (hm : WfMode mode) :
    ∃ R1, run (address mode).1 regs m = some (R1, m) ∧
      (address mode).2.1.eval R1 = (Arm64.evalAddrMode s mode).1 ∧
      Agree R1 m (preState s mode) := by
  cases mode with
  | Offset b off => exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm], h⟩
  | UnscaledOffset b off =>
    exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm], h⟩
  | PostIndex b off => exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm], h⟩
  | RegOffset b i ext n =>
    have := extended_eval h .W64 ext hm.2.2 hm.2.1
    simp only [eval_trunc, reduceCtorEq, ite_false] at this
    exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm.1, this], h⟩
  | PreIndex b off =>
    obtain ⟨R1, h1, h2, -⟩ := wr_run h hm.1 (r := b) (add (rd b) (.imm off))
    simp only [eval_add, eval_imm, rd_eval h hm.1] at h2
    exact ⟨R1, h1, by
      simp [address, Arm64.evalAddrMode, rd_eval h2 hm.1, readReg64_same s hm.1 hm.2], h2⟩

/-- **After the access**: the operations run, and write the base back. -/
theorem address_post {R2 : Reg → BitVec 64} {m2 : Arm64.Memory} {s2 : Arm64.State}
    (h2 : Agree R2 m2 s2) {mode : AddrMode} (hm : WfMode mode)
    (hbase : ∀ b off, mode = .PostIndex b off → s2.readReg64 b = s.readReg64 b) :
    ∃ R3, run (address mode).2.2 R2 m2 = some (R3, m2) ∧
      Agree R3 m2 (postState s s2 mode) := by
  cases mode with
  | PostIndex b off =>
    obtain ⟨R3, h1, h3, -⟩ := wr_run h2 hm (r := b) (add (rd b) (.imm off))
    simp only [eval_add, eval_imm, rd_eval h2 hm, hbase b off rfl] at h3
    exact ⟨R3, h1, h3⟩
  | _ => exact ⟨R2, rfl, h2⟩

/-! ## Loads -/

theorem updReg_updReg (R : Reg → BitVec 64) (d : Reg) (u v : BitVec 64) :
    updReg (updReg R d u) d v = updReg R d v := by
  funext x; simp only [updReg]; split <;> rfl

/-- A read narrower than 64 bits, zero-extended, is of 32 bits. -/
theorem readSized_low (mem : Arm64.Memory) {sz : MemWidth} (hsz : sz ≠ .X64) (a : BitVec 64) :
    ((mem.readSized sz false a).setWidth 32).setWidth 64 = mem.readSized sz false a := by
  cases sz <;> simp_all [Arm64.Memory.readSized]

/-- **`ldr`, `ldur` and their signed and narrow forms.** Where the operations run, the machine
    does not fault and its state is what the registers stand for. -/
theorem ldr_sound (h : Agree regs m s) (w : RegWidth) (sz : MemWidth) (sgn : Bool)
    {rt : Arm64.Reg} (hrt : Wf rt) {mode : AddrMode} (hm : WfMode mode)
    (hal : Arm64.checkAddrSPAligned s mode = true) (hap : ∀ b ∈ writeback mode, rt ≠ b)
    (hsz : w = .W32 → sz ≠ .X64) {r' : Reg → BitVec 64} {m' : Arm64.Memory}
    (hrun : run ((address mode).1 ++ [.load (dest rt) (width sz) sgn (address mode).2.1] ++
      (if sgn ∧ w = .W32 then [.set (dest rt) (z32 (.reg (dest rt)))] else []) ++
      (address mode).2.2) regs m = some (r', m')) :
    Agree r' m' (Arm64.execLdr w sz sgn rt mode s) ∧
      (Arm64.execLdr w sz sgn rt mode s).status = s.status ∧
      (Arm64.execLdr w sz sgn rt mode s).pc = s.pc + 4#64 := by
  obtain ⟨R1, e1, ha, hA1⟩ := address_pre h hm
  rw [List.append_assoc, List.append_assoc, run_append, e1] at hrun
  simp only [Option.bind_some, List.cons_append, List.nil_append, run_load, ha] at hrun
  have hmem : m = s.mem := h.mem
  by_cases hc : m.canRead (Arm64.evalAddrMode s mode).1 sz.bytes = true
  · simp only [hc, ↓reduceIte] at hrun
    generalize hv : m.readSized sz sgn (Arm64.evalAddrMode s mode).1 = val at hrun
    -- the register loaded, at the width
    have hA2 : ∃ R2, run ((if sgn ∧ w = .W32 then [.set (dest rt) (z32 (.reg (dest rt)))]
        else []) ++ (address mode).2.2) (updReg R1 (dest rt) val) m =
          run (address mode).2.2 R2 m ∧
        Agree R2 m ((preState s mode).writeReg w rt val) := by
      by_cases hf : sgn ∧ w = .W32
      · refine ⟨updReg R1 (dest rt) ((val.setWidth 32).setWidth 64), ?_, ?_⟩
        · simp [hf, updReg, updReg_updReg]
        · obtain ⟨-, rfl⟩ := hf
          exact hA1.dest hrt _
      · refine ⟨updReg R1 (dest rt) val, by simp [hf], ?_⟩
        cases w
        · have hs : sgn = false := by simpa using hf
          subst hs
          have := readSized_low m (hsz rfl) (Arm64.evalAddrMode s mode).1
          rw [hv] at this
          have e : (preState s mode).writeReg .W32 rt val = (preState s mode).writeReg64 rt val := by
            simp [Arm64.State.writeReg, this]
          rw [e]
          exact hA1.dest hrt val
        · exact hA1.dest hrt val
    obtain ⟨R2, e2, hA2⟩ := hA2
    rw [e2] at hrun
    -- the base written back after
    obtain ⟨R3, e3, hA3⟩ := address_post (s := s) hA2 hm (fun b off hb => by
      subst hb
      have hne : rt ≠ b := hap b rfl
      exact readReg64_writeReg64 _ hne hm _)
    rw [e3] at hrun
    obtain ⟨rfl, rfl⟩ : R3 = r' ∧ m = m' := by simpa using hrun
    -- the machine
    have hc' : s.mem.canRead (Arm64.evalAddrMode s mode).1 sz.bytes = true := hmem ▸ hc
    have hx : Arm64.execLdr w sz sgn rt mode s =
        (postState s ((preState s mode).writeReg w rt val) mode).advancePC := by
      subst hv hmem
      cases mode <;>
        simp_all [Arm64.execLdr, Arm64.evalAddrMode, preState, postState, Arm64.State.writeReg]
      rw [writeReg64_comm _ (Ne.symm (hap _ rfl))]
    rw [hx]
    exact ⟨hA3.advancePC, by cases mode <;> rfl, by cases mode <;> rfl⟩
  · simp only [hc] at hrun
    cases hrun

end MachineChecked.ARM.Lift
