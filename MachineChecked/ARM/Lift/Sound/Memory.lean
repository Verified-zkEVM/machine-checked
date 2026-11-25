/-
  MachineChecked.ARM.Lift.Sound.Memory

  The lift of AArch64 against arm64-semantics: loads and stores.

  A load or a store of the lift faults where the machine's permission check fails, so where
  the operations run the machine does not fault on a permission. The machine faults also on a
  stack pointer that is not aligned, when it is the base of the access: that is a
  hypothesis here (`Aligned`). With write-back, the register loaded or stored is not the
  base (`Apart`): the architecture leaves that case unpredictable.

  ## Main results

  * `address_pre`, `address_post`: an addressing mode, before and after the access
  * `ldr_sound`, `ldrLit_sound`, `ldp_sound`, `str_sound`, `stp_sound`
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

/-- A write moved before two others. -/
theorem writeReg64_rotate (s : Arm64.State) {a b c : Arm64.Reg} (hac : a ≠ c) (hbc : b ≠ c)
    (u v x : BitVec 64) : ((s.writeReg64 a u).writeReg64 b v).writeReg64 c x =
      ((s.writeReg64 c x).writeReg64 a u).writeReg64 b v := by
  rw [writeReg64_comm _ hbc, writeReg64_comm s hac]

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

/-- **Before the access**: the operations run, the address is the machine's, and `t0` and
    `t1` are kept. -/
theorem address_pre (h : Agree regs m s) {mode : AddrMode} (hm : WfMode mode) :
    ∃ R1, run (address mode).1 regs m = some (R1, m) ∧
      (address mode).2.1.eval R1 = (Arm64.evalAddrMode s mode).1 ∧
      Agree R1 m (preState s mode) ∧ R1 .t0 = regs .t0 ∧ R1 .t1 = regs .t1 := by
  cases mode with
  | Offset b off =>
    exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm], h, rfl, rfl⟩
  | UnscaledOffset b off =>
    exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm], h, rfl, rfl⟩
  | PostIndex b off =>
    exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm], h, rfl, rfl⟩
  | RegOffset b i ext n =>
    have := extended_eval h .W64 ext hm.2.2 hm.2.1
    simp only [eval_trunc, reduceCtorEq, ite_false] at this
    exact ⟨regs, rfl, by simp [address, Arm64.evalAddrMode, rd_eval h hm.1, this], h, rfl, rfl⟩
  | PreIndex b off =>
    obtain ⟨R1, h1, h2, h3⟩ := wr_run h hm.1 (r := b) (add (rd b) (.imm off))
    simp only [eval_add, eval_imm, rd_eval h hm.1] at h2
    have hd : dest b ≠ .t0 ∧ dest b ≠ .t1 := by
      obtain ⟨-, hz⟩ := hm
      cases b with
      | gpr i => exact ⟨(ofGpr_ne i).2.2.2.2.2.1, (ofGpr_ne i).2.2.2.2.2.2.1⟩
      | sp => simp [dest]
      | xzr => exact absurd rfl hz
    exact ⟨R1, h1, by
      simp [address, Arm64.evalAddrMode, rd_eval h2 hm.1, readReg64_same s hm.1 hm.2], h2,
      h3 _ (Ne.symm hd.1), h3 _ (Ne.symm hd.2)⟩

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
  obtain ⟨R1, e1, ha, hA1, -, -⟩ := address_pre h hm
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

theorem dest_ne_t2 (r : Arm64.Reg) : dest r ≠ .t2 := by
  cases r with
  | gpr i => exact (ofGpr_ne i).2.2.2.2.2.2.2
  | sp => simp [dest]
  | xzr => simp [dest]

/-- The width of the accesses of a pair. -/
def pairSize (w : RegWidth) (sgn : Bool) : MemWidth :=
  if sgn then .W32 else match w with | .W32 => .W32 | .W64 => .X64

theorem pairSize_width (w : RegWidth) (sgn : Bool) :
    (if w = .W32 ∨ sgn then Width.b4 else Width.b8) = width (pairSize w sgn) := by
  cases w <;> cases sgn <;> rfl

/-- **`ldp` and `ldpsw`.** -/
theorem ldp_sound (h : Agree regs m s) (w : RegWidth) (sgn : Bool) {rt1 rt2 : Arm64.Reg}
    (h1 : Wf rt1) (h2 : Wf rt2) {mode : AddrMode} (hm : WfMode mode)
    (hal : Arm64.checkAddrSPAligned s mode = true)
    (hap : ∀ b ∈ writeback mode, rt1 ≠ b ∧ rt2 ≠ b) {r' : Reg → BitVec 64}
    {m' : Arm64.Memory}
    (hrun : run ((address mode).1 ++
      [.set .t2 (address mode).2.1,
       .load (dest rt1) (if w = .W32 ∨ sgn then Width.b4 else Width.b8) sgn (.reg .t2),
       .load (dest rt2) (if w = .W32 ∨ sgn then Width.b4 else Width.b8) sgn
        (add (.reg .t2) (num (if w = .W32 ∨ sgn then Width.b4 else Width.b8).bytes))] ++
      (address mode).2.2) regs m = some (r', m')) :
    Agree r' m' (Arm64.execLdp w sgn rt1 rt2 mode s) ∧
      (Arm64.execLdp w sgn rt1 rt2 mode s).status = s.status ∧
      (Arm64.execLdp w sgn rt1 rt2 mode s).pc = s.pc + 4#64 := by
  obtain ⟨R1, e1, ha, hA1, -, -⟩ := address_pre h hm
  have hmem : m = s.mem := h.mem
  generalize hea : (Arm64.evalAddrMode s mode).1 = ea at ha
  have hstep : (num (width (pairSize w sgn)).bytes : E).eval
      (updReg (updReg R1 .t2 ea) (dest rt1) (m.readSized (pairSize w sgn) sgn ea)) =
      BitVec.ofNat 64 (pairSize w sgn).bytes := by
    cases w <;> cases sgn <;> rfl
  rw [List.append_assoc, run_append, e1] at hrun
  simp only [Option.bind_some, List.cons_append, List.nil_append, pairSize_width, run_set,
    run_load, ha, eval_reg, eval_add, updReg_apply, ite_true, ite_false,
    Ne.symm (dest_ne_t2 rt1), hstep] at hrun
  by_cases c1 : m.canRead ea (pairSize w sgn).bytes = true
  · by_cases c2 : m.canRead (ea + BitVec.ofNat 64 (pairSize w sgn).bytes)
        (pairSize w sgn).bytes = true
    · simp only [c1, c2, ↓reduceIte] at hrun
      generalize hv1 : m.readSized (pairSize w sgn) sgn ea = v1 at hrun
      generalize hv2 : m.readSized (pairSize w sgn) sgn
        (ea + BitVec.ofNat 64 (pairSize w sgn).bytes) = v2 at hrun
      -- a value loaded is of the width it is written at
      have hw : ∀ (st : Arm64.State) (rt : Arm64.Reg) (a : BitVec 64),
          st.writeReg (if sgn then .W64 else w) rt (m.readSized (pairSize w sgn) sgn a) =
            st.writeReg64 rt (m.readSized (pairSize w sgn) sgn a) := by
        intro st rt a
        cases w <;> cases sgn <;> simp [Arm64.State.writeReg, pairSize, Arm64.Memory.readSized]
      have hA2 : Agree (updReg (updReg (updReg R1 .t2 ea) (dest rt1) v1) (dest rt2) v2) m
          (((preState s mode).writeReg (if sgn then .W64 else w) rt1 v1).writeReg
            (if sgn then .W64 else w) rt2 v2) := by
        rw [← hv1, ← hv2, hw, hw, hv1, hv2]
        exact ((hA1.scratch (.inr (.inr rfl)) ea).dest h1 v1).dest h2 v2
      obtain ⟨R3, e3, hA3⟩ := address_post (s := s) hA2 hm (fun b off hb => by
        subst hb
        obtain ⟨n1, n2⟩ := hap b rfl
        exact (readReg64_writeReg64 _ n2 hm _).trans (readReg64_writeReg64 _ n1 hm _))
      rw [e3] at hrun
      obtain ⟨rfl, rfl⟩ : R3 = r' ∧ m = m' := by simpa using hrun
      have hx : Arm64.execLdp w sgn rt1 rt2 mode s =
          (postState s (((preState s mode).writeReg (if sgn then .W64 else w) rt1 v1).writeReg
            (if sgn then .W64 else w) rt2 v2) mode).advancePC := by
        subst hv1 hv2 hmem hea
        have c1' := c1; have c2' := c2
        cases w <;> cases sgn <;> cases mode <;>
          simp_all [Arm64.execLdp, Arm64.evalAddrMode, preState, postState, pairSize,
            Arm64.State.writeReg]
        all_goals
          exact congrArg _ (writeReg64_rotate s (hap _ rfl).1 (hap _ rfl).2 _ _ _).symm
      rw [hx]
      exact ⟨hA3.advancePC, by cases mode <;> rfl, by cases mode <;> rfl⟩
    · simp only [c1, c2] at hrun
      cases hrun
  · simp only [c1] at hrun
    cases hrun

/-- The width of a literal load. -/
def litSize (w : RegWidth) (sgn : Bool) : MemWidth :=
  if sgn then .W32 else match w with | .W32 => .W32 | .W64 => .X64

/-- **`ldr` and `ldrsw` of a literal.** The signed form is of 64 bits. -/
theorem ldrLit_sound (h : Agree regs m s) (w : RegWidth) (sgn : Bool) {rt : Arm64.Reg}
    (hrt : Wf rt) (off : BitVec 64) (hw : sgn = true → w = .W64) {r' : Reg → BitVec 64}
    {m' : Arm64.Memory}
    (hrun : run [.load (dest rt) (if w = .W64 ∧ !sgn then Width.b8 else Width.b4) sgn
      (.imm (s.pc + off))] regs m = some (r', m')) :
    Agree r' m' (Arm64.execLdrLit w (litSize w sgn) sgn rt off s) ∧
      (Arm64.execLdrLit w (litSize w sgn) sgn rt off s).status = s.status ∧
      (Arm64.execLdrLit w (litSize w sgn) sgn rt off s).pc = s.pc + 4#64 := by
  have hmem : m = s.mem := h.mem
  have hsz : (if w = .W64 ∧ !sgn then Width.b8 else Width.b4) = width (litSize w sgn) := by
    cases w <;> cases sgn <;> rfl
  simp only [hsz, run_load, eval_imm] at hrun
  by_cases hc : m.canRead (s.pc + off) (litSize w sgn).bytes = true
  · simp only [hc, ↓reduceIte] at hrun
    obtain ⟨rfl, rfl⟩ : updReg regs (dest rt) (m.readSized (litSize w sgn) sgn (s.pc + off)) = r' ∧
        m = m' := by simpa [run] using hrun
    have hx : Arm64.execLdrLit w (litSize w sgn) sgn rt off s =
        (s.writeReg64 rt (m.readSized (litSize w sgn) sgn (s.pc + off))).advancePC := by
      subst hmem
      cases w <;> cases sgn <;>
        simp_all [Arm64.execLdrLit, litSize, Arm64.State.writeReg, Arm64.Memory.readSized]
    rw [hx]
    exact ⟨(h.dest hrt _).advancePC, rfl, rfl⟩
  · simp only [hc] at hrun
    cases hrun

/-! ## Permissions after a store -/

theorem perm_write8 (mem : Arm64.Memory) (a : BitVec 64) (v : BitVec 8) (b : BitVec 64) :
    (mem.write8 a v).perm b = mem.perm b := by
  simp only [Arm64.Memory.perm, Arm64.Memory.write8, Arm64.Memory.rawPerm]
  by_cases hb : b = a
  · subst hb
    simp only [ite_true]
    rcases mem.cells b with _ | ⟨_ | p, c⟩ <;> rfl
  · simp [hb]

theorem allPerm_congr {m1 m2 : Arm64.Memory} (h : ∀ b, m1.perm b = m2.perm b)
    (p : Option Arm64.Perm → Bool) (a : BitVec 64) (n : Nat) :
    m1.allPerm p a n = m2.allPerm p a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [Arm64.Memory.allPerm, h, ih]

/-- **A store does not change what may be written.** -/
theorem canWrite_writeSized (mem : Arm64.Memory) (sz : MemWidth) (a v b : BitVec 64) (n : Nat) :
    (mem.writeSized sz a v).canWrite b n = mem.canWrite b n := by
  unfold Arm64.Memory.canWrite
  apply allPerm_congr
  intro c
  cases sz <;>
    simp [Arm64.Memory.writeSized, Arm64.Memory.write16, Arm64.Memory.write32,
      Arm64.Memory.write64, perm_write8]

/-! ## Stores -/

/-- **`str`, `stur` and their narrow forms.** -/
theorem str_sound (h : Agree regs m s) (sz : MemWidth) {rt : Arm64.Reg} (hrt : Wf rt)
    {mode : AddrMode} (hm : WfMode mode) (hal : Arm64.checkAddrSPAligned s mode = true)
    (hap : ∀ b ∈ writeback mode, rt ≠ b) {r' : Reg → BitVec 64} {m' : Arm64.Memory}
    (hrun : run ((address mode).1 ++ [.store (width sz) (address mode).2.1 (rd rt)] ++
      (address mode).2.2) regs m = some (r', m')) :
    Agree r' m' (Arm64.execStr sz rt mode s) ∧
      (Arm64.execStr sz rt mode s).status = s.status ∧
      (Arm64.execStr sz rt mode s).pc = s.pc + 4#64 := by
  obtain ⟨R1, e1, ha, hA1, -, -⟩ := address_pre h hm
  have hv : (rd rt).eval R1 = s.readReg64 rt := by
    rw [rd_eval hA1 hrt]
    cases mode <;> first | rfl | exact readReg64_writeReg64 _ (Ne.symm (hap _ rfl)) hrt _
  rw [List.append_assoc, run_append, e1] at hrun
  simp only [Option.bind_some, List.cons_append, List.nil_append, run_store, ha, hv] at hrun
  have hmem : m = s.mem := h.mem
  by_cases hc : m.canWrite (Arm64.evalAddrMode s mode).1 sz.bytes = true
  · simp only [hc, ↓reduceIte] at hrun
    generalize hm1 : m.writeSized sz (Arm64.evalAddrMode s mode).1 (s.readReg64 rt) = m1 at hrun
    obtain ⟨R3, e3, hA3⟩ := address_post (s := s) (hA1.setMem m1) hm (fun b off hb => by
      subst hb; rfl)
    rw [e3] at hrun
    obtain ⟨rfl, rfl⟩ : R3 = r' ∧ m1 = m' := by simpa using hrun
    have hc' : s.mem.canWrite (Arm64.evalAddrMode s mode).1 sz.bytes = true := hmem ▸ hc
    have hx : Arm64.execStr sz rt mode s =
        (postState s ((preState s mode).setMem m1) mode).advancePC := by
      subst hm1 hmem
      cases mode <;>
        simp_all [Arm64.execStr, Arm64.evalAddrMode, preState, postState] <;> rfl
    rw [hx]
    exact ⟨hA3.advancePC, by cases mode <;> rfl, by cases mode <;> rfl⟩
  · simp only [hc] at hrun
    cases hrun

/-- **`stp`.** -/
theorem stp_sound (h : Agree regs m s) (w : RegWidth) {rt1 rt2 : Arm64.Reg} (h1 : Wf rt1)
    (h2 : Wf rt2) {mode : AddrMode} (hm : WfMode mode)
    (hal : Arm64.checkAddrSPAligned s mode = true) {r' : Reg → BitVec 64} {m' : Arm64.Memory}
    (hrun : run ([.set .t0 (rd rt1), .set .t1 (rd rt2)] ++ (address mode).1 ++
      [.store (if w = .W32 then Width.b4 else Width.b8) (address mode).2.1 (.reg .t0),
       .store (if w = .W32 then Width.b4 else Width.b8)
        (add (address mode).2.1 (num (if w = .W32 then Width.b4 else Width.b8).bytes))
        (.reg .t1)] ++ (address mode).2.2) regs m = some (r', m')) :
    Agree r' m' (Arm64.execStp w rt1 rt2 mode s) ∧
      (Arm64.execStp w rt1 rt2 mode s).status = s.status ∧
      (Arm64.execStp w rt1 rt2 mode s).pc = s.pc + 4#64 := by
  have hmem : m = s.mem := h.mem
  have hA0 : Agree (updReg (updReg regs .t0 (s.readReg64 rt1)) .t1 (s.readReg64 rt2)) m s :=
    (h.scratch (.inl rfl) _).scratch (.inr (.inl rfl)) _
  obtain ⟨R1, e1, ha, hA1, t0, t1⟩ := address_pre hA0 hm
  have t0 : R1 .t0 = s.readReg64 rt1 := t0
  have t1 : R1 .t1 = s.readReg64 rt2 := t1
  generalize hea : (Arm64.evalAddrMode s mode).1 = ea at ha
  have hsz : (if w = .W32 then Width.b4 else Width.b8) = width (pairSize w false) := by
    cases w <;> rfl
  have hstep : (num (width (pairSize w false)).bytes : E).eval R1 =
      BitVec.ofNat 64 (pairSize w false).bytes := by cases w <;> rfl
  simp only [List.cons_append, List.nil_append, List.append_assoc, run_set, rd_eval h h1] at hrun
  rw [show (rd rt2).eval (updReg regs .t0 (s.readReg64 rt1)) = s.readReg64 rt2 from
    rd_eval (h.scratch (.inl rfl) _) h2, run_append, e1] at hrun
  simp only [Option.bind_some, hsz, run_store, ha, eval_reg, eval_add, hstep, t0, t1] at hrun
  by_cases c1 : m.canWrite ea (pairSize w false).bytes = true
  · simp only [c1, ↓reduceIte] at hrun
    generalize hm1 : m.writeSized (pairSize w false) ea (s.readReg64 rt1) = m1 at hrun
    by_cases c2 : m1.canWrite (ea + BitVec.ofNat 64 (pairSize w false).bytes)
        (pairSize w false).bytes = true
    · simp only [c2, ↓reduceIte] at hrun
      generalize hm2 : m1.writeSized (pairSize w false)
        (ea + BitVec.ofNat 64 (pairSize w false).bytes) (s.readReg64 rt2) = m2 at hrun
      obtain ⟨R3, e3, hA3⟩ := address_post (s := s) (hA1.setMem m2) hm (fun b off hb => by
        subst hb; rfl)
      rw [e3] at hrun
      obtain ⟨rfl, rfl⟩ : R3 = r' ∧ m2 = m' := by simpa using hrun
      have c2' : m.canWrite (ea + BitVec.ofNat 64 (pairSize w false).bytes)
          (pairSize w false).bytes = true := by
        rw [← hm1, canWrite_writeSized] at c2; exact c2
      have hx : Arm64.execStp w rt1 rt2 mode s =
          (postState s ((preState s mode).setMem m2) mode).advancePC := by
        subst hm2 hm1 hmem hea
        cases w <;> cases mode <;>
          simp only [Arm64.evalAddrMode, pairSize, Bool.false_eq_true, ite_false] at c1 c2' <;>
          simp [Arm64.execStp, Arm64.evalAddrMode, preState, postState, pairSize, hal, c1, c2']
            <;> rfl
      rw [hx]
      exact ⟨hA3.advancePC, by cases mode <;> rfl, by cases mode <;> rfl⟩
    · simp only [c2] at hrun
      cases hrun
  · simp only [c1] at hrun
    cases hrun

end MachineChecked.ARM.Lift
