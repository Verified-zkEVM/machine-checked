/-
  MachineChecked.RiscV.Lprog.Transfer

  **The lift is correct**: `SafeN` proved at Lprog for a lifted program gives `SafeN` over
  riscv-zkvm's `stepSp1`.

  `Sim fs exit s t` relates an Lprog state of the lifted program to a machine state: they
  agree on registers, memory, code and the I/O fields; the machine holds every function of
  the program at its address; and the activations correspond to the machine's control state:
  the innermost one's counter to the pc (label or instruction `k` of a function at
  `base + 4k`), each other one's counter to the return value of the activation above it, and
  the outermost one returns to `exit`. Return values below the outermost are aligned, as
  `jalr` needs; the outermost one returns to `exit &&& ~~~1`, where `jalr` lands.

  One machine step from a simulated state is matched at Lprog (`back_step`) by at most two
  steps, a label and the instruction, ending in a simulated state, or in a returned program
  with the machine at `exit`; a machine that is stuck accepting is matched by an Lprog state
  that accepts. An Lprog step to `wrong` matches nothing, and the Lprog judgement rules it
  out. So, by induction on the machine's budget, `SafeN` at Lprog at every budget gives
  `SafeN` over `stepSp1` (`transfer`), and from a function's entry (`SafeN.of_lift`) the
  machine is safe if it is safe from every state the function may return to `ra` in.

  ## Main definitions

  * `Sim`, `ProgOk`

  ## Main results

  * `back_step`: one machine step, matched at Lprog
  * `transfer`, `SafeN.of_lift`: the transfer theorem
-/

import MachineChecked.RiscV.Lprog.Lift

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog
open MachineChecked.Ascent (Outcome)

/-! ## The machine side -/

theorem Agree.refl (t : MachineState) : Agree t t := ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Agree.symm {t u : MachineState} (h : Agree t u) : Agree u t :=
  ⟨fun r => (h.regs r).symm, fun a => (h.mem a).symm, h.code.symm, h.committed.symm,
    h.publicValues.symm, h.privateInput.symm, h.inputBufBase.symm⟩

theorem Agree.trans {t u v : MachineState} (h₁ : Agree t u) (h₂ : Agree u v) : Agree t v :=
  ⟨fun r => (h₁.regs r).trans (h₂.regs r), fun a => (h₁.mem a).trans (h₂.mem a),
    h₁.code.trans h₂.code, h₁.committed.trans h₂.committed, h₁.publicValues.trans h₂.publicValues,
    h₁.privateInput.trans h₂.privateInput, h₁.inputBufBase.trans h₂.inputBufBase⟩

/-- A machine state agrees with itself seen through Lprog's register file. -/
theorem agree_ofParts_regsOf (t : MachineState) : Agree (ofParts (regsOf t) t) t := by
  refine ⟨fun r => ?_, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [getReg_ofParts]
  split
  · next h => subst h; rfl
  · rfl

/-- Writing a register in Lprog agrees with writing it in an agreeing machine. -/
theorem agree_set' {regs : Reg → BitVec 64} {m u : MachineState} (hag : Agree (ofParts regs m) u)
    (rd : Reg) {v v' : Word} (p : Word) (h : v = v') :
    Agree (ofParts (updReg regs rd v) m) ((u.setReg rd v').setPC p) := by
  subst h
  refine ⟨fun r => ?_, fun a => by simpa using hag.mem a, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  all_goals first
    | (rw [show ((u.setReg rd v).setPC p).code = u.code by cases rd <;> rfl]; exact hag.code)
    | (rw [show ((u.setReg rd v).setPC p).committed = u.committed by cases rd <;> rfl]; exact hag.committed)
    | (rw [show ((u.setReg rd v).setPC p).publicValues = u.publicValues by cases rd <;> rfl];
       exact hag.publicValues)
    | (rw [show ((u.setReg rd v).setPC p).privateInput = u.privateInput by cases rd <;> rfl];
       exact hag.privateInput)
    | (rw [show ((u.setReg rd v).setPC p).inputBufBase = u.inputBufBase by cases rd <;> rfl];
       exact hag.inputBufBase)
    | skip
  rw [getReg_ofParts, MachineState.getReg_setPC, getReg_setReg]
  by_cases h0 : r = .x0
  · subst h0
    simp only [getReg_x0, ite_true]
    split
    · next h => exact absurd h.1.symm h.2
    · rfl
  · by_cases hr : r = rd
    · subst hr; simp [h0, updReg]
    · have := hag.regs r
      rw [getReg_ofParts] at this
      simp only [h0, ite_false] at this
      simp [h0, hr, updReg, this]

/-- An operation advances the pc by four. -/
theorem pc_execInstrBr_opn {t : MachineState} {i : Instr} (h : opnOk i = true) :
    (execInstrBr t i).pc = t.pc + 4 := by
  cases i <;> simp_all [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, execInstrBr, pc_setPC]

/-- An operation's code map is unchanged. -/
theorem code_execInstrBr_opn {t : MachineState} {i : Instr} (h : opnOk i = true) :
    (execInstrBr t i).code = t.code := by
  cases i <;> simp_all [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, execInstrBr,
    MachineState.setByte, MachineState.setHalfword, MachineState.setWord32]

theorem not_ecall_of_opnOk {i : Instr} (h : opnOk i = true) : i ≠ .ECALL := by
  rintro rfl; simp [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS] at h

/-- `stepSp1` on an operation: the memory check, then `execInstrBr`. -/
theorem stepSp1_opn_eq {t : MachineState} {i : Instr} (hf : t.code t.pc = some i)
    (h : opnOk i = true) : stepSp1 t = if memOkSp1 t i then some (execInstrBr t i) else none := by
  unfold stepSp1
  rw [hf]
  cases i <;> simp_all [opnOk, isPure, isStraight, isCSRS, Instr.isMemAccess, memOkSp1, memAccess]

/-- `stepSp1` on an instruction that neither accesses memory nor calls the environment. -/
theorem stepSp1_ctl {t : MachineState} {i : Instr} (hf : t.code t.pc = some i)
    (hm : i.isMemAccess = false) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK) :
    stepSp1 t = some (execInstrBr t i) :=
  stepSp1_plain hf hm he hb

/-- An `ecall` that steps advances the pc by four. -/
theorem pc_sp1Ecall {s s' : MachineState} (hf : s.code s.pc = some .ECALL) (h : sp1Ecall s = some s') :
    s'.pc = s.pc + 4 := by
  simp only [sp1Ecall] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; simp [pc_setPC]
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; simp [hintLen, pc_setPC]
    · split at h
      · simp only [hintRead] at h
        repeat' split at h
        all_goals first | (simp at h; done) | (simp only [Option.some.injEq] at h; subst h; simp [pc_setPC])
      · split at h
        · simp only [Option.some.injEq] at h; subst h; simp [pc_setPC]
        · split at h
          · simp only [Option.some.injEq] at h; subst h; simp [pc_setPC]
          · split at h
            · unfold step at h
              rw [hf] at h
              simp only at h
              repeat' split at h
              all_goals first | (simp at h; done) | (simp only [Option.some.injEq] at h; subst h; simp [pc_setPC, execInstrBr])
            · simp at h

/-- The fetch at instruction `k` of a function held at `base`. -/
theorem fetch_at {base : Word} {prog : List Instr} {t : MachineState} {k : Nat}
    (hcode : CodeAt base (prog.map some) t) (hk : k < prog.length)
    (hpc : t.pc = base + BitVec.ofNat 64 (4 * k)) : t.code t.pc = some prog[k] := by
  rw [hpc, hcode k (by simpa using hk)]
  simp [hk]

/-- The address a well-formed jump reaches. -/
theorem jump_addr {base : Word} {k len : Nat} {off : Word} (h : jumpOk k len off = true) :
    base + BitVec.ofNat 64 (4 * k) + off = base + BitVec.ofNat 64 (4 * tgt k off) ∧ tgt k off < len := by
  simp only [jumpOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h4, h0⟩, hlt⟩ := h
  have ht : (tgt k off : Int) = (k : Int) + off.toInt / 4 := by
    unfold tgt; omega
  refine ⟨?_, by unfold tgt; omega⟩
  rw [BitVec.add_assoc]
  congr 1
  rw [← BitVec.ofInt_natCast 64 (4 * k), ← BitVec.ofInt_natCast 64 (4 * tgt k off),
    ← BitVec.ofInt_toInt (x := off), ← BitVec.ofInt_add, BitVec.ofInt_toInt]
  congr 1
  push_cast
  omega

/-- A register operand reads what an agreeing machine's register holds. -/
theorem opnd_val_of_agree {regs : Reg → BitVec 64} {m t : MachineState}
    (h : Agree (ofParts regs m) t) (r : Reg) : operandVal regs (opnd r) = some (t.getReg r) := by
  rw [opnd_val regs m, h.regs r]

theorem rv_eval_of_agree {regs : Reg → BitVec 64} {m t : MachineState}
    (h : Agree (ofParts regs m) t) (r : Reg) : (rv r).eval regs = t.getReg r := by
  rw [rv_eval regs m, h.regs r]

theorem jalrTgt_eval {regs : Reg → BitVec 64} {m t : MachineState}
    (h : Agree (ofParts regs m) t) (rs : Reg) (off : BitVec 12) :
    (jalrTgt rs off).eval regs = (t.getReg rs + signExtend12 off) &&& ~~~1#64 := by
  simp [jalrTgt, addr, Expr.eval, BinOp.eval, se12, rv_eval_of_agree h]

/-! ## The simulation -/

/-- A program the lift handles: every function at an address that is a multiple of four. -/
abbrev ProgOk (fs : List Fn) : Prop := ∀ f ∈ fs, f.base.toNat % 4 = 0

/-- Activation `fr` stands for the machine at address `a`. -/
def FrameAt (fs : List Fn) (fr : Frame) (a : Word) : Prop :=
  ∃ f, fs[fr.fn]? = some f ∧ fr.pc ≤ 2 * f.prog.length ∧ a = f.base + BitVec.ofNat 64 (4 * (fr.pc / 2))

/-- The return value of an activation over `rest` is aligned, as `jalr` needs, unless it is the
    outermost one (whose return lands at `exit &&& ~~~1`). -/
def RetOk (rest : List Frame) (ret : Word) : Prop := rest ≠ [] → ret &&& ~~~1#64 = ret

/-- The activations stand for the machine at `a`, each returning where the next one resumes,
    and the outermost to `exit`. -/
def Chain (fs : List Fn) (exit : Word) : List Frame → Word → Prop
  | [], a => a = exit
  | fr :: rest, a => FrameAt fs fr a ∧ RetOk rest fr.ret ∧ Chain fs exit rest fr.ret

/-- **The simulation**: an Lprog state of the lifted program `fs` that has not returned
    stands for a machine state. -/
structure Sim (fs : List Fn) (exit : Word) (s : State rvIsa) (t : MachineState) : Prop where
  agree : Agree (ofParts s.regs s.m) t
  code : ∀ f ∈ fs, CodeAt f.base (f.prog.map some) t
  chain : Chain fs exit s.stack t.pc
  ne : s.stack ≠ []

/-- The address of the next instruction. -/
theorem addr_succ (base : Word) (k : Nat) :
    base + BitVec.ofNat 64 (4 * (k + 1)) = base + BitVec.ofNat 64 (4 * k) + 4 := by
  rw [BitVec.add_assoc, show 4 * (k + 1) = 4 * k + 4 by omega, BitVec.ofNat_add]
  rfl

/-- An even value is aligned for `jalr`. -/
theorem aligned_of_even {x : Word} (h : x.toNat % 2 = 0) : x &&& ~~~1#64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  by_cases h0 : i = 0
  · subst h0
    have : x.getLsbD 0 = false := by
      simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two, h]
    rw [this]; rfl
  · simp [BitVec.getLsbD_one, h0]

/-- An address after an aligned base is aligned. -/
theorem aligned_add {base : Word} (hb : base.toNat % 4 = 0) (j : Nat) :
    (base + BitVec.ofNat 64 (4 * j)) &&& ~~~1#64 = base + BitVec.ofNat 64 (4 * j) :=
  aligned_of_even (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

/-! ## The Lprog side -/

/-- Safe at Lprog along every run, at every budget. -/
def AllSafe (fs : List Fn) (Q : State rvIsa → Prop) (s : State rvIsa) : Prop :=
  ∀ k, LSafeN fs (fun _ => True) k Q s

section AllSafe

variable {fs : List Fn} {Q : State rvIsa → Prop} {s t : State rvIsa}

theorem AllSafe.next (h : AllSafe fs Q s) (hs : rvIsa.step (liftProg fs) sp1Ctx s (.ok (t, []))) :
    AllSafe fs Q t :=
  fun k => Ascent.SafeN.next trivial ⟨[], hs⟩ (h (k + 1))

theorem AllSafe.not_wrong (h : AllSafe fs Q s) (hs : rvIsa.step (liftProg fs) sp1Ctx s .wrong) : False :=
  Ascent.SafeN.not_wrong trivial hs (h 2)

theorem AllSafe.acc (h : AllSafe fs Q s) (ha : rvIsa.accept (liftProg fs) sp1Ctx s) : Q s :=
  Ascent.SafeN.of_accept trivial ha (h 1)

end AllSafe

/-- What a machine step to `t'` is at Lprog: a simulated state safe at every budget, or a
    returned program with the machine at `exit`. -/
def Next (fs : List Fn) (exit : Word) (Q : State rvIsa → Prop) (t' : MachineState) : Prop :=
  (∃ s', Sim fs exit s' t' ∧ AllSafe fs Q s') ∨
    (∃ s', s'.stack = [] ∧ Agree (ofParts s'.regs s'.m) t' ∧ t'.pc = exit &&& ~~~1#64 ∧ Q s')

/-- The innermost activation `fr` of a simulated state is at instruction `k` of function `f`. -/
structure At (fs : List Fn) (exit : Word) (fr : Frame) (rest : List Frame) (regs : Reg → BitVec 64)
    (m t : MachineState) (f : Fn) (k : Nat) : Prop where
  sim : Sim fs exit ⟨fr :: rest, regs, m⟩ t
  hf : fs[fr.fn]? = some f
  hk : k < f.prog.length
  hpc : fr.pc = 2 * k + 1
  tpc : t.pc = f.base + BitVec.ofNat 64 (4 * k)

namespace At

variable {fs : List Fn} {exit : Word} {fr : Frame} {rest : List Frame} {regs : Reg → BitVec 64}
  {m t : MachineState} {f : Fn} {k : Nat}

theorem fetch (h : At fs exit fr rest regs m t f k) : t.code t.pc = some (f.prog[k]'h.hk) :=
  fetch_at (h.sim.code f (List.mem_of_getElem? h.hf)) h.hk h.tpc

theorem body (h : At fs exit fr rest regs m t f k) :
    ((liftProg fs)[fr.fn]?.map (·.body)) = some (bodyOf fs f) ∧
      (bodyOf fs f)[fr.pc]? = some (liftI fs f.prog.length k (f.base + BitVec.ofNat 64 (4 * k)) (f.prog[k]'h.hk)) := by
  refine ⟨by simp [getElem?_liftProg h.hf, liftFn], ?_⟩
  rw [h.hpc]; exact body_odd fs f h.hk

/-- The step of the lifted instruction. -/
theorem step_iff (h : At fs exit fr rest regs m t f k) (o : Outcome (State rvIsa × List Unit)) :
    rvIsa.step (liftProg fs) sp1Ctx ⟨fr :: rest, regs, m⟩ o ↔
      rvIsa.stepI (liftProg fs) sp1Ctx (bodyOf fs f) fr rest regs m
        (liftI fs f.prog.length k (f.base + BitVec.ofNat 64 (4 * k)) (f.prog[k]'h.hk)) o :=
  MachineChecked.Lprog.SafeN.step_eq (getElem?_liftProg h.hf) h.body.2 o

/-- Machine states after a step that keeps the code still hold the program. -/
theorem code' (h : At fs exit fr rest regs m t f k) {t' : MachineState} (hc : t'.code = t.code) :
    ∀ g ∈ fs, CodeAt g.base (g.prog.map some) t' :=
  fun g hg => codeAt_of_code_eq hc (h.sim.code g hg)

/-- Fall through to the next instruction. -/
theorem next (h : At fs exit fr rest regs m t f k) {r' : Reg → BitVec 64} {m' t' : MachineState}
    (hag : Agree (ofParts r' m') t') (hc : t'.code = t.code) (hpc : t'.pc = t.pc + 4) :
    Sim fs exit ⟨fr.at (fr.pc + 1) :: rest, r', m'⟩ t' := by
  obtain ⟨⟨-, hfr, hchain⟩, -⟩ := And.intro h.sim.chain h.sim.ne
  refine ⟨hag, h.code' hc, ⟨⟨f, h.hf, by simp [h.hpc]; have := h.hk; omega, ?_⟩, hfr, hchain⟩, by simp⟩
  rw [hpc, h.tpc, Frame.at_pc, h.hpc, show (2 * k + 1 + 1) / 2 = k + 1 by omega, addr_succ]

/-- Jump to label `l` of the function. -/
theorem jump (h : At fs exit fr rest regs m t f k) {r' : Reg → BitVec 64} {m' t' : MachineState}
    (hag : Agree (ofParts r' m') t') (hc : t'.code = t.code) {l : Nat} (hl : l < f.prog.length)
    (hpc : t'.pc = f.base + BitVec.ofNat 64 (4 * l)) :
    Sim fs exit ⟨fr.at (2 * l) :: rest, r', m'⟩ t' := by
  obtain ⟨-, hfr, hchain⟩ := h.sim.chain
  refine ⟨hag, h.code' hc, ⟨⟨f, h.hf, by simp; omega, ?_⟩, hfr, hchain⟩, by simp⟩
  rw [hpc, Frame.at_pc, show 2 * l / 2 = l by omega]

/-- Enter function `g` with return value `ret` over activations `rest'`. -/
theorem enter (h : At fs exit fr rest regs m t f k) {r' : Reg → BitVec 64} {m' t' : MachineState}
    (hag : Agree (ofParts r' m') t') (hc : t'.code = t.code) {g : Nat} {fn : Fn}
    (hg : fs[g]? = some fn) (hpc : t'.pc = fn.base) {ret top : Word} {rest' : List Frame}
    (hret : RetOk rest' ret) (hchain : Chain fs exit rest' ret) :
    Sim fs exit ⟨⟨g, 0, ret, top⟩ :: rest', r', m'⟩ t' :=
  ⟨hag, h.code' hc, ⟨⟨fn, hg, Nat.zero_le _, by simp [hpc]⟩, hret, hchain⟩, by simp⟩

/-- The activations below a call: the caller resumes after the call. -/
theorem below (h : At fs exit fr rest regs m t f k) :
    Chain fs exit (fr.at (fr.pc + 1) :: rest) (t.pc + 4) := by
  obtain ⟨-, hfr, hchain⟩ := h.sim.chain
  refine ⟨⟨f, h.hf, by simp [h.hpc]; have := h.hk; omega, ?_⟩, hfr, hchain⟩
  rw [h.tpc, Frame.at_pc, h.hpc, show (2 * k + 1 + 1) / 2 = k + 1 by omega, addr_succ]

/-- The return value of a call is aligned. -/
theorem ret_aligned (h : At fs exit fr rest regs m t f k) (hok : ProgOk fs) :
    (t.pc + 4) &&& ~~~1#64 = t.pc + 4 := by
  rw [h.tpc, ← addr_succ]
  exact aligned_add (hok f (List.mem_of_getElem? h.hf)) _

end At

/-! ## One machine step, matched at Lprog -/

section Back

variable {fs : List Fn} {exit : Word} {Q : State rvIsa → Prop} {fr : Frame} {rest : List Frame}
  {regs : Reg → BitVec 64} {m t : MachineState} {f : Fn} {k : Nat} {i : Instr}

/-- The step of the lifted instruction `L` at the innermost activation. -/
abbrev StepIs (fs : List Fn) (fr : Frame) (rest : List Frame) (regs : Reg → BitVec 64) (m : MachineState)
    (f : Fn) (L : LinstrR (Op Reg) Reg) : Prop :=
  ∀ o, rvIsa.step (liftProg fs) sp1Ctx ⟨fr :: rest, regs, m⟩ o ↔
    rvIsa.stepI (liftProg fs) sp1Ctx (bodyOf fs f) fr rest regs m L o

theorem back_abort (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩) (hstep : StepIs fs fr rest regs m f .Labort) :
    False :=
  hL.not_wrong ((hstep _).2 rfl)

theorem back_opn (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩) (h : At fs exit fr rest regs m t f k)
    (hfetch : t.code t.pc = some i) (hop : opnOk i = true)
    (hstep : StepIs fs fr rest regs m f (.Lopn (opOf i))) :
    ∀ t', stepSp1 t = some t' → Next fs exit Q t' := by
  intro t' ht'
  rw [stepSp1_opn_eq hfetch hop] at ht'
  have hag := h.sim.agree
  have hspec := opOf_spec hop regs m
  split at ht'
  · next hok =>
    cases ht'
    cases he : (opOf i).eval rvMem regs m with
    | none =>
      simp only [he] at hspec
      rw [hag.memOkSp1 i, hok] at hspec
      cases hspec
    | some rm =>
      obtain ⟨r', m'⟩ := rm
      simp only [he] at hspec
      exact .inl ⟨_, h.next (hspec.2.trans (hag.execInstrBr hop)) (code_execInstrBr_opn hop)
        (pc_execInstrBr_opn hop), hL.next ((hstep _).2 (by simp [Isa.stepI, he]))⟩
  · cases ht'

theorem back_auipc (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩) (h : At fs exit fr rest regs m t f k)
    {rd : Reg} {imm : BitVec 20} (hfetch : t.code t.pc = some (.AUIPC rd imm))
    (hstep : StepIs fs fr rest regs m f
      (.Lopn (.set rd (.imm (f.base + BitVec.ofNat 64 (4 * k) + auipcOff imm))))) :
    ∀ t', stepSp1 t = some t' → Next fs exit Q t' := by
  intro t' ht'
  rw [stepSp1_ctl hfetch rfl (by simp) (by simp)] at ht'
  cases ht'
  exact .inl ⟨_, h.next (agree_set' h.sim.agree rd _ (by rw [h.tpc])) (by simp [execInstrBr])
    (by simp [execInstrBr, pc_setPC]), hL.next ((hstep _).2 (by simp [Isa.stepI, Op.eval, Expr.eval, auipcOff]))⟩

theorem back_branch (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩) (h : At fs exit fr rest regs m t f k)
    (hfetch : t.code t.pc = some i) (hm : i.isMemAccess = false) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    {op : String} {a b : Reg} {off : BitVec 13} {c : Bool}
    (hc : cmpEval op (t.getReg a) (t.getReg b) = some c)
    (hexec : execInstrBr t i = if c then t.setPC (t.pc + signExtend13 off) else t.setPC (t.pc + 4))
    (hstep : StepIs fs fr rest regs m f (liftBr k f.prog.length op a b off)) :
    ∀ t', stepSp1 t = some t' → Next fs exit Q t' := by
  intro t' ht'
  rw [stepSp1_ctl hfetch hm he hb, hexec] at ht'
  cases ht'
  have hag := h.sim.agree
  unfold liftBr at hstep
  split at hstep
  · next hj =>
    obtain ⟨haddr, hlt⟩ := jump_addr (base := f.base) hj
    have hcond : condEval (.cmp op (opnd a) (opnd b)) regs = some c := by
      simp [condEval, opnd_val_of_agree hag, hc]
    cases c
    · exact .inl ⟨_, h.next (hag.trans (agree_setPC t _)) (by simp) (by simp [pc_setPC]),
        hL.next ((hstep _).2 (by simp [Isa.stepI, hcond]))⟩
    · exact .inl ⟨_, h.jump (hag.trans (agree_setPC t _)) (by simp) hlt
        (by simp only [pc_setPC]; rw [h.tpc, haddr]),
        hL.next ((hstep _).2 (by simp [Isa.stepI, hcond, labelIdx_body fs f hlt]))⟩
  · exact (back_abort hL hstep).elim

theorem back_jal (hok : ProgOk fs) (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩)
    (h : At fs exit fr rest regs m t f k) {rd : Reg} {off : BitVec 21}
    (hfetch : t.code t.pc = some (.JAL rd off))
    (hstep : StepIs fs fr rest regs m f
      (liftJal fs f.prog.length k (f.base + BitVec.ofNat 64 (4 * k)) rd off)) :
    ∀ t', stepSp1 t = some t' → Next fs exit Q t' := by
  intro t' ht'
  rw [stepSp1_ctl hfetch rfl (by simp) (by simp)] at ht'
  cases ht'
  have hag := h.sim.agree
  unfold liftJal at hstep
  by_cases h0 : rd = .x0
  · subst h0
    rw [ite_eq_left rfl] at hstep
    have hag' : Agree (ofParts regs m) (execInstrBr t (.JAL .x0 off)) := hag.trans (agree_setPC t _)
    split at hstep
    · next hj =>
      obtain ⟨haddr, hlt⟩ := jump_addr (base := f.base) hj
      exact .inl ⟨_, h.jump hag' (by simp [execInstrBr]) hlt
        (by simp only [execInstrBr, pc_setPC]; rw [h.tpc, haddr]),
        hL.next ((hstep _).2 (by simp [Isa.stepI, labelIdx_body fs f hlt]))⟩
    · split at hstep
      · next g hg =>
        obtain ⟨fn, hfn, hbase⟩ := entryOf_spec hg
        have hglt : g < fs.length := (List.getElem?_eq_some_iff.mp hfn).1
        by_cases hsp : regs .x2 = fr.top
        · exact .inl ⟨_, h.enter (top := fr.top) hag' (by simp [execInstrBr]) hfn
            (by simp only [execInstrBr, pc_setPC]; rw [h.tpc, hbase]) h.sim.chain.2.1 h.sim.chain.2.2,
            hL.next ((hstep _).2 (by simp [Isa.stepI, hsp, callee_direct hglt]))⟩
        · exact (hL.not_wrong ((hstep _).2 (by simp [Isa.stepI, hsp]))).elim
      · exact (back_abort hL hstep).elim
  · rw [ite_eq_right h0] at hstep
    by_cases h1 : rd = .x1
    · subst h1
      rw [ite_eq_left rfl] at hstep
      split at hstep
      · next g hg =>
        obtain ⟨fn, hfn, hbase⟩ := entryOf_spec hg
        have hglt : g < fs.length := (List.getElem?_eq_some_iff.mp hfn).1
        have hret := h.ret_aligned hok
        have hbelow := h.below
        rw [h.tpc] at hret hbelow
        replace hret : RetOk (fr.at (fr.pc + 1) :: rest) _ := fun _ => hret
        exact .inl ⟨_, h.enter (top := regs .x2) (agree_set' hag .x1 _ (by rw [h.tpc])) (by simp) hfn
          (by simp only [pc_setPC]; rw [h.tpc, hbase]) hret hbelow,
          hL.next ((hstep _).2 (by simp [Isa.stepI, callee_direct hglt]))⟩
      · exact (back_abort hL hstep).elim
    · rw [ite_eq_right h1] at hstep
      exact (back_abort hL hstep).elim

theorem back_jalr (hok : ProgOk fs) (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩)
    (h : At fs exit fr rest regs m t f k) {rd rs : Reg} {off : BitVec 12}
    (hfetch : t.code t.pc = some (.JALR rd rs off))
    (hstep : StepIs fs fr rest regs m f (liftJalr fs (f.base + BitVec.ofNat 64 (4 * k)) rd rs off)) :
    ∀ t', stepSp1 t = some t' → Next fs exit Q t' := by
  intro t' ht'
  rw [stepSp1_ctl hfetch rfl (by simp) (by simp)] at ht'
  cases ht'
  have hag := h.sim.agree
  have htgt := jalrTgt_eval hag rs off
  unfold liftJalr at hstep
  by_cases h0 : rd = .x0
  · subst h0
    rw [ite_eq_left rfl] at hstep
    have hag' : Agree (ofParts regs m) (execInstrBr t (.JALR .x0 rs off)) := hag.trans (agree_setPC t _)
    split at hstep
    · next hr =>
      obtain ⟨rfl, rfl⟩ := hr
      by_cases hra : regs .x1 = fr.ret ∧ regs .x2 = fr.top
      · have hs1 := hL.next ((hstep (.ok (⟨rest, regs, m⟩, []))).2 (by simp [Isa.stepI, hra]))
        have h1 : t.getReg .x1 = fr.ret := by
          rw [← hag.regs .x1, getReg_ofParts]; exact hra.1
        have hpc : (execInstrBr t (.JALR .x0 .x1 0)).pc = fr.ret &&& ~~~1#64 := by
          simp only [execInstrBr, pc_setPC, h1, signExtend12]
          rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 from rfl,
            show fr.ret + (0 : Word) = fr.ret from by simp]
        have hchain := h.sim.chain.2.2
        cases rest with
        | nil => exact .inr ⟨_, rfl, hag', by rw [hpc, show fr.ret = exit from hchain],
            hs1.acc (Or.inl rfl)⟩
        | cons fr' rest' =>
          exact .inl ⟨_, ⟨hag', h.code' (by simp [execInstrBr]),
            by rw [hpc, h.sim.chain.2.1 (by simp)]; exact hchain, by simp⟩, hs1⟩
      · exact (hL.not_wrong ((hstep _).2 (by simp [Isa.stepI, hra]))).elim
    · by_cases hsp : regs .x2 = fr.top
      · cases hc : rvIsa.callee (liftProg fs) regs (.indirect (jalrTgt rs off) (List.range fs.length)) with
        | none => exact (hL.not_wrong ((hstep _).2 (by simp only [Isa.stepI, hsp, hc]; simp))).elim
        | some g =>
          obtain ⟨fn, hfn, hbase⟩ := callee_indirect hc
          exact .inl ⟨_, h.enter (top := fr.top) hag' (by simp [execInstrBr]) hfn
            (by simp only [execInstrBr, pc_setPC]; rw [hbase, htgt]) h.sim.chain.2.1 h.sim.chain.2.2,
            hL.next ((hstep _).2 (by simp only [Isa.stepI, hsp, hc]; simp))⟩
      · exact (hL.not_wrong ((hstep _).2 (by simp [Isa.stepI, hsp]))).elim
  · rw [ite_eq_right h0] at hstep
    by_cases h1 : rd = .x1
    · subst h1
      rw [ite_eq_left rfl] at hstep
      cases hc : rvIsa.callee (liftProg fs) regs (.indirect (jalrTgt rs off) (List.range fs.length)) with
      | none => exact (hL.not_wrong ((hstep _).2 (by simp only [Isa.stepI, hc]))).elim
      | some g =>
        obtain ⟨fn, hfn, hbase⟩ := callee_indirect hc
        have hret := h.ret_aligned hok
        have hbelow := h.below
        rw [h.tpc] at hret hbelow
        replace hret : RetOk (fr.at (fr.pc + 1) :: rest) _ := fun _ => hret
        exact .inl ⟨_, h.enter (top := regs .x2) (agree_set' hag .x1 _ (by rw [h.tpc])) (by simp) hfn
          (by simp only [pc_setPC]; rw [hbase, htgt]) hret hbelow,
          hL.next ((hstep _).2 (by simp only [Isa.stepI, hc]))⟩
    · rw [ite_eq_right h1] at hstep
      exact (back_abort hL hstep).elim

theorem stepSp1_ecall {t : MachineState} (hf : t.code t.pc = some .ECALL) : stepSp1 t = sp1Ecall t := by
  unfold stepSp1; rw [hf]

theorem back_ecall (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩) (h : At fs exit fr rest regs m t f k)
    (hfetch : t.code t.pc = some .ECALL) (hstep : StepIs fs fr rest regs m f .Lext) :
    ∀ t', stepSp1 t = some t' → Next fs exit Q t' := by
  intro t' ht'
  have hst := ht'
  rw [stepSp1_ecall hfetch] at ht'
  exact .inl ⟨_, h.next (agree_ofParts_regsOf t') (code_stepSp1 hst) (pc_sp1Ecall hfetch ht'),
    hL.next ((hstep _).2 ⟨rfl, t, h.sim.agree, hfetch, by simp [ht']⟩)⟩

theorem accept_ecall (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩) (h : At fs exit fr rest regs m t f k)
    (hbody : (bodyOf fs f)[fr.pc]? = some .Lext) (ha : Accepted t) : Q ⟨fr :: rest, regs, m⟩ := by
  have hag := h.sim.agree
  refine hL.acc (Or.inr ⟨MachineChecked.Lprog.SafeN.fetch_eq (getElem?_liftProg h.hf) hbody, ?_, ?_⟩)
  · rw [hag.regs]; exact ha.2.1
  · rw [hag.regs]; exact ha.2.2

/-- **One instruction**: a machine step from the instruction the innermost activation is at
    is matched at Lprog, and a machine stuck accepting there is an accepting Lprog state. -/
theorem back_instr (hok : ProgOk fs) (hL : AllSafe fs Q ⟨fr :: rest, regs, m⟩)
    (h : At fs exit fr rest regs m t f k) :
    (∀ t', stepSp1 t = some t' → Next fs exit Q t') ∧ (Accepted t → Q ⟨fr :: rest, regs, m⟩) := by
  have hfetch := h.fetch
  have hstep : StepIs fs fr rest regs m f
      (liftI fs f.prog.length k (f.base + BitVec.ofNat 64 (4 * k)) (f.prog[k]'h.hk)) := h.step_iff
  have hbody := h.body.2
  generalize f.prog[k]'h.hk = i at hfetch hstep hbody
  by_cases hop : opnOk i = true
  · simp only [liftI, hop, ite_true] at hstep
    refine ⟨back_opn hL h hfetch hop hstep, fun ha => ?_⟩
    exact absurd (Option.some.inj (hfetch.symm.trans ha.1)) (not_ecall_of_opnOk hop)
  · simp only [liftI, hop, Bool.false_eq_true, ite_false] at hstep hbody
    refine ⟨?_, fun ha => ?_⟩
    · cases i
      case AUIPC rd imm => exact back_auipc hL h hfetch hstep
      case BEQ a b off =>
        exact back_branch hL h hfetch rfl (by simp) (by simp) (c := t.getReg a == t.getReg b)
          (by simp [cmpEval]) (by simp [execInstrBr]) hstep
      case BNE a b off =>
        exact back_branch hL h hfetch rfl (by simp) (by simp) (c := t.getReg a != t.getReg b)
          (by simp [cmpEval]) (by simp [execInstrBr]) hstep
      case BLT a b off =>
        exact back_branch hL h hfetch rfl (by simp) (by simp) (c := BitVec.slt (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) hstep
      case BGE a b off =>
        exact back_branch hL h hfetch rfl (by simp) (by simp) (c := !BitVec.slt (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) hstep
      case BLTU a b off =>
        exact back_branch hL h hfetch rfl (by simp) (by simp) (c := BitVec.ult (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) hstep
      case BGEU a b off =>
        exact back_branch hL h hfetch rfl (by simp) (by simp) (c := !BitVec.ult (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) hstep
      case JAL rd off => exact back_jal hok hL h hfetch hstep
      case JALR rd rs off => exact back_jalr hok hL h hfetch hstep
      case ECALL => exact back_ecall hL h hfetch hstep
      all_goals first
        | exact absurd rfl hop
        | exact (back_abort hL hstep).elim
    · obtain rfl : i = .ECALL := Option.some.inj (hfetch.symm.trans ha.1)
      exact accept_ecall hL h hbody ha

/-- **One machine step, matched at Lprog**: from a label, the label step and then the
    instruction. -/
theorem back_step (hok : ProgOk fs) {s : State rvIsa} (hs : Sim fs exit s t) (hL : AllSafe fs Q s) :
    (∀ t', stepSp1 t = some t' → Next fs exit Q t') ∧ (Accepted t → ∃ s', s'.stack ≠ [] ∧ Q s') := by
  obtain ⟨stack, regs, m⟩ := s
  obtain ⟨hag, hcode, hchain, hne⟩ := hs
  cases stack with
  | nil => exact absurd rfl hne
  | cons fr rest =>
    obtain ⟨⟨f, hf, hle, htpc⟩, hfr, hrest⟩ := hchain
    obtain ⟨k, hk | hk⟩ : ∃ k, fr.pc = 2 * k ∨ fr.pc = 2 * k + 1 := ⟨fr.pc / 2, by omega⟩
    · by_cases hkl : k < f.prog.length
      · have hst : rvIsa.step (liftProg fs) sp1Ctx ⟨fr :: rest, regs, m⟩
            (.ok (⟨fr.at (fr.pc + 1) :: rest, regs, m⟩, [])) := by
          rw [MachineChecked.Lprog.SafeN.step_eq (getElem?_liftProg hf) (by rw [hk]; exact body_even fs f hkl)]
          rfl
        have hAt : At fs exit (fr.at (fr.pc + 1)) rest regs m t f k :=
          ⟨⟨hag, hcode, ⟨⟨f, hf, by simp; omega, by rw [htpc, hk]; simp; congr 2; omega⟩, hfr, hrest⟩,
            by simp⟩, hf, hkl, by simp [hk], by rw [htpc, hk]; congr 2; omega⟩
        obtain ⟨h1, h2⟩ := back_instr hok (hL.next hst) hAt
        exact ⟨h1, fun ha => ⟨_, by simp, h2 ha⟩⟩
      · exfalso
        refine hL.not_wrong ?_
        simp only [Isa.step, getElem?_liftProg hf]
        rw [show (liftFn fs f).body = bodyOf fs f from rfl, body_end fs f (by omega)]
        trivial
    · exact back_instr hok hL ⟨⟨hag, hcode, ⟨⟨f, hf, hle, htpc⟩, hfr, hrest⟩, hne⟩, hf, by omega, hk,
        by rw [htpc, hk]; congr 2; omega⟩ |>.imp id fun h2 ha => ⟨_, by simp, h2 ha⟩

end Back

/-! ## The transfer theorem -/

/-- **The transfer theorem.** A simulated state safe at Lprog at every budget, with `Q` giving
    `P` at an accepting state and the machine's continuation at a return to `exit`, makes the
    machine state safe. -/
theorem transfer {fs : List Fn} (hok : ProgOk fs) {G : MachineState → Prop} {N : Nat} {P : Prop}
    {exit : Word} {Q : State rvIsa → Prop} (hacc : ∀ s', s'.stack ≠ [] → Q s' → P)
    (hret : ∀ s' t', s'.stack = [] → Agree (ofParts s'.regs s'.m) t' → t'.pc = exit &&& ~~~1#64 →
      Q s' → SafeN G N P t') :
    ∀ n, n ≤ N → ∀ s t, Sim fs exit s t → AllSafe fs Q s → SafeN G n P t := by
  intro n
  induction n with
  | zero => intros; exact SafeN.zero
  | succ n ih =>
    intro hn s t hs hL
    obtain ⟨hnext, hacc'⟩ := back_step hok hs hL
    cases hst : stepSp1 t with
    | none =>
      exact SafeN.stuck hst fun ha => let ⟨s', hne, hq⟩ := hacc' ha; hacc s' hne hq
    | some t' =>
      refine SafeN.step (not_accepted_of_step hst) hst ?_
      rcases hnext t' hst with ⟨s', hs', hL'⟩ | ⟨s', hnil, hag, hpc, hq⟩
      · exact ih (by omega) s' t' hs' hL'
      · exact SafeN.mono (by omega) (hret s' t' hnil hag hpc hq)

/-- **The transfer theorem, from a function's entry.** A machine at the entry of function `g`
    of a lifted program it holds is safe if the call `⟨g, 0, ra, sp⟩` is safe at Lprog at every
    budget, where `Q` gives `P` at an accepting state and, once the function has returned, the
    machine's continuation where `jalr` lands, at `ra &&& ~~~1`. -/
theorem SafeN.of_lift {fs : List Fn} (hok : ProgOk fs) {g : Nat} {fn : Fn} (hg : fs[g]? = some fn)
    {t : MachineState} (hpc : t.pc = fn.base) (hcode : ∀ f ∈ fs, CodeAt f.base (f.prog.map some) t)
    {Q : State rvIsa → Prop}
    (hL : AllSafe fs Q ⟨[⟨g, 0, t.getReg .x1, t.getReg .x2⟩], regsOf t, t⟩)
    {G : MachineState → Prop} {N : Nat} {P : Prop} (hacc : ∀ s', s'.stack ≠ [] → Q s' → P)
    (hret : ∀ s' t', s'.stack = [] → Agree (ofParts s'.regs s'.m) t' →
      t'.pc = t.getReg .x1 &&& ~~~1#64 → Q s' → SafeN G N P t') :
    SafeN G N P t :=
  transfer hok hacc hret N (Nat.le_refl N) ⟨[⟨g, 0, t.getReg .x1, t.getReg .x2⟩], regsOf t, t⟩ t
    ⟨agree_ofParts_regsOf t, hcode, ⟨⟨fn, hg, Nat.zero_le _, by simp [hpc]⟩, nofun, rfl⟩, by simp⟩ hL


/-- **A function's contract at Lprog, over the machine.** If the call of function `g` is safe at
    Lprog whenever every return in a state satisfying `Post` is, then a machine at its entry is
    safe whenever every state it may return in, at `ra &&& ~~~1`, that agrees with one satisfying
    `Post` is. -/
theorem SafeN.of_contract {fs : List Fn} (hok : ProgOk fs) {g : Nat} {fn : Fn} (hg : fs[g]? = some fn)
    {t : MachineState} (hpc : t.pc = fn.base) (hcode : ∀ f ∈ fs, CodeAt f.base (f.prog.map some) t)
    {Post : MachineState → Prop}
    (hspec : ∀ (Q : State rvIsa → Prop) k,
      (∀ r' m', Post (ofParts r' m') → LSafeN fs (fun _ => True) k Q ⟨[], r', m'⟩) →
      LSafeN fs (fun _ => True) k Q ⟨[⟨g, 0, t.getReg .x1, t.getReg .x2⟩], regsOf t, t⟩)
    {G : MachineState → Prop} {N : Nat} {P : Prop}
    (hk : ∀ t' r' m', Agree (ofParts r' m') t' → t'.pc = t.getReg .x1 &&& ~~~1#64 →
      Post (ofParts r' m') → SafeN G N P t') :
    SafeN G N P t :=
  SafeN.of_lift (Q := fun s' => s'.stack = [] ∧ Post (ofParts s'.regs s'.m)) hok hg hpc hcode
    (fun k => hspec _ k fun _ _ hp => MachineChecked.Lprog.SafeN.returned ⟨rfl, hp⟩)
    (fun _ hne hq => absurd hq.1 hne) (fun s' t' _ hag hpc' hq => hk t' s'.regs s'.m hag hpc' hq.2)

end MachineChecked.RiscV.Lprog
