/-
  MachineChecked.ARM.Lift.Transfer

  **The lift of AArch64 is correct**: `SafeN` proved at Lprog for a lifted program gives
  `SafeN` over arm64-semantics' `Step`.

  `Sim prog fns exit s t` relates a state of the lifted program to a machine state: the
  registers and the memory stand for it (`Agree`), it is running, its stack pointer is
  aligned, it holds the program (it fetches each instruction from memory, `Loaded`), and the
  activations correspond to its control state: the innermost one is at the label of the
  instruction the counter is on, each other one resumes where the one above it returns, and
  the outermost returns to `exit`.

  One machine step from a simulated state is matched at Lprog (`back`) by the label and the
  commands of the instruction, ending in a simulated state, or in a returned program with
  the machine at `exit`; a machine that faults is matched by a program that traps. A program
  that goes `wrong` on the way matches nothing, and the Lprog judgement rules it out: an
  instruction the lift does not take, a stack pointer written to a value that is not a
  multiple of 16, a return that is not to the caller, a call out of the program, `svc`. So,
  by the transfer theorem of any two systems (`Lprog.Ascent.transfer`), `SafeN` at Lprog at
  every budget gives `SafeN` over the machine (`transfer`), and from a function's entry
  (`SafeN.of_lift`).

  What is assumed of the program: its instructions are four bytes each, one after another
  (`ProgOk`), and of kinds that are proved (`Proved`: all the lift takes but `clz`, `cls`,
  addition with carry and signed division). What is assumed of the machine state: it is
  running, its stack pointer is aligned, and it holds the program. Nothing is assumed of
  `Arm64.decode`: the lift refuses what the proof does not cover (`okI`).

  The context is `armCtx`, where an external call goes `wrong`: a program proved safe under
  it makes none.

  ## Main definitions

  * `armCtx`, `lsys`, `mstep`, `MSafeN`: the lifted program and the machine, as systems
  * `ProgOk`, `Proved`, `Loaded`, `Chain`, `Sim`, `Ret`: the simulation
  * `Here`, `Out`: at an instruction, and what the program does for the machine's step

  ## Main results

  * `step_of_fetch`: the machine's step at a fetched instruction
  * `steps_ops`: the operations of an instruction, as steps of the program
  * `noLab_liftI`: no command of an instruction is a label
  * `Here.out`: one instruction, matched, whichever it is
  * `back`: one machine step, matched at Lprog
  * `transfer`, `SafeN.of_lift`: the transfer theorem
-/

import MachineChecked.ARM.Lift.Sound
import Lprog.LinkedSpec
import Lprog.Ascent.Transfer

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build Lprog.Linked
open Lprog.Ascent (Outcome Steps GoesWrong System)
open Arm64 (Instr RegWidth MemWidth AddrMode)

/-! ## The two systems -/

/-- **The context of a lifted AArch64 program**: an external call is not lifted, and goes
    `wrong`. -/
def armCtx : Context armIsa Unit := ⟨fun _ _ _ o => o = .wrong, fun _ _ _ => False⟩

/-- The lifted program, as a system. -/
abbrev lsys (fns : List Fun) : System (State armIsa) Unit := armIsa.system (liftArm fns) armCtx

/-- **AArch64 as arm64-semantics steps it**: a step to a running state. A step to a state
    that is not running (a fault, a halt, an exit) is a trap; nothing is `wrong`. -/
def mstep (prog : Arm64.Program) (t : Arm64.State) : Outcome Arm64.State → Prop
  | .ok t' => Arm64.Step prog t t' ∧ t'.status = .Running
  | .trap => ∃ t', Arm64.Step prog t t' ∧ t'.status ≠ .Running
  | .wrong => False

/-- **The machine's step at an instruction it fetches** is the execution of that
    instruction. -/
theorem step_of_fetch {prog : Arm64.Program} {t t' : Arm64.State} {i : Instr}
    (hrun : t.status = .Running) (hf : prog.fetchMem t.mem t.pc = some i) :
    Arm64.Step prog t t' ↔ t' = prog.evalInst i t := by
  constructor
  · intro h
    cases h with
    | exec _ h_fetch => rw [hf] at h_fetch; cases h_fetch; rfl
    | halt_unmapped _ h_fetch => rw [hf] at h_fetch; cases h_fetch
    | extern _ h_ext => simp [Arm64.Program.fetchMem, h_ext] at hf
    | extern_fault _ h_ext => simp [Arm64.Program.fetchMem, h_ext] at hf
  · rintro rfl
    exact .exec hrun hf

/-! ## Operations as steps -/

section steps

variable {p : Lprog O Reg} {fd : Lfundef O Reg} {fn : Nat}

/-- **The operations of an instruction, as steps of the program**: where they run, the
    program steps past them; where they fault, it steps to a trap. -/
theorem steps_ops (hf : p[fn]? = some fd) {os : List O} {P : Nat}
    (hb : ∀ j (hj : j < os.length), fd.body[P + j]? = some (.Lopn os[j]))
    (rv top : BitVec 64) (rest : List Frame) (regs : Reg → BitVec 64) (m : Arm64.Memory) :
    match run os regs m with
    | some (r', m') => Steps (armIsa.system p armCtx) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ []
        ⟨⟨fn, P + os.length, rv, top⟩ :: rest, r', m'⟩
    | none => ∃ s', Steps (armIsa.system p armCtx) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ [] s' ∧
        ¬ armIsa.accept p armCtx s' ∧ armIsa.step p armCtx s' .trap := by
  induction os generalizing P regs m with
  | nil => exact .refl _
  | cons o os ih =>
    have h0 : fd.body[P]? = some (.Lopn o) := hb 0 (by simp)
    have hb' : ∀ j (hj : j < os.length), fd.body[P + 1 + j]? = some (.Lopn os[j]) := by
      intro j hj
      have := hb (j + 1) (by simpa using hj)
      rw [show P + (j + 1) = P + 1 + j by omega] at this
      exact this
    rw [run_cons]
    cases he : o.eval armMem regs m with
    | none =>
      refine ⟨_, .refl _, Lprog.SafeN.not_accept hf h0 (by simp), ?_⟩
      exact (Lprog.SafeN.step_eq (fr := ⟨fn, P, rv, top⟩) hf h0 _).2 (by simp [Isa.stepI, he])
    | some rm =>
      obtain ⟨r1, m1⟩ := rm
      have hs : (armIsa.system p armCtx).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩
          (.ok (⟨⟨fn, P + 1, rv, top⟩ :: rest, r1, m1⟩, [])) :=
        (Lprog.SafeN.step_eq (fr := ⟨fn, P, rv, top⟩) hf h0 _).2 (by simp [Isa.stepI, he, Frame.at])
      have := ih hb' r1 m1
      simp only [Option.bind_some]
      cases hr : run os r1 m1 with
      | none =>
        rw [hr] at this
        obtain ⟨s', hs', h1, h2⟩ := this
        exact ⟨s', by simpa using Steps.step hs hs', h1, h2⟩
      | some rm' =>
        obtain ⟨r', m'⟩ := rm'
        rw [hr] at this
        have h2 := Steps.step hs this
        rw [show P + 1 + os.length = P + (o :: os).length by simp; omega] at h2
        simpa using h2

end steps

/-! ## No command of an instruction is a label -/

/-- No command is a label. -/
def NoLab (cs : Lcmd O Reg) : Prop := ∀ c ∈ cs, ∀ l, isLabel l c = false

theorem NoLab.nil : NoLab [] := fun _ h => by cases h

theorem NoLab.append {a b : Lcmd O Reg} (ha : NoLab a) (hb : NoLab b) : NoLab (a ++ b) :=
  fun c hc l => (List.mem_append.1 hc).elim (ha c · l) (hb c · l)

theorem NoLab.cons {c : LinstrR O Reg} {cs : Lcmd O Reg} (hc : ∀ l, isLabel l c = false)
    (hcs : NoLab cs) : NoLab (c :: cs) := fun d hd l => by
  rcases List.mem_cons.1 hd with rfl | hd
  · exact hc l
  · exact hcs d hd l

theorem NoLab.opns (os : List O) : NoLab (os.map .Lopn) := fun c hc l => by
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 hc; rfl

theorem noLab_spCheck (ab : LLabel) (os : List O) : NoLab (spCheck ab os) := by
  unfold spCheck
  split
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)
  · exact .nil

theorem noLab_toLabel (cx : Cx) (a : BitVec 64) {k : LLabel → Lcmd O Reg} (hk : ∀ l, NoLab (k l)) :
    NoLab (toLabel cx a k) := by
  unfold toLabel
  split
  · exact hk _
  · exact .cons (fun _ => rfl) .nil

theorem noLab_branch (c : Arm64.CondCode) (l : LLabel) : NoLab (branch c l) := by
  cases c <;> simp [branch, NoLab, isLabel]

theorem noLab_jump (e : E) (locals : List (BitVec 64 × LLabel)) (fns : List Nat) :
    NoLab (Linked.jump .t2 e [] locals fns) := by
  unfold Linked.jump
  split
  · split <;> exact .cons (fun _ => rfl) .nil
  · refine .append (.append (.append (.cons (fun _ => rfl) .nil) .nil) ?_) ?_
    · intro c hc l
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc; rfl
    · split <;> exact .cons (fun _ => rfl) .nil

/-- **No command the lift writes for an instruction is a label**, so a label is found at the
    instruction it names. -/
theorem noLab_liftI (cx : Cx) (prev : Option (At (Option Instr))) (i : At (Option Instr)) :
    NoLab (liftI cx prev i) := by
  unfold liftI
  split
  · exact .cons (fun _ => rfl) .nil
  · unfold liftB; split <;> exact .cons (fun _ => rfl) .nil
  · unfold liftBl; split <;> exact .cons (fun _ => rfl) .nil
  · exact noLab_toLabel _ _ fun l => noLab_branch _ l
  · refine noLab_toLabel _ _ fun l => ?_
    unfold liftCbz
    repeat' split
    all_goals first
      | exact .nil
      | exact .cons (fun _ => rfl) .nil
      | exact .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)
  · refine noLab_toLabel _ _ fun l => ?_
    unfold liftTbz
    split
    · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)
    · exact .cons (fun _ => rfl) .nil
  · split
    · exact noLab_jump _ _ _
    · exact .cons (fun _ => rfl) .nil
  · split <;> exact .cons (fun _ => rfl) .nil
  · split <;> exact .cons (fun _ => rfl) .nil
  · exact .cons (fun l => by split <;> rfl) .nil
  · unfold liftOps
    repeat' split
    all_goals first
      | exact .append (.opns _) (noLab_spCheck _ _)
      | exact .cons (fun _ => rfl) .nil

/-! ## The simulation -/

/-- **A program the lift is proved for**: in each function, instructions of four bytes one
    after another from its address. -/
def ProgOk (fns : List Fun) : Prop :=
  ∀ f ∈ fns, ∀ k (hk : k < f.code.length),
    f.code[k].addr = f.addr + BitVec.ofNat 64 (4 * k) ∧ f.code[k].size = 4

/-- **The machine holds the program**: it fetches each of its instructions from memory. -/
def Loaded (prog : Arm64.Program) (fns : List Fun) (mem : Arm64.Memory) : Prop :=
  ∀ f ∈ fns, ∀ k (hk : k < f.code.length) (i : Instr), f.code[k].instr = some i →
    prog.fetchMem mem f.code[k].addr = some i

theorem Loaded.keeps {prog : Arm64.Program} {fns : List Fun} {m m' : Arm64.Memory}
    (h : Loaded prog fns m) (hk : Keeps m m') : Loaded prog fns m' :=
  fun f hf k hk' i hi => fetchMem_keeps hk (h f hf k hk' i hi)

/-- Activation `fr` stands for the machine at address `a`: at the label of an instruction of
    its function, or after the last one. -/
def FrameAt (fns : List Fun) (fr : Frame) (a : BitVec 64) : Prop :=
  ∃ f, fns[fr.fn]? = some f ∧ ∃ k, k ≤ f.code.length ∧ fr.pc = pos liftI fns f k ∧
    a = f.addr + BitVec.ofNat 64 (4 * k)

/-- The activations stand for the machine at `a`, each returning where the next one resumes,
    and the outermost to `exit`. -/
def Chain (fns : List Fun) (exit : BitVec 64) : List Frame → BitVec 64 → Prop
  | [], a => a = exit
  | fr :: rest, a => FrameAt fns fr a ∧ Chain fns exit rest fr.ret

/-- **The simulation**: a state of the lifted program that has not returned stands for a
    machine state that is running, with its stack pointer aligned, holding the program. -/
structure Sim (prog : Arm64.Program) (fns : List Fun) (exit : BitVec 64) (s : State armIsa)
    (t : Arm64.State) : Prop where
  agree : Agree s.regs s.m t
  running : t.status = .Running
  aligned : t.spAligned = true
  loaded : Loaded prog fns t.mem
  chain : Chain fns exit s.stack t.pc
  ne : s.stack ≠ []

/-- A returned program stands for the machine at `exit`. -/
def Ret (prog : Arm64.Program) (fns : List Fun) (exit : BitVec 64) (s : State armIsa)
    (t : Arm64.State) : Prop :=
  s.stack = [] ∧ Agree s.regs s.m t ∧ t.status = .Running ∧ t.spAligned = true ∧
    Loaded prog fns t.mem ∧ t.pc = exit

/-- The commands `cs` are in the body of `fd` from position `P`. -/
def Cmds (fd : Lfundef O Reg) (P : Nat) (cs : Lcmd O Reg) : Prop :=
  ∀ j (hj : j < cs.length), fd.body[P + j]? = some cs[j]

theorem Cmds.head {fd : Lfundef O Reg} {P : Nat} {c : LinstrR O Reg} {cs : Lcmd O Reg}
    (h : Cmds fd P (c :: cs)) : fd.body[P]? = some c := h 0 (by simp)

theorem Cmds.tail {fd : Lfundef O Reg} {P : Nat} {c : LinstrR O Reg} {cs : Lcmd O Reg}
    (h : Cmds fd P (c :: cs)) : Cmds fd (P + 1) cs := fun j hj => by
  have := h (j + 1) (by simpa using hj)
  rw [show P + (j + 1) = P + 1 + j by omega] at this
  exact this

theorem Cmds.left {fd : Lfundef O Reg} {P : Nat} {cs ds : Lcmd O Reg} (h : Cmds fd P (cs ++ ds)) :
    Cmds fd P cs := fun j hj => by
  have := h j (by simp; omega)
  rwa [List.getElem_append_left hj] at this

theorem Cmds.right {fd : Lfundef O Reg} {P : Nat} {cs ds : Lcmd O Reg}
    (h : Cmds fd P (cs ++ ds)) : Cmds fd (P + cs.length) ds := fun j hj => by
  have := h (cs.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

theorem Cmds.opns {fd : Lfundef O Reg} {P : Nat} {os : List O} (h : Cmds fd P (os.map .Lopn)) :
    ∀ j (hj : j < os.length), fd.body[P + j]? = some (.Lopn os[j]) := fun j hj => by
  have := h j (by simpa using hj)
  rwa [List.getElem_map] at this

/-! ## Single steps of the lifted program -/

section single

variable {fns : List Fun} {fd : Lfundef O Reg} {fn P : Nat} {rv top : BitVec 64}
  {rest : List Frame} {regs : Reg → BitVec 64} {m : Arm64.Memory}

theorem step_iff (hfd : (liftArm fns)[fn]? = some fd) {c : LinstrR O Reg}
    (hi : fd.body[P]? = some c) (o : Outcome (State armIsa × List Unit)) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ o ↔
      armIsa.stepI (liftArm fns) armCtx fd.body ⟨fn, P, rv, top⟩ rest regs m c o :=
  Lprog.SafeN.step_eq (fr := ⟨fn, P, rv, top⟩) hfd hi o

theorem step_label (hfd : (liftArm fns)[fn]? = some fd) {kd : LabelKind} {l : LLabel}
    (hi : fd.body[P]? = some (.Llabel kd l)) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩
      (.ok (⟨⟨fn, P + 1, rv, top⟩ :: rest, regs, m⟩, [])) :=
  (step_iff hfd hi _).2 rfl

theorem step_opn (hfd : (liftArm fns)[fn]? = some fd) {o : O} (hi : fd.body[P]? = some (.Lopn o))
    {r' : Reg → BitVec 64} {m' : Arm64.Memory} (he : o.eval armMem regs m = some (r', m')) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩
      (.ok (⟨⟨fn, P + 1, rv, top⟩ :: rest, r', m'⟩, [])) :=
  (step_iff hfd hi _).2 (by simp [Isa.stepI, he, Frame.at])

theorem step_abort (hfd : (liftArm fns)[fn]? = some fd) (hi : fd.body[P]? = some .Labort) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ .wrong :=
  (step_iff hfd hi _).2 rfl

theorem step_goto (hfd : (liftArm fns)[fn]? = some fd) {l : LLabel} {j : Nat}
    (hi : fd.body[P]? = some (.Lgoto l)) (hl : labelIdx fd.body l = some j) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩
      (.ok (⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩, [])) :=
  (step_iff hfd hi _).2 (by simp [Isa.stepI, hl, Frame.at])

theorem step_cond_false (hfd : (liftArm fns)[fn]? = some fd) {c : LOperand Reg} {l : LLabel}
    (hi : fd.body[P]? = some (.Lcond c l)) (hc : condEval c regs = some false) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩
      (.ok (⟨⟨fn, P + 1, rv, top⟩ :: rest, regs, m⟩, [])) :=
  (step_iff hfd hi _).2 (by simp [Isa.stepI, hc, Frame.at])

theorem step_cond_true (hfd : (liftArm fns)[fn]? = some fd) {c : LOperand Reg} {l : LLabel}
    {j : Nat} (hi : fd.body[P]? = some (.Lcond c l)) (hc : condEval c regs = some true)
    (hl : labelIdx fd.body l = some j) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩
      (.ok (⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩, [])) :=
  (step_iff hfd hi _).2 (by simp [Isa.stepI, hc, hl, Frame.at])

theorem step_cond_wrong (hfd : (liftArm fns)[fn]? = some fd) {c : LOperand Reg} {l : LLabel}
    (hi : fd.body[P]? = some (.Lcond c l)) (hc : condEval c regs = some true)
    (hl : labelIdx fd.body l = none) :
    (lsys fns).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ .wrong :=
  (step_iff hfd hi _).2 (by simp [Isa.stepI, hc, hl])

/-- A comparison of a register with zero. -/
theorem cond_reg_zero (r : Reg) (ne : Bool) :
    condEval (.cmp (if ne then "ne" else "eq") (.reg r) (.imm 0)) regs =
      some (if ne then regs r != 0#64 else regs r == 0#64) := by
  cases ne <;> simp [condEval, operandVal, cmpEval] <;> rfl

end single

/-! ## Tests and branches -/

section tests

variable {fns : List Fun} {fd : Lfundef O Reg} {fn P : Nat} {rv top : BitVec 64}
  {rest : List Frame} {regs : Reg → BitVec 64} {m : Arm64.Memory}

theorem flag_ne_zero (b : Bool) : (flag b != 0#64) = b := by cases b <;> decide

theorem flag_eq_zero (b : Bool) : (flag b == 0#64) = !b := by cases b <;> decide

/-- A bit of a value, tested. -/
theorem bit_ne_zero (v : BitVec 64) (b : Nat) :
    ((v >>> b) &&& 1#64 != 0#64) = v.getLsbD b := by
  have e : v.getLsbD b = (v >>> b).getLsbD 0 := by simp
  rw [e]
  generalize v >>> b = u
  have : (u &&& 1#64 != 0#64) = u.getLsbD 0 := by bv_decide
  exact this

theorem bit_eq_zero (v : BitVec 64) (b : Nat) :
    ((v >>> b) &&& 1#64 == 0#64) = !v.getLsbD b := by
  rw [← bit_ne_zero]; simp [bne]

/-- **A test of a register against zero**: a jump to the label, or on to the next command. -/
theorem test_steps (hfd : (liftArm fns)[fn]? = some fd) {ne : Bool} {r : Reg} {l : LLabel}
    {j : Nat}
    (hi : fd.body[P]? = some (.Lcond (.cmp (if ne then "ne" else "eq") (.reg r) (.imm 0)) l))
    (hj : labelIdx fd.body l = some j) :
    Steps (lsys fns) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ []
      ⟨⟨fn, if (if ne then regs r != 0#64 else regs r == 0#64) then j else P + 1, rv, top⟩ ::
        rest, regs, m⟩ := by
  have hc := cond_reg_zero (regs := regs) r ne
  cases hb : (if ne then regs r != 0#64 else regs r == 0#64) with
  | false =>
    rw [hb] at hc
    exact Steps.one (step_cond_false hfd hi hc)
  | true =>
    rw [hb] at hc
    exact Steps.one (step_cond_true hfd hi hc hj)

/-- **A value computed into `t0` and tested against zero.** -/
theorem set_test_steps (hfd : (liftArm fns)[fn]? = some fd) {ne : Bool} {e : E} {l : LLabel}
    {j : Nat}
    (hc : Cmds fd P [.Lopn (.set .t0 e),
      .Lcond (.cmp (if ne then "ne" else "eq") (.reg .t0) (.imm 0)) l])
    (hj : labelIdx fd.body l = some j) :
    Steps (lsys fns) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ []
      ⟨⟨fn, if (if ne then e.eval regs != 0#64 else e.eval regs == 0#64) then j else P + 2,
        rv, top⟩ :: rest, updReg regs .t0 (e.eval regs), m⟩ := by
  have s1 := step_opn (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m) hfd hc.head
    (r' := updReg regs .t0 (e.eval regs)) (m' := m) rfl
  have s2 := test_steps (rv := rv) (top := top) (rest := rest)
    (regs := updReg regs .t0 (e.eval regs)) (m := m) hfd hc.tail.head hj
  simpa [updReg] using (Steps.one s1).trans s2

/-- **A conditional branch**: a jump to the label where the machine's condition holds. -/
theorem branch_steps {t : Arm64.State} (hfd : (liftArm fns)[fn]? = some fd) (c : Arm64.CondCode)
    {l : LLabel} {j : Nat} (hc : Cmds fd P (branch c l)) (hag : Agree regs m t)
    (hj : labelIdx fd.body l = some j) :
    ∃ r', Agree r' m t ∧ Steps (lsys fns) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ []
      ⟨⟨fn, if Arm64.ConditionHolds c t.pstate then j else P + (branch c l).length, rv, top⟩ ::
        rest, r', m⟩ := by
  have hce := cond_eval hag c
  cases c
  case AL | NV =>
    exact ⟨regs, hag, Steps.one (step_goto hfd hc.head hj)⟩
  case EQ =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.zf, flag_ne_zero, Arm64.ConditionHolds, branch] using this
  case NE =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := false) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.zf, flag_eq_zero, Arm64.ConditionHolds, branch] using this
  case CS =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.cf, flag_ne_zero, Arm64.ConditionHolds, branch] using this
  case CC =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := false) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.cf, flag_eq_zero, Arm64.ConditionHolds, branch] using this
  case MI =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.nf, flag_ne_zero, Arm64.ConditionHolds, branch] using this
  case PL =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := false) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.nf, flag_eq_zero, Arm64.ConditionHolds, branch] using this
  case VS =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.vf, flag_ne_zero, Arm64.ConditionHolds, branch] using this
  case VC =>
    have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := false) hfd hc.head hj
    refine ⟨regs, hag, ?_⟩
    simpa [hag.vf, flag_eq_zero, Arm64.ConditionHolds, branch] using this
  case HI =>
    have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc hj
    refine ⟨updReg regs .t0 ((cond .HI).eval regs), hag.scratch (.inl rfl) _, ?_⟩
    simpa [hce, flag_ne_zero, branch] using this
  case LS =>
    have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc hj
    refine ⟨updReg regs .t0 ((cond .LS).eval regs), hag.scratch (.inl rfl) _, ?_⟩
    simpa [hce, flag_ne_zero, branch] using this
  case GE =>
    have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc hj
    refine ⟨updReg regs .t0 ((cond .GE).eval regs), hag.scratch (.inl rfl) _, ?_⟩
    simpa [hce, flag_ne_zero, branch] using this
  case LT =>
    have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc hj
    refine ⟨updReg regs .t0 ((cond .LT).eval regs), hag.scratch (.inl rfl) _, ?_⟩
    simpa [hce, flag_ne_zero, branch] using this
  case GT =>
    have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc hj
    refine ⟨updReg regs .t0 ((cond .GT).eval regs), hag.scratch (.inl rfl) _, ?_⟩
    simpa [hce, flag_ne_zero, branch] using this
  case LE =>
    have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      (ne := true) hfd hc hj
    refine ⟨updReg regs .t0 ((cond .LE).eval regs), hag.scratch (.inl rfl) _, ?_⟩
    simpa [hce, flag_ne_zero, branch] using this

/-- **The comparisons of a computed jump** with the addresses it may reach in the function: a
    jump to the label of one that is the target, or on past them all. -/
theorem conds_steps (hfd : (liftArm fns)[fn]? = some fd) (locals : List (BitVec 64 × LLabel))
    (hc : Cmds fd P (locals.map fun (a, l) =>
      .Lcond (.cmp "eq" (.reg .t2) (.imm (a.toNat : Int))) l))
    (hj : ∀ a l, (a, l) ∈ locals → ∃ j, labelIdx fd.body l = some j) :
    (∃ a l j, (a, l) ∈ locals ∧ regs .t2 = a ∧ labelIdx fd.body l = some j ∧
      Steps (lsys fns) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ []
        ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩) ∨
    Steps (lsys fns) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ []
      ⟨⟨fn, P + locals.length, rv, top⟩ :: rest, regs, m⟩ := by
  induction locals generalizing P with
  | nil => exact .inr (.refl _)
  | cons al ls ih =>
    obtain ⟨a, l⟩ := al
    have hi : fd.body[P]? = some (.Lcond (.cmp "eq" (.reg .t2) (.imm (a.toNat : Int))) l) :=
      hc.head
    have hce : condEval (.cmp "eq" (.reg .t2) (.imm (a.toNat : Int))) regs =
        some (regs .t2 == a) := by
      simp [condEval, operandVal, cmpEval, BitVec.ofInt_natCast]
    obtain ⟨j, hjl⟩ := hj a l List.mem_cons_self
    by_cases ht : regs .t2 = a
    · exact .inl ⟨a, l, j, List.mem_cons_self, ht, hjl,
        Steps.one (step_cond_true hfd hi (hce.trans (by simp [ht])) hjl)⟩
    · have s1 := step_cond_false (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
        hfd hi (hce.trans (by simp [ht]))
      rcases ih (P := P + 1) hc.tail (fun a l h => hj a l (List.mem_cons_of_mem _ h)) with
        ⟨a', l', j', hm, he, hl', hs⟩ | hs
      · exact .inl ⟨a', l', j', List.mem_cons_of_mem _ hm, he, hl',
          by simpa using (Steps.one s1).trans hs⟩
      · refine .inr ?_
        have := (Steps.one s1).trans hs
        simp only [List.length_cons, List.append_nil] at this ⊢
        rwa [show P + (ls.length + 1) = P + 1 + ls.length by omega]

end tests

/-! ## One instruction, matched -/

theorem goesWrong_of {fns : List Fun} {s s' : State armIsa} (hs : Steps (lsys fns) s [] s')
    (hw : (lsys fns).step s' .wrong) : GoesWrong (lsys fns) s [] :=
  ⟨[], List.prefix_refl _, Lprog.Ascent.Behaves.wrong_iff.2 ⟨s', hs, hw⟩⟩

/-- **What the program does for a machine step to `t'`**, from the state `s1` after the
    label: it goes `wrong`; or `t'` is running and the program steps to a state that stands
    for it; or `t'` is not running and the program steps to a trap. -/
def Out (prog : Arm64.Program) (fns : List Fun) (exit : BitVec 64) (s1 : State armIsa)
    (t' : Arm64.State) : Prop :=
  GoesWrong (lsys fns) s1 [] ∨
  (t'.status = .Running ∧ ∃ s', Steps (lsys fns) s1 [] s' ∧
    (Sim prog fns exit s' t' ∨ Ret prog fns exit s' t')) ∨
  (t'.status ≠ .Running ∧ ∃ s', Steps (lsys fns) s1 [] s' ∧ ¬ (lsys fns).accept s' ∧
    (lsys fns).step s' .trap)

/-- The label to give up at is not there, or leads to `Labort`. -/
def AbortOk (fd : Lfundef O Reg) (ab : LLabel) : Prop :=
  labelIdx fd.body ab = none ∨ ∃ j, labelIdx fd.body ab = some j ∧
    fd.body[j]? = some (.Llabel .internal ab) ∧ fd.body[j + 1]? = some .Labort

section out

variable {prog : Arm64.Program} {fns : List Fun} {exit : BitVec 64} {fd : Lfundef O Reg}
  {fn P : Nat} {rv top : BitVec 64} {rest : List Frame} {regs : Reg → BitVec 64}
  {m : Arm64.Memory} {t : Arm64.State}

/-- A jump to the label to give up at goes `wrong`. -/
theorem goesWrong_abort (hfd : (liftArm fns)[fn]? = some fd) {ab : LLabel} (hab : AbortOk fd ab)
    {c : LOperand Reg} (hi : fd.body[P]? = some (.Lcond c ab))
    (hc : condEval c regs = some true) :
    GoesWrong (lsys fns) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ [] := by
  rcases hab with hn | ⟨j, hj, h1, h2⟩
  · exact goesWrong_of (.refl _) (step_cond_wrong hfd hi hc hn)
  · have s1 := step_cond_true (rv := rv) (top := top) (rest := rest) (m := m) hfd hi hc hj
    have s2 := step_label (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m) hfd h1
    exact goesWrong_of (by simpa using (Steps.one s1).trans (Steps.one s2)) (step_abort hfd h2)

/-- **An instruction that does not transfer control**, matched: its operations run or fault
    as the machine does, and the check of the stack pointer after them gives up or goes on. -/
theorem out_ops (hfd : (liftArm fns)[fn]? = some fd) {i : Instr} {os : List O} {ab : LLabel}
    (ho : ops t.pc i = some os)
    (hc : Cmds fd P (os.map .Lopn ++ spCheck ab os))
    (hab : AbortOk fd ab) (hok : Ok t i) (hag : Agree regs m t) (hrun : t.status = .Running)
    (hal : t.spAligned = true) (hld : Loaded prog fns t.mem)
    (hnext : ∀ (Q : Nat) (r' : Reg → BitVec 64) (m' : Arm64.Memory) (t' : Arm64.State),
      Q = P + (os.map LinstrR.Lopn ++ spCheck ab os).length →
      Agree r' m' t' → t'.status = .Running → t'.spAligned = true → Loaded prog fns t'.mem →
      t'.pc = t.pc + 4#64 → Sim prog fns exit ⟨⟨fn, Q, rv, top⟩ :: rest, r', m'⟩ t') :
    Out prog fns exit ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ (prog.evalInst i t) := by
  have hr : Ran (run os regs m) t (prog.evalInst i t) := ops_run hag _ hok ho
  have hst := steps_ops hfd hc.left.opns rv top rest regs m
  cases hrn : run os regs m with
  | none =>
    rw [hrn] at hr hst
    obtain ⟨msg, hmsg⟩ := hr
    exact .inr (.inr ⟨by rw [hmsg]; simp, hst⟩)
  | some rm =>
    obtain ⟨r', m'⟩ := rm
    rw [hrn] at hr hst
    obtain ⟨hag', hst', hpc'⟩ := hr
    have hrun' : (prog.evalInst i t).status = .Running := hst'.trans hrun
    have hld' : Loaded prog fns (prog.evalInst i t).mem := by
      rw [← hag'.mem]
      exact hld.keeps (hag.mem ▸ run_keeps hrn)
    by_cases hw : os.any writesSp = true
    · have hsp : spCheck ab os = [.Lopn (.set .t0 (band (.reg .sp) (num 15))),
          .Lcond (.cmp "ne" (.reg .t0) (.imm 0)) ab] := by simp [spCheck, hw]
      rw [hsp] at hc hnext
      have hc2 := hc.right
      simp only [List.length_map] at hc2
      have e1 := step_opn (rv := rv) (top := top) (rest := rest) (regs := r') (m := m') hfd
        hc2.head (r' := updReg r' .t0 (r' .sp &&& 15#64)) (m' := m') rfl
      have hcond := cond_reg_zero (regs := updReg r' .t0 (r' .sp &&& 15#64)) .t0 true
      by_cases hz : r' .sp &&& 15#64 = 0#64
      · have s2 := step_cond_false (rv := rv) (top := top) (rest := rest) (m := m') hfd
          hc2.tail.head (hcond.trans (by simp [updReg, hz]))
        refine .inr (.inl ⟨hrun', _, by simpa using (hst.trans (Steps.one e1)).trans (Steps.one s2),
          .inl (hnext _ _ m' _ (by simp; omega) (hag'.scratch (.inl rfl) _) hrun' ?_ hld' hpc')⟩)
        simp only [Arm64.State.spAligned, ← hag'.sp]
        simpa using hz
      · refine .inl ?_
        have := Lprog.Ascent.GoesWrong.of_steps (hst.trans (Steps.one e1))
          (goesWrong_abort (rv := rv) (top := top) (rest := rest) (m := m') hfd hab
            hc2.tail.head (hcond.trans (by simp [updReg, hz])))
        simpa using this
    · have hw' : os.any writesSp = false := by simpa using hw
      have hsp : spCheck ab os = [] := by simp [spCheck, hw']
      rw [hsp] at hnext
      refine .inr (.inl ⟨hrun', _, hst, .inl (hnext _ r' m' _ (by simp) hag' hrun' ?_ hld' hpc')⟩)
      have e : (prog.evalInst i t).sp = t.sp := by
        rw [← hag'.sp, run_sp hrn hw', hag.sp]
      simpa [Arm64.State.spAligned, e] using hal

end out

theorem Agree.setPC {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}
    (h : Agree regs m s) (a : BitVec 64) : Agree regs m (s.setPC a) :=
  ⟨h.gpr, h.sp, h.nf, h.zf, h.cf, h.vf, h.mem⟩

@[simp] theorem length_liftArm (fns : List Fun) : (liftArm fns).length = fns.length := by
  simp [liftArm, liftProgram]

/-- The address of a function of the lifted program is its address. -/
theorem addrAt_liftArm (fns : List Fun) (g : Nat) :
    armIsa.addrAt (liftArm fns) g = (fns[g]?).map (·.addr) := by
  simp [Isa.addrAt, liftArm, liftProgram, List.getElem?_map]
  cases fns[g]? <;> rfl

/-- **A function an indirect call finds** is the one at the address called. -/
theorem callee_indirect {fns : List Fun} {regs : Reg → BitVec 64} {e : E} {cands : List Nat}
    {g : Nat} (h : armIsa.callee (liftArm fns) regs (.indirect e cands) = some g) :
    ∃ fg, fns[g]? = some fg ∧ fg.addr = e.eval regs := by
  have := List.find?_some h
  rw [addrAt_liftArm] at this
  cases hg : fns[g]? with
  | none => simp [hg] at this
  | some fg => exact ⟨fg, rfl, by simpa [hg] using this⟩

/-! ## At an instruction -/

/-- The address of the next instruction. -/
theorem addr_succ (base : BitVec 64) (k : Nat) :
    base + BitVec.ofNat 64 (4 * (k + 1)) = base + BitVec.ofNat 64 (4 * k) + 4#64 := by
  rw [BitVec.add_assoc, show 4 * (k + 1) = 4 * k + 4 by omega, BitVec.ofNat_add]

/-- **The innermost activation is past the label of instruction `k`** of function `f`, whose
    commands are in the body `fd`, and the machine is at that instruction. -/
structure Here (prog : Arm64.Program) (fns : List Fun) (exit : BitVec 64) (f : Fun) (k : Nat)
    (fd : Lfundef O Reg) (fn : Nat) (rv top : BitVec 64) (rest : List Frame)
    (regs : Reg → BitVec 64) (m : Arm64.Memory) (t : Arm64.State) : Prop where
  ok : ProgOk fns
  hf : fns[fn]? = some f
  hk : k < f.code.length
  hfd : (liftArm fns)[fn]? = some fd
  cmds : Cmds fd (pos liftI fns f k + 1) (Linked.cmds liftI fns f k hk)
  lbl : ∀ l, l < f.code.length → labelIdx fd.body l = some (pos liftI fns f l)
  hab : AbortOk fd f.code.length
  agree : Agree regs m t
  running : t.status = .Running
  aligned : t.spAligned = true
  loaded : Loaded prog fns t.mem
  tpc : t.pc = f.addr + BitVec.ofNat 64 (4 * k)
  chain : Chain fns exit rest rv

namespace Here

variable {prog : Arm64.Program} {fns : List Fun} {exit : BitVec 64} {f : Fun} {k : Nat}
  {fd : Lfundef O Reg} {fn : Nat} {rv top : BitVec 64} {rest : List Frame}
  {regs : Reg → BitVec 64} {m : Arm64.Memory} {t : Arm64.State}

/-- The address of the instruction. -/
theorem addr (h : Here prog fns exit f k fd fn rv top rest regs m t) :
    (f.code[k]'h.hk).addr = t.pc := by
  rw [h.tpc]; exact (h.ok f (List.mem_of_getElem? h.hf) k h.hk).1

/-- Its size. -/
theorem next (h : Here prog fns exit f k fd fn rv top rest regs m t) :
    (f.code[k]'h.hk).next = t.pc + 4#64 := by
  rw [At.next, h.addr, (h.ok f (List.mem_of_getElem? h.hf) k h.hk).2]

/-- Instruction `l` of the function, from here. -/
theorem jump (h : Here prog fns exit f k fd fn rv top rest regs m t) {r' : Reg → BitVec 64}
    {m' : Arm64.Memory} {t' : Arm64.State} (hag : Agree r' m' t') (hr : t'.status = .Running)
    (hal : t'.spAligned = true) (hld : Loaded prog fns t'.mem) {l : Nat} (hl : l ≤ f.code.length)
    (hpc : t'.pc = f.addr + BitVec.ofNat 64 (4 * l)) :
    Sim prog fns exit ⟨⟨fn, pos liftI fns f l, rv, top⟩ :: rest, r', m'⟩ t' :=
  ⟨hag, hr, hal, hld, ⟨⟨f, h.hf, l, hl, rfl, hpc⟩, h.chain⟩, by simp⟩

/-- The next instruction. -/
theorem step (h : Here prog fns exit f k fd fn rv top rest regs m t) {r' : Reg → BitVec 64}
    {m' : Arm64.Memory} {t' : Arm64.State} (hag : Agree r' m' t') (hr : t'.status = .Running)
    (hal : t'.spAligned = true) (hld : Loaded prog fns t'.mem) (hpc : t'.pc = t.pc + 4#64) :
    Sim prog fns exit ⟨⟨fn, pos liftI fns f (k + 1), rv, top⟩ :: rest, r', m'⟩ t' :=
  h.jump hag hr hal hld h.hk (by rw [hpc, h.tpc, addr_succ])

/-- The activations below a call: this one resumes at the next instruction. -/
theorem below (h : Here prog fns exit f k fd fn rv top rest regs m t) :
    Chain fns exit (⟨fn, pos liftI fns f (k + 1), rv, top⟩ :: rest) (t.pc + 4#64) :=
  ⟨⟨f, h.hf, k + 1, h.hk, rfl, by rw [h.tpc, addr_succ]⟩, h.chain⟩

/-- Function `g`, entered. -/
theorem enter (_ : Here prog fns exit f k fd fn rv top rest regs m t) {r' : Reg → BitVec 64}
    {m' : Arm64.Memory} {t' : Arm64.State} (hag : Agree r' m' t') (hr : t'.status = .Running)
    (hal : t'.spAligned = true) (hld : Loaded prog fns t'.mem) {g : Nat} {fg : Fun}
    (hg : fns[g]? = some fg) (hpc : t'.pc = fg.addr) {ret top' : BitVec 64} {rest' : List Frame}
    (hch : Chain fns exit rest' ret) :
    Sim prog fns exit ⟨⟨g, 0, ret, top'⟩ :: rest', r', m'⟩ t' :=
  ⟨hag, hr, hal, hld, ⟨⟨fg, hg, 0, Nat.zero_le _, by simp, by simpa using hpc⟩, hch⟩, by simp⟩

/-- **An instruction that does not transfer control**, of a kind that is proved. -/
theorem out_data (h : Here prog fns exit f k fd fn rv top rest regs m t) {i : Instr}
    (hpr : proved i = true)
    (hl : Linked.cmds liftI fns f k h.hk = liftOps (cxOf fns f) (f.code[k]'h.hk).addr i) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst i t) := by
  have hc := h.cmds
  have hps := pos_succ liftI fns f k h.hk
  rw [hl] at hc hps
  unfold liftOps at hc hps
  rw [h.addr] at hc hps
  cases ho : ops t.pc i with
  | none =>
    rw [ho] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))
  | some os =>
    rw [ho] at hc hps
    by_cases hokI : okI i = true
    · simp only [hokI, ↓reduceIte] at hc hps
      refine out_ops h.hfd ho hc h.hab (ok_of_okI hokI hpr h.aligned) h.agree h.running h.aligned
        h.loaded fun Q r' m' t' hQ hag hr hal hld hpc => ?_
      have : Q = pos liftI fns f (k + 1) := by
        rw [hQ, hps]
      rw [this]
      exact h.step hag hr hal hld hpc
    · simp only [hokI] at hc
      exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))

/-- **`b`**: a jump inside the function, or a tail call. -/
theorem out_b (h : Here prog fns exit f k fd fn rv top rest regs m t) (off : BitVec 64)
    (hl : Linked.cmds liftI fns f k h.hk = liftB (cxOf fns f) ((f.code[k]'h.hk).addr + off)) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.b off) t) := by
  have hc := h.cmds
  rw [hl, h.addr] at hc
  unfold liftB at hc
  have hag' : Agree regs m (prog.evalInst (.b off) t) := h.agree.setPC _
  cases hlab : (cxOf fns f).label (t.pc + off) with
  | some l =>
    rw [hlab] at hc
    obtain ⟨hlt, hadr⟩ := label_sound fns f hlab
    exact .inr (.inl ⟨h.running, _, Steps.one (step_goto h.hfd hc.head (h.lbl l hlt)),
      .inl (h.jump hag' h.running h.aligned h.loaded (Nat.le_of_lt hlt)
        (hadr.symm.trans (h.ok f (List.mem_of_getElem? h.hf) l hlt).1))⟩)
  | none =>
    rw [hlab] at hc
    cases hent : (cxOf fns f).entry (t.pc + off) with
    | none =>
      rw [hent] at hc
      exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))
    | some g =>
      rw [hent] at hc
      obtain ⟨hg, hadr⟩ := entry_sound fns f hent
      by_cases hsp : regs .sp = top
      · have hs := (step_iff (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
          h.hfd hc.head (.ok (⟨⟨g, 0, rv, top⟩ :: rest, regs, m⟩, []))).2
          (by simp [Isa.stepI, hsp, Isa.callee, hg])
        exact .inr (.inl ⟨h.running, _, Steps.one hs,
          .inl (h.enter hag' h.running h.aligned h.loaded (List.getElem?_eq_getElem hg)
            hadr.symm h.chain)⟩)
      · exact .inl (goesWrong_of (.refl _) ((step_iff h.hfd hc.head _).2
          (by simp [Isa.stepI, hsp])))

/-- **`bl`**: a call. -/
theorem out_bl (h : Here prog fns exit f k fd fn rv top rest regs m t) (off : BitVec 64)
    (hl : Linked.cmds liftI fns f k h.hk =
      liftBl (cxOf fns f) (f.code[k]'h.hk).next ((f.code[k]'h.hk).addr + off)) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.bl off) t) := by
  have hc := h.cmds
  have hps := pos_succ liftI fns f k h.hk
  rw [hl, h.addr, h.next] at hc
  rw [hl] at hps
  unfold liftBl at hc hps
  rw [h.addr] at hps
  have hag' : Agree (updReg regs .x30 (t.pc + 4#64)) m (prog.evalInst (.bl off) t) :=
    (h.agree.dest (r := .gpr 30#5) (show (30#5 : BitVec 5) ≠ 31#5 by decide) _).setPC _
  cases hent : (cxOf fns f).entry (t.pc + off) with
  | none =>
    rw [hent] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))
  | some g =>
    rw [hent] at hc hps
    obtain ⟨hg, hadr⟩ := entry_sound fns f hent
    have hs := (step_iff (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
      h.hfd hc.head (.ok (⟨⟨g, 0, t.pc + 4#64, regs .sp⟩ ::
        ⟨fn, pos liftI fns f k + 1 + 1, rv, top⟩ :: rest, updReg regs .x30 (t.pc + 4#64), m⟩,
        []))).2 (by simp [Isa.stepI, Isa.callee, hg, Frame.at])
    have hbelow := h.below
    rw [hps] at hbelow
    exact .inr (.inl ⟨h.running, _, Steps.one hs,
      .inl (h.enter hag' h.running h.aligned h.loaded (List.getElem?_eq_getElem hg)
        hadr.symm hbelow)⟩)

/-- **`ret`** through the link register. -/
theorem out_ret (h : Here prog fns exit f k fd fn rv top rest regs m t) (rn : Arm64.Reg)
    (hl : Linked.cmds liftI fns f k h.hk =
      if rn = Arm64.Reg.x30 then [.Lret] else [.Labort]) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.ret rn) t) := by
  have hc := h.cmds
  rw [hl] at hc
  by_cases hrn : rn = Arm64.Reg.x30
  · subst hrn
    simp only [↓reduceIte] at hc
    have hag' : Agree regs m (prog.evalInst (.ret Arm64.Reg.x30) t) := h.agree.setPC _
    have hpc : (prog.evalInst (.ret Arm64.Reg.x30) t).pc = regs .x30 :=
      (h.agree.gpr 30#5 (by decide)).symm
    by_cases hra : regs .x30 = rv ∧ regs .sp = top
    · have hs := (step_iff (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
        h.hfd hc.head (.ok (⟨rest, regs, m⟩, []))).2 (by simp [Isa.stepI, hra])
      refine .inr (.inl ⟨h.running, _, Steps.one hs, ?_⟩)
      cases rest with
      | nil =>
        exact .inr ⟨rfl, hag', h.running, h.aligned, h.loaded, by
          rw [hpc, hra.1]; exact h.chain⟩
      | cons fr' rest' =>
        exact .inl ⟨hag', h.running, h.aligned, h.loaded, by rw [hpc, hra.1]; exact h.chain,
          by simp⟩
    · exact .inl (goesWrong_of (.refl _) ((step_iff h.hfd hc.head _).2
        (by simp [Isa.stepI, hra])))
  · simp only [hrn, ↓reduceIte] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))

/-- **A conditional jump**, once the program has taken it or not as the machine does. -/
theorem out_cond (h : Here prog fns exit f k fd fn rv top rest regs m t) {b : Bool}
    {off : BitVec 64} {l : LLabel} (hlab : (cxOf fns f).label (t.pc + off) = some l)
    {r' : Reg → BitVec 64} (hag : Agree r' m t) {Q : Nat} (hQ : pos liftI fns f (k + 1) = Q)
    (hst : Steps (lsys fns) ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩ []
      ⟨⟨fn, if b then pos liftI fns f l else Q, rv, top⟩ :: rest, r', m⟩) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (if b then t.setPC (t.pc + off) else t.advancePC) := by
  cases b with
  | false =>
    subst hQ
    exact .inr (.inl ⟨h.running, _, hst,
      .inl (h.step hag.advancePC h.running h.aligned h.loaded rfl)⟩)
  | true =>
    obtain ⟨hlt, hadr⟩ := label_sound fns f hlab
    exact .inr (.inl ⟨h.running, _, hst,
      .inl (h.jump (t' := t.setPC (t.pc + off)) (hag.setPC _) h.running h.aligned h.loaded
        (Nat.le_of_lt hlt) (hadr.symm.trans (h.ok f (List.mem_of_getElem? h.hf) l hlt).1))⟩)

/-- **`b.cond`.** -/
theorem out_bCond (h : Here prog fns exit f k fd fn rv top rest regs m t) (c : Arm64.CondCode)
    (off : BitVec 64)
    (hl : Linked.cmds liftI fns f k h.hk =
      toLabel (cxOf fns f) ((f.code[k]'h.hk).addr + off) (branch c)) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.bCond c off) t) := by
  have hc := h.cmds
  have hps := pos_succ liftI fns f k h.hk
  rw [hl, h.addr] at hc hps
  unfold toLabel at hc hps
  cases hlab : (cxOf fns f).label (t.pc + off) with
  | none =>
    rw [hlab] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))
  | some l =>
    rw [hlab] at hc hps
    obtain ⟨hlt, -⟩ := label_sound fns f hlab
    obtain ⟨r', hag, hst⟩ := branch_steps (rv := rv) (top := top) (rest := rest) h.hfd c hc
      h.agree (h.lbl l hlt)
    exact h.out_cond hlab hag hps hst

/-- **`cbz` and `cbnz`.** -/
theorem out_cbz (h : Here prog fns exit f k fd fn rv top rest regs m t) (w : RegWidth)
    (nz : Bool) (rt : Arm64.Reg) (off : BitVec 64)
    (hl : Linked.cmds liftI fns f k h.hk =
      toLabel (cxOf fns f) ((f.code[k]'h.hk).addr + off) (liftCbz w nz rt)) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.cbz w nz rt off) t) := by
  have hc := h.cmds
  have hps := pos_succ liftI fns f k h.hk
  rw [hl, h.addr] at hc hps
  unfold toLabel at hc hps
  cases hlab : (cxOf fns f).label (t.pc + off) with
  | none =>
    rw [hlab] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))
  | some l =>
    rw [hlab] at hc hps
    obtain ⟨hlt, -⟩ := label_sound fns f hlab
    have hj := h.lbl l hlt
    -- the machine's test
    have hm : prog.evalInst (.cbz w nz rt off) t =
        if (if nz then t.readReg w rt != 0#64 else t.readReg w rt == 0#64)
        then t.setPC (t.pc + off) else t.advancePC := by
      cases nz <;> simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, bne]
    rw [hm]
    unfold liftCbz at hc hps
    by_cases hokr : okReg rt = true
    · simp only [hokr, ↓reduceIte] at hc hps
      have hwf := wf_of_okReg hokr
      have he := rdw_eval h.agree w hwf
      cases rt with
      | xzr =>
        have hz : t.readReg w .xzr = 0#64 := by cases w <;> rfl
        rw [hz]
        cases nz with
        | true =>
          have hc0 : pos liftI fns f (k + 1) = pos liftI fns f k + 1 := by
            cases w <;> simpa using hps
          exact h.out_cond (b := false) hlab h.agree hc0 (.refl _)
        | false =>
          have hc1 : Cmds fd (pos liftI fns f k + 1) [.Lgoto l] := by
            cases w <;> simpa using hc
          exact h.out_cond (b := true) (Q := pos liftI fns f (k + 1)) hlab h.agree rfl
            (Steps.one (step_goto h.hfd hc1.head hj))
      | sp =>
        have hc2 : Cmds fd (pos liftI fns f k + 1) [.Lopn (.set .t0 (rdw w .sp)),
            .Lcond (.cmp (if nz then "ne" else "eq") (.reg .t0) (.imm 0)) l] := by
          cases w <;> simpa using hc
        have hp2 : pos liftI fns f (k + 1) = pos liftI fns f k + 1 + 2 := by
          cases w <;> simpa using hps
        have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
          h.hfd hc2 hj
        rw [he] at this
        exact h.out_cond hlab (h.agree.scratch (.inl rfl) _) hp2 this
      | gpr i =>
        cases w with
        | W32 =>
          have hc2 : Cmds fd (pos liftI fns f k + 1) [.Lopn (.set .t0 (rdw .W32 (.gpr i))),
              .Lcond (.cmp (if nz then "ne" else "eq") (.reg .t0) (.imm 0)) l] := by
            simpa using hc
          have hp2 : pos liftI fns f (k + 1) = pos liftI fns f k + 1 + 2 := by simpa using hps
          have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
            h.hfd hc2 hj
          rw [he] at this
          exact h.out_cond hlab (h.agree.scratch (.inl rfl) _) hp2 this
        | W64 =>
          have hc1 : Cmds fd (pos liftI fns f k + 1)
              [.Lcond (.cmp (if nz then "ne" else "eq") (.reg (.ofGpr i)) (.imm 0)) l] := by
            simpa using hc
          have hp1 : pos liftI fns f (k + 1) = pos liftI fns f k + 1 + 1 := by simpa using hps
          have := test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
            h.hfd hc1.head hj
          have hv : regs (.ofGpr i) = t.readReg .W64 (.gpr i) := by
            rw [← he]; simp [rdw, rd, trunc]
          rw [hv] at this
          exact h.out_cond hlab h.agree hp1 this
    · simp only [hokr] at hc
      exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))

/-- **`tbz` and `tbnz`.** -/
theorem out_tbz (h : Here prog fns exit f k fd fn rv top rest regs m t) (w : RegWidth)
    (nz : Bool) (rt : Arm64.Reg) (b : Nat) (off : BitVec 64)
    (hl : Linked.cmds liftI fns f k h.hk =
      toLabel (cxOf fns f) ((f.code[k]'h.hk).addr + off) (liftTbz nz rt b)) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.tbz w nz rt b off) t) := by
  have hc := h.cmds
  have hps := pos_succ liftI fns f k h.hk
  rw [hl, h.addr] at hc hps
  unfold toLabel at hc hps
  cases hlab : (cxOf fns f).label (t.pc + off) with
  | none =>
    rw [hlab] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))
  | some l =>
    rw [hlab] at hc hps
    obtain ⟨hlt, -⟩ := label_sound fns f hlab
    have hj := h.lbl l hlt
    unfold liftTbz at hc hps
    by_cases hok : okReg rt = true ∧ b < 64
    · simp only [hok, and_self, ↓reduceIte] at hc hps
      have he : (bit (rd rt) b : E).eval regs = (t.readReg64 rt >>> b) &&& 1#64 := by
        rw [eval_bit, rd_eval h.agree (wf_of_okReg hok.1), Nat.mod_eq_of_lt (by omega)]
      have hm : prog.evalInst (.tbz w nz rt b off) t =
          if (if nz then (t.readReg64 rt >>> b) &&& 1#64 != 0#64
            else (t.readReg64 rt >>> b) &&& 1#64 == 0#64)
          then t.setPC (t.pc + off) else t.advancePC := by
        rw [bit_ne_zero, bit_eq_zero]
        cases nz <;> cases hb : (t.readReg64 rt).getLsbD b <;>
          simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, hb]
      rw [hm]
      have := set_test_steps (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
        h.hfd hc hj
      rw [he] at this
      exact h.out_cond hlab (h.agree.scratch (.inl rfl) _) (by simpa using hps) this
    · simp only [hok, ↓reduceIte] at hc
      exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))

/-- **`blr`**: a call of the function at the address a register holds. -/
theorem out_blr (h : Here prog fns exit f k fd fn rv top rest regs m t) (rn : Arm64.Reg)
    (hl : Linked.cmds liftI fns f k h.hk =
      if okReg rn then [.Lcall (f.code[k]'h.hk).next (.indirect (rd rn) (cxOf fns f).all)]
      else [.Labort]) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.blr rn) t) := by
  have hc := h.cmds
  have hps := pos_succ liftI fns f k h.hk
  rw [hl, h.next] at hc
  rw [hl] at hps
  by_cases hokr : okReg rn = true
  · simp only [hokr, ↓reduceIte] at hc hps
    have hv := rd_eval h.agree (wf_of_okReg hokr)
    have hag' : Agree (updReg regs .x30 (t.pc + 4#64)) m (prog.evalInst (.blr rn) t) :=
      (h.agree.dest (r := .gpr 30#5) (show (30#5 : BitVec 5) ≠ 31#5 by decide) _).setPC _
    cases hcal : armIsa.callee (liftArm fns) regs (.indirect (rd rn) (cxOf fns f).all) with
    | none =>
      exact .inl (goesWrong_of (.refl _) ((step_iff h.hfd hc.head _).2
        (by simp only [Isa.stepI, hcal])))
    | some g =>
      obtain ⟨fg, hg, hadr⟩ := callee_indirect hcal
      have hs := (step_iff (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m)
        h.hfd hc.head (.ok (⟨⟨g, 0, t.pc + 4#64, regs .sp⟩ ::
          ⟨fn, pos liftI fns f k + 1 + 1, rv, top⟩ :: rest, updReg regs .x30 (t.pc + 4#64), m⟩,
          []))).2 (by simp only [Isa.stepI, hcal]; rfl)
      have hbelow := h.below
      rw [hps] at hbelow
      exact .inr (.inl ⟨h.running, _, Steps.one hs,
        .inl (h.enter hag' h.running h.aligned h.loaded hg (hadr.trans hv).symm hbelow)⟩)
  · simp only [hokr] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))

/-- **`svc`, `brk` and the like** are not lifted: the program goes `wrong`. -/
theorem out_system (h : Here prog fns exit f k fd fn rv top rest regs m t) (isHalt : Bool)
    (imm : BitVec 16)
    (hl : Linked.cmds liftI fns f k h.hk = [if isHalt then .Labort else .Lext 0]) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.system isHalt imm) t) := by
  have hc := h.cmds
  rw [hl] at hc
  cases isHalt with
  | true => exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))
  | false =>
    exact .inl (goesWrong_of (.refl _) ((step_iff h.hfd hc.head _).2 (by
      simp [Isa.stepI, armCtx])))

/-- **A tail call through an address**, once the program is at it: the function at the
    address, entered. -/
theorem out_tail (h : Here prog fns exit f k fd fn rv top rest regs m t) {Q : Nat} {e : E}
    {cands : List Nat} {c : LinstrR O Reg}
    (hc : c = if cands.isEmpty then .Labort else .Ltail (.indirect e cands))
    (hi : fd.body[Q]? = some c) {r' : Reg → BitVec 64} (hag : Agree r' m t) {v : BitVec 64}
    (hv : e.eval r' = v)
    (hst : Steps (lsys fns) ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩ []
      ⟨⟨fn, Q, rv, top⟩ :: rest, r', m⟩) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩ (t.setPC v) := by
  subst hc
  by_cases hem : cands.isEmpty = true
  · simp only [hem, ↓reduceIte] at hi
    exact .inl (goesWrong_of hst (step_abort h.hfd hi))
  · simp only [hem, Bool.false_eq_true, ↓reduceIte] at hi
    by_cases hsp : r' .sp = top
    · cases hcal : armIsa.callee (liftArm fns) r' (.indirect e cands) with
      | none =>
        exact .inl (goesWrong_of hst ((step_iff h.hfd hi _).2
          (by simp only [Isa.stepI, hcal]; simp [hsp])))
      | some g =>
        obtain ⟨fg, hg, hadr⟩ := callee_indirect hcal
        have hs := (step_iff (rv := rv) (top := top) (rest := rest) (regs := r') (m := m)
          h.hfd hi (.ok (⟨⟨g, 0, rv, top⟩ :: rest, r', m⟩, []))).2
          (by simp only [Isa.stepI, hcal]; simp [hsp])
        exact .inr (.inl ⟨h.running, _, by simpa using hst.trans (Steps.one hs),
          .inl (h.enter (t' := t.setPC v) (hag.setPC _) h.running h.aligned h.loaded hg
            (hv ▸ hadr.symm) h.chain)⟩)
    · exact .inl (goesWrong_of hst ((step_iff h.hfd hi _).2 (by simp [Isa.stepI, hsp])))

/-- **`br`**: a computed jump, to an instruction of the function the program holds the address
    of, or to another function. -/
theorem out_br (h : Here prog fns exit f k fd fn rv top rest regs m t) (rn : Arm64.Reg)
    (hl : Linked.cmds liftI fns f k h.hk =
      if okReg rn then Linked.jump .t2 (rd rn) [] (cxOf fns f).cands (cxOf fns f).all
      else [.Labort]) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst (.br rn) t) := by
  have hc := h.cmds
  rw [hl] at hc
  by_cases hokr : okReg rn = true
  · simp only [hokr, ↓reduceIte] at hc
    have hv := rd_eval h.agree (wf_of_okReg hokr)
    unfold Linked.jump at hc
    split at hc
    · exact h.out_tail rfl hc.head h.agree hv (.refl _)
    · simp only [List.append_nil, List.cons_append, List.nil_append] at hc
      have s1 := step_opn (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m) h.hfd
        hc.head (r' := updReg regs .t2 (t.readReg64 rn)) (m' := m) (by simp [Op.eval, hv])
      have hag' : Agree (updReg regs .t2 (t.readReg64 rn)) m t :=
        h.agree.scratch (.inr (.inr rfl)) _
      have hmem : ∀ a l, (a, l) ∈ (cxOf fns f).cands → (cxOf fns f).label a = some l := by
        intro a l hal
        obtain ⟨a', -, ha'⟩ := List.mem_filterMap.1 hal
        cases hla : (labelsOf f.code)[a']? with
        | none => simp [hla] at ha'
        | some l' =>
          simp only [hla, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha'
          obtain ⟨rfl, rfl⟩ := ha'
          exact hla
      rcases conds_steps (rv := rv) (top := top) (rest := rest)
          (regs := updReg regs .t2 (t.readReg64 rn)) (m := m) h.hfd _ hc.tail.left
          (fun a l hal => by
            obtain ⟨hlt, -⟩ := label_sound fns f (hmem a l hal)
            exact ⟨_, h.lbl l hlt⟩) with ⟨a, l, j, hal, ha, hjl, hs⟩ | hs
      · obtain ⟨hlt, hadr⟩ := label_sound fns f (hmem a l hal)
        have hj : j = pos liftI fns f l := by
          have := h.lbl l hlt
          rw [hjl] at this
          exact Option.some.inj this
        subst hj
        have ha' : t.readReg64 rn = a := by simpa [updReg] using ha
        exact .inr (.inl ⟨h.running, _, by simpa using (Steps.one s1).trans hs,
          .inl (h.jump (t' := t.setPC (t.readReg64 rn)) (hag'.setPC _) h.running h.aligned
            h.loaded (Nat.le_of_lt hlt)
            (ha'.trans (hadr.symm.trans (h.ok f (List.mem_of_getElem? h.hf) l hlt).1)))⟩)
      · exact h.out_tail (e := .reg .t2) rfl hc.tail.right.head hag' (by simp [updReg])
          (by simpa using (Steps.one s1).trans hs)
  · simp only [hokr] at hc
    exact .inl (goesWrong_of (.refl _) (step_abort h.hfd hc.head))

/-- **One instruction, matched**, whichever it is. -/
theorem out (h : Here prog fns exit f k fd fn rv top rest regs m t) {i : Instr}
    (hi : (f.code[k]'h.hk).instr = some i) (hpr : proved i = true) :
    Out prog fns exit ⟨⟨fn, pos liftI fns f k + 1, rv, top⟩ :: rest, regs, m⟩
      (prog.evalInst i t) := by
  have hcm : Linked.cmds liftI fns f k h.hk =
      liftI (cxOf fns f) ((withPrev f.code)[k]'(by simpa using h.hk)).2 (f.code[k]'h.hk) := rfl
  unfold liftI at hcm
  simp only [hi] at hcm
  cases i with
  | b off => exact h.out_b off hcm
  | bl off => exact h.out_bl off hcm
  | bCond c off => exact h.out_bCond c off hcm
  | cbz w nz rt off => exact h.out_cbz w nz rt off hcm
  | tbz w nz rt b off => exact h.out_tbz w nz rt b off hcm
  | br rn => exact h.out_br rn hcm
  | blr rn => exact h.out_blr rn hcm
  | ret rn => exact h.out_ret rn hcm
  | system isHalt imm => exact h.out_system isHalt imm hcm
  | _ => exact h.out_data hpr hcm

end Here

/-! ## One machine step, matched -/

/-- **Every instruction of the program is of a kind that is proved** (`proved`). -/
def Proved (fns : List Fun) : Prop :=
  ∀ f ∈ fns, ∀ k (hk : k < f.code.length) (i : Instr), f.code[k].instr = some i → proved i = true

/-- **One machine step, matched at Lprog**: from the label of an instruction, the label and
    then the instruction's commands. The program goes `wrong` on the way, or matches the
    machine. -/
theorem back {prog : Arm64.Program} {fns : List Fun} {exit : BitVec 64} (hok : ProgOk fns)
    (hpr : Proved fns) {s : State armIsa} {t : Arm64.State} (hs : Sim prog fns exit s t) :
    GoesWrong (lsys fns) s [] ∨
      Lprog.Ascent.Matched (lsys fns) (mstep prog) (fun _ => False) (Sim prog fns exit)
        (Ret prog fns exit) (fun _ _ => False) s t := by
  obtain ⟨stk, regs, m⟩ := s
  cases stk with
  | nil => exact absurd rfl hs.ne
  | cons fr rest =>
    obtain ⟨fn, pc, rv, top⟩ := fr
    obtain ⟨⟨f, hf, k, hk, hpc, htpc⟩, hchain⟩ := hs.chain
    simp only at hf hpc
    subst hpc
    obtain ⟨tail, hfd, htail⟩ := getElem?_liftProgram liftI fns hf
    have hno : NoLabel (fun z => liftI (cxOf fns f) z.2 z.1) (withPrev f.code) :=
      fun z _ c hc l => noLab_liftI _ _ _ c hc l
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · -- at an instruction: its label, then its commands
      have s0 := step_label (rv := rv) (top := top) (rest := rest) (regs := regs) (m := m) hfd
        (getElem?_label liftI fns f tail k hk)
      have hH : Here prog fns exit f k _ fn rv top rest regs m t :=
        { ok := hok, hf := hf, hk := hk, hfd := hfd
          cmds := fun j hj => (getElem?_cmd liftI fns f tail k hk j hj).trans
            (List.getElem?_eq_getElem hj)
          lbl := fun l hl => labelIdx_label liftI fns f tail hno l hl
          hab := by
            rcases labelIdx_abort liftI fns f tail hno htail with h | ⟨j, h1, h2, h3⟩
            · exact .inl h
            · exact .inr ⟨j, h1, h2, h3⟩
          agree := hs.agree, running := hs.running, aligned := hs.aligned, loaded := hs.loaded
          tpc := htpc, chain := hchain }
      cases hi : (f.code[k]'hk).instr with
      | none =>
        have hc := hH.cmds
        have hcm : Linked.cmds liftI fns f k hk = [.Labort] := by
          show liftI _ _ _ = _
          unfold liftI
          simp only [hi]
        rw [hcm] at hc
        refine .inl ?_
        simpa using Lprog.Ascent.GoesWrong.of_steps (Steps.one s0)
          (goesWrong_of (.refl _) (step_abort hfd hc.head))
      | some i =>
        have hfetch : prog.fetchMem t.mem t.pc = some i := by
          rw [← hH.addr]
          exact hs.loaded f (List.mem_of_getElem? hf) k hk i hi
        rcases hH.out hi (hpr f (List.mem_of_getElem? hf) k hk i hi) with
          hw | ⟨hr, s', hs', hsim⟩ | ⟨hnr, s', hs', hna, htr⟩
        · exact .inl (by simpa using Lprog.Ascent.GoesWrong.of_steps (Steps.one s0) hw)
        · refine .inr ⟨fun t' ht' => ?_, fun h => h.elim, fun ht' _ => ?_⟩
          · obtain ⟨hst, -⟩ := ht'
            rw [step_of_fetch hs.running hfetch] at hst
            subst hst
            exact ⟨s', by simpa using (Steps.one s0).trans hs', hsim⟩
          · obtain ⟨t', hst, hnr⟩ := ht'
            rw [step_of_fetch hs.running hfetch] at hst
            subst hst
            exact absurd hr hnr
        · refine .inr ⟨fun t' ht' => ?_, fun h => h.elim, fun ht' _ => ?_⟩
          · obtain ⟨hst, hr⟩ := ht'
            rw [step_of_fetch hs.running hfetch] at hst
            subst hst
            exact absurd hr hnr
          · exact ⟨s', by simpa using (Steps.one s0).trans hs', hna, htr⟩
    · -- past the last instruction
      exact .inl (goesWrong_of (.refl _) (step_abort hfd (getElem?_end liftI fns f tail)))

/-! ## The transfer theorem -/

/-- The judgement over the machine: `Lprog.Ascent.SafeN` at arm64-semantics' step, where no
    state accepts. -/
abbrev MSafeN (prog : Arm64.Program) (G : Arm64.State → Prop) (n : Nat)
    (P : Arm64.State → Prop) (t : Arm64.State) : Prop :=
  Lprog.Ascent.SafeN (mstep prog) (fun _ => False) G n P t

/-- **The transfer theorem for AArch64.** A simulated state safe at Lprog at every budget
    makes the machine state safe over arm64-semantics, given the machine's continuation where
    the program has returned: in a state the returned program stands for, at `exit`. -/
theorem transfer {prog : Arm64.Program} {fns : List Fun} (hok : ProgOk fns) (hpr : Proved fns)
    {G : Arm64.State → Prop} {N : Nat} {P : Arm64.State → Prop} {exit : BitVec 64}
    {Q : State armIsa → Prop}
    (hret : ∀ s' t', Ret prog fns exit s' t' → Q s' → MSafeN prog G N P t') :
    ∀ n, n ≤ N → ∀ s t, Sim prog fns exit s t → Lprog.Ascent.AllSafe (lsys fns) Q s →
      MSafeN prog G n P t :=
  Lprog.Ascent.transfer (S := Sim prog fns exit) (T := Ret prog fns exit) (U := fun _ _ => False)
    (fun _ _ hs => back hok hpr hs) (fun _ h => h) (fun _ _ h => h.elim)
    (fun s' t' hT hL => hret s' t' hT (hL.acc (Or.inl hT.1)))

/-- A machine state seen through Lprog's registers: the lift's own hold zero. -/
def regsOf (t : Arm64.State) : Reg → BitVec 64
  | .x0 => t.regs.read 0 | .x1 => t.regs.read 1 | .x2 => t.regs.read 2 | .x3 => t.regs.read 3
  | .x4 => t.regs.read 4 | .x5 => t.regs.read 5 | .x6 => t.regs.read 6 | .x7 => t.regs.read 7
  | .x8 => t.regs.read 8 | .x9 => t.regs.read 9 | .x10 => t.regs.read 10
  | .x11 => t.regs.read 11 | .x12 => t.regs.read 12 | .x13 => t.regs.read 13
  | .x14 => t.regs.read 14 | .x15 => t.regs.read 15 | .x16 => t.regs.read 16
  | .x17 => t.regs.read 17 | .x18 => t.regs.read 18 | .x19 => t.regs.read 19
  | .x20 => t.regs.read 20 | .x21 => t.regs.read 21 | .x22 => t.regs.read 22
  | .x23 => t.regs.read 23 | .x24 => t.regs.read 24 | .x25 => t.regs.read 25
  | .x26 => t.regs.read 26 | .x27 => t.regs.read 27 | .x28 => t.regs.read 28
  | .x29 => t.regs.read 29 | .x30 => t.regs.read 30
  | .sp => t.sp
  | .nf => flag t.pstate.n | .zf => flag t.pstate.z | .cf => flag t.pstate.c
  | .vf => flag t.pstate.v
  | .t0 | .t1 | .t2 => 0#64

theorem regsOf_gpr (t : Arm64.State) (i : BitVec 5) (hi : i ≠ 31#5) :
    regsOf t (.ofGpr i) = t.regs.read i := by
  have key : ∀ n, n < 31 →
      regsOf t (.ofGpr (BitVec.ofNat 5 n)) = t.regs.read (BitVec.ofNat 5 n) := by
    intro n hn
    match n, hn with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
    | 8, _ => rfl
    | 9, _ => rfl
    | 10, _ => rfl
    | 11, _ => rfl
    | 12, _ => rfl
    | 13, _ => rfl
    | 14, _ => rfl
    | 15, _ => rfl
    | 16, _ => rfl
    | 17, _ => rfl
    | 18, _ => rfl
    | 19, _ => rfl
    | 20, _ => rfl
    | 21, _ => rfl
    | 22, _ => rfl
    | 23, _ => rfl
    | 24, _ => rfl
    | 25, _ => rfl
    | 26, _ => rfl
    | 27, _ => rfl
    | 28, _ => rfl
    | 29, _ => rfl
    | 30, _ => rfl
    | n + 31, h => exact absurd h (by omega)
  have := key i.toNat (by bv_omega)
  simpa using this

theorem agree_regsOf (t : Arm64.State) : Agree (regsOf t) t.mem t :=
  ⟨regsOf_gpr t, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The transfer theorem, from a function's entry.** A running machine at the entry of
    function `g` of a program it holds, with its stack pointer aligned, is safe if the call of
    `g` is safe at Lprog at every budget, given the machine's continuation where `g` has
    returned: in a state the returned program stands for, at the address in `x30`. -/
theorem SafeN.of_lift {prog : Arm64.Program} {fns : List Fun} (hok : ProgOk fns)
    (hpr : Proved fns) {g : Nat} {fg : Fun} (hg : fns[g]? = some fg) {t : Arm64.State}
    (hpc : t.pc = fg.addr) (hrun : t.status = .Running) (hal : t.spAligned = true)
    (hld : Loaded prog fns t.mem) {Q : State armIsa → Prop}
    (hL : Lprog.Ascent.AllSafe (lsys fns) Q
      ⟨[⟨g, 0, t.regs.read 30, t.sp⟩], regsOf t, t.mem⟩)
    {G : Arm64.State → Prop} {N : Nat} {P : Arm64.State → Prop}
    (hret : ∀ s' t', Ret prog fns (t.regs.read 30) s' t' → Q s' → MSafeN prog G N P t') :
    MSafeN prog G N P t :=
  transfer hok hpr hret N (Nat.le_refl N) ⟨[⟨g, 0, t.regs.read 30, t.sp⟩], regsOf t, t.mem⟩ t
    ⟨agree_regsOf t, hrun, hal, hld,
      ⟨⟨fg, hg, 0, Nat.zero_le _, by simp, by simpa using hpc⟩, rfl⟩, by simp⟩ hL

end MachineChecked.ARM.Lift
