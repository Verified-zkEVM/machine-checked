/-
  MachineChecked.ARM.Lift.Transfer

  **The lift of AArch64 is correct**: `SafeN` proved at Lprog for a lifted program gives
  `SafeN` over arm64-semantics' `Step`. In progress: this file has the two systems, the
  simulation relation, and how a run of an instruction's operations is steps of the program.

  ## Main definitions

  * `armCtx`, `lsys`, `mstep`: the lifted program and the machine, as systems
  * `ProgOk`, `Loaded`, `Chain`, `Sim`, `Ret`: the simulation

  ## Main results

  * `step_of_fetch`: the machine's step at a fetched instruction
  * `steps_ops`: the operations of an instruction, as steps of the program
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

end Here

end MachineChecked.ARM.Lift
