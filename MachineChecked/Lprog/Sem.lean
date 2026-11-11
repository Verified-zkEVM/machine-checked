/-
  MachineChecked.Lprog.Sem

  The semantics of an Lprog program under an instruction set and an execution context.

  catcrypt-compiler runs Lprog over a state fixed by its x86 back end: named word arrays and
  the flags `zf`/`cf`/`of`. Here an instruction set `Isa` chooses its operation type `Op`, its
  registers `Reg` (with a link register and a stack register) and the state `M` beside the
  registers (memory, flags, anything else), and gives the meaning of an operation and of a
  condition. An execution context (`Context`) gives the meaning of `Lext` and says which
  states accept. Control flow is shared by every instruction set.

  A state is a stack of activations (`Frame`: the function, the counter in its body, the
  return value the call put in the link register and the stack pointer at the call), the
  register file, which is global as on a machine, and the rest. A step is a relation, since an
  external call may have many results, and ends in a state, in a `trap` (the machine is stuck
  too: a fault; safe) or in `wrong` (an assumption of the program is violated; unsafe):

  * `Lcall` pushes a frame and writes its return value to the link register; `Lret` pops it,
    and is defined only if the link register holds that value again and the stack pointer is
    back where it was at the call, so return-address integrity is part of every proof;
  * `Ltail` replaces the current frame, and is defined only if the stack pointer is back;
  * an indirect call or jump whose target is none of its candidates, a jump to a missing
    label, running off the end of a body and `Labort` go `wrong`.

  The judgement is the generic one (`Ascent.SafeN`) at this step relation. A state accepts when
  the program has returned (the stack is empty: `Q` then says what the outermost function
  leaves behind) or when it is at an `Lext` the context accepts.

  ## Main definitions

  * `Isa`, `Frame`, `State`, `Context`, `Isa.step`, `Isa.accept`, `Isa.SafeN`

  ## Main results

  * `SafeN.label`, `opn`, `fault`, `goto`, `cond`, `call`, `tail`, `ret`, `ext`, `returned`:
    one rule per instruction, in continuation form
-/

import MachineChecked.Lprog.Syntax
import MachineChecked.Ascent.Safe

namespace MachineChecked.Lprog

open MachineChecked.Ascent (Outcome)

/-- An instruction set for Lprog: operations, registers, the state beside the registers, and
    the meaning of operations and conditions. -/
structure Isa where
  /-- The operations of `Lopn`. -/
  Op : Type
  /-- The registers. -/
  Reg : Type
  [decEq : DecidableEq Reg]
  /-- The register a call writes its return value to. -/
  link : Reg
  /-- The stack pointer. -/
  sp : Reg
  /-- The machine state beside the registers. -/
  M : Type
  /-- An operation on registers and state; `none` is a fault. -/
  opn : Op → (Reg → BitVec 64) → M → Option ((Reg → BitVec 64) × M)
  /-- A branch condition; `none` is a condition the instruction set does not have. -/
  cond : LOperand Reg → (Reg → BitVec 64) → M → Option Bool

attribute [instance] Isa.decEq

/-- A register file with one register changed. -/
def updReg {Reg : Type} [DecidableEq Reg] (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) :
    Reg → BitVec 64 :=
  fun r' => if r' = r then v else regs r'

theorem updReg_apply {Reg : Type} [DecidableEq Reg] (regs : Reg → BitVec 64) (r r' : Reg)
    (v : BitVec 64) : updReg regs r v r' = if r' = r then v else regs r' := rfl

/-- An activation: the function, the counter in its body, the value the call put in the link
    register, and the stack pointer at the call. -/
structure Frame where
  fn : Nat
  pc : Nat
  ret : BitVec 64
  top : BitVec 64
  deriving DecidableEq, Repr

/-- The frame at another counter. -/
def Frame.at (fr : Frame) (pc : Nat) : Frame := { fr with pc }

@[simp] theorem Frame.at_fn (fr : Frame) (pc : Nat) : (fr.at pc).fn = fr.fn := rfl
@[simp] theorem Frame.at_pc (fr : Frame) (pc : Nat) : (fr.at pc).pc = pc := rfl
@[simp] theorem Frame.at_ret (fr : Frame) (pc : Nat) : (fr.at pc).ret = fr.ret := rfl
@[simp] theorem Frame.at_top (fr : Frame) (pc : Nat) : (fr.at pc).top = fr.top := rfl

/-- The state of a run: the activations (innermost first; empty once the program has
    returned), the registers and the rest. -/
structure State (I : Isa) where
  stack : List Frame
  regs : I.Reg → BitVec 64
  m : I.M

/-- An execution context: the meaning of `Lext`, a relation from the registers and state
    before to the outcomes after, and the states that accept. -/
structure Context (I : Isa) where
  ext : (I.Reg → BitVec 64) → I.M → Outcome ((I.Reg → BitVec 64) × I.M) → Prop
  accept : (I.Reg → BitVec 64) → I.M → Prop

/-- Is this the label `l`? -/
def isLabel {Op Reg : Type} (l : LLabel) : LinstrR Op Reg → Bool
  | .Llabel _ l' => l' == l
  | _ => false

/-- The index of label `l` in a body. -/
def labelIdx {Op Reg : Type} (body : Lcmd Op Reg) (l : LLabel) : Option Nat :=
  body.findIdx? (isLabel l)

namespace Isa

variable (I : Isa) (p : Lprog I.Op I.Reg) (c : Context I)

/-- The address of function `f`. -/
def addrAt (f : Nat) : Option (BitVec 64) := (p[f]?).map (·.addr)

/-- The function a call calls, if it is one of the program's. -/
def callee (regs : I.Reg → BitVec 64) : Target I.Reg → Option Nat
  | .direct f => if f < p.length then some f else none
  | .indirect e cands => cands.find? fun f => I.addrAt p f == some (e.eval regs)

/-- The instruction the innermost activation is at. -/
def fetch (s : State I) : Option (LinstrR I.Op I.Reg) :=
  match s.stack with
  | [] => none
  | fr :: _ => (p[fr.fn]?).bind fun fd => fd.body[fr.pc]?

/-- One instruction, from activation `fr` over `rest`, in function body `body`. -/
def stepI (body : Lcmd I.Op I.Reg) (fr : Frame) (rest : List Frame) (regs : I.Reg → BitVec 64)
    (m : I.M) : LinstrR I.Op I.Reg → Outcome (State I) → Prop
  | .Lopn op, o => match I.opn op regs m with
    | some (r', m') => o = .ok ⟨fr.at (fr.pc + 1) :: rest, r', m'⟩
    | none => o = .trap
  | .Llabel .., o => o = .ok ⟨fr.at (fr.pc + 1) :: rest, regs, m⟩
  | .Lgoto l, o => match labelIdx body l with
    | some j => o = .ok ⟨fr.at j :: rest, regs, m⟩
    | none => o = .wrong
  | .Lcond cnd l, o => match I.cond cnd regs m with
    | some true => match labelIdx body l with
      | some j => o = .ok ⟨fr.at j :: rest, regs, m⟩
      | none => o = .wrong
    | some false => o = .ok ⟨fr.at (fr.pc + 1) :: rest, regs, m⟩
    | none => o = .wrong
  | .Ligoto e cands, o => match cands.find? (fun x => x.1 == e.eval regs) with
    | some (_, l) => match labelIdx body l with
      | some j => o = .ok ⟨fr.at j :: rest, regs, m⟩
      | none => o = .wrong
    | none => o = .wrong
  | .Lcall ret tgt, o => match I.callee p regs tgt with
    | some f => o = .ok ⟨⟨f, 0, ret, regs I.sp⟩ :: fr.at (fr.pc + 1) :: rest, updReg regs I.link ret, m⟩
    | none => o = .wrong
  | .Ltail tgt, o =>
    if regs I.sp = fr.top then match I.callee p regs tgt with
      | some f => o = .ok ⟨⟨f, 0, fr.ret, fr.top⟩ :: rest, regs, m⟩
      | none => o = .wrong
    else o = .wrong
  | .Lret, o =>
    if regs I.link = fr.ret ∧ regs I.sp = fr.top then o = .ok ⟨rest, regs, m⟩ else o = .wrong
  | .Lext, o => match o with
    | .ok t => t.stack = fr.at (fr.pc + 1) :: rest ∧ c.ext regs m (.ok (t.regs, t.m))
    | .trap => c.ext regs m .trap
    | .wrong => c.ext regs m .wrong
  | .Labort, o => o = .wrong

/-- **One step** of a program. A returned program has none; an activation with no instruction
    goes `wrong`. -/
def step (s : State I) (o : Outcome (State I)) : Prop :=
  match s.stack with
  | [] => False
  | fr :: rest => match p[fr.fn]? with
    | none => o = .wrong
    | some fd => match fd.body[fr.pc]? with
      | none => o = .wrong
      | some i => I.stepI p c fd.body fr rest s.regs s.m i o

/-- The accepting states: the program has returned, or it is at an `Lext` the context
    accepts. -/
def accept (s : State I) : Prop :=
  s.stack = [] ∨ (I.fetch p s = some .Lext ∧ c.accept s.regs s.m)

/-- **The judgement** at Lprog: the generic one at `step` and `accept`. -/
abbrev SafeN (G : State I → Prop) (n : Nat) (Q : State I → Prop) (s : State I) : Prop :=
  Ascent.SafeN (I.step p c) (I.accept p c) G n Q s

end Isa

/-! ## One rule per instruction

Each rule takes the state at an instruction of the innermost activation (`⟨fn, pc, ret, top⟩`
over `rest`, in function `fd` of the program) and gives `SafeN` there from `SafeN` at every
state the instruction may continue in, at the same budget. -/

namespace SafeN

open Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {c : Context I} {G : State I → Prop} {n : Nat}
  {Q : State I → Prop} {fr : Frame} {rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M}
  {fd : Lfundef I.Op I.Reg} {fn pc : Nat} {rv top : BitVec 64}

/-- The step at an instruction, through the program's lookups. -/
theorem step_eq (hf : p[fr.fn]? = some fd) {i : LinstrR I.Op I.Reg} (hi : fd.body[fr.pc]? = some i)
    (o : Outcome (State I)) :
    I.step p c ⟨fr :: rest, regs, m⟩ o ↔ I.stepI p c fd.body fr rest regs m i o := by
  simp only [Isa.step, hf, hi]

theorem fetch_eq (hf : p[fr.fn]? = some fd) {i : LinstrR I.Op I.Reg}
    (hi : fd.body[fr.pc]? = some i) : I.fetch p ⟨fr :: rest, regs, m⟩ = some i := by
  simp [Isa.fetch, hf, hi]

/-- A state at an instruction other than `Lext` does not accept. -/
theorem not_accept (hf : p[fr.fn]? = some fd) {i : LinstrR I.Op I.Reg}
    (hi : fd.body[fr.pc]? = some i) (hne : i ≠ .Lext) : ¬ I.accept p c ⟨fr :: rest, regs, m⟩ := by
  rintro (h | ⟨h, -⟩)
  · cases h
  · rw [fetch_eq hf hi] at h; exact hne (Option.some.inj h)

/-- An instruction with one result, at the same budget. -/
theorem of_one {i : LinstrR I.Op I.Reg} (hf : p[fr.fn]? = some fd) (hi : fd.body[fr.pc]? = some i)
    (hne : i ≠ .Lext) {t : State I} (hs : ∀ o, I.stepI p c fd.body fr rest regs m i o → o = .ok t)
    (h : I.SafeN p c G n Q t) : I.SafeN p c G n Q ⟨fr :: rest, regs, m⟩ :=
  Ascent.SafeN.of_step (not_accept hf hi hne) (fun o ho => hs o ((step_eq hf hi o).1 ho)) h

theorem label {kd : LabelKind} {l : LLabel} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Llabel kd l))
    (h : I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi nofun (fun _ ho => ho) h

theorem opn {op : I.Op} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn op))
    {r' : I.Reg → BitVec 64} {m' : I.M} (he : I.opn op regs m = some (r', m'))
    (h : I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi nofun (fun o ho => by simpa [Frame.at, Isa.stepI, he] using ho) h

/-- A faulting operation: the run stops, safely. -/
theorem fault {op : I.Op} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn op))
    (he : I.opn op regs m = none) : I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Ascent.SafeN.stuck (fun o ho => by simpa [Frame.at, Isa.stepI, he] using (step_eq hf hi o).1 ho)
    (fun ha => absurd ha (not_accept hf hi nofun))

theorem goto {l : LLabel} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lgoto l))
    {j : Nat} (hl : labelIdx fd.body l = some j)
    (h : I.SafeN p c G n Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩) : I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi nofun (fun o ho => by simpa [Frame.at, Isa.stepI, hl] using ho) h

theorem cond {cnd : LOperand I.Reg} {l : LLabel} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcond cnd l)) {b : Bool} (hc : I.cond cnd regs m = some b)
    {j : Nat} (hl : labelIdx fd.body l = some j)
    (ht : b = true → I.SafeN p c G n Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩)
    (hn : b = false → I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  cases b
  · exact of_one hf hi nofun (fun o ho => by simpa [Frame.at, Isa.stepI, hc] using ho) (hn rfl)
  · exact of_one hf hi nofun (fun o ho => by simpa [Frame.at, Isa.stepI, hc, hl] using ho) (ht rfl)

theorem call {ret : BitVec 64} {tgt : Target I.Reg} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcall ret tgt)) {f : Nat} (hc : I.callee p regs tgt = some f)
    (h : I.SafeN p c G n Q
      ⟨⟨f, 0, ret, regs I.sp⟩ :: ⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs I.link ret, m⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi nofun (fun o ho => by simpa [Frame.at, Isa.stepI, hc] using ho) h

theorem tail {tgt : Target I.Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Ltail tgt))
    (hsp : regs I.sp = top) {f : Nat} (hc : I.callee p regs tgt = some f)
    (h : I.SafeN p c G n Q ⟨⟨f, 0, rv, top⟩ :: rest, regs, m⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi nofun (fun o ho => by simpa [Frame.at, Isa.stepI, hsp, hc] using ho) h

theorem ret (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some .Lret)
    (hra : regs I.link = rv) (hsp : regs I.sp = top)
    (h : I.SafeN p c G n Q ⟨rest, regs, m⟩) : I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_one hf hi nofun (fun o ho => by simpa [Frame.at, Isa.stepI, hra, hsp] using ho) h

/-- An external call: safe if it accepts only where `Q` holds, never goes `wrong`, and every
    state it may continue in is safe. -/
theorem ext (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some .Lext)
    (hacc : c.accept regs m → Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩) (hw : ¬ c.ext regs m .wrong)
    (h : ∀ r' m', c.ext regs m (.ok (r', m')) → I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  refine Ascent.SafeN.mono (Nat.le_succ n) (Ascent.SafeN.intro ?_ fun o ho => ?_)
  · rintro (h | ⟨-, ha⟩)
    · cases h
    · exact hacc ha
  · have ho := (step_eq hf hi o).1 ho
    match o, ho with
    | .ok ⟨_, r', m'⟩, ⟨rfl, he⟩ => exact h r' m' he
    | .trap, _ => trivial
    | .wrong, he => exact hw he

/-- A returned program: `Q` must hold. -/
theorem returned (hq : Q ⟨[], regs, m⟩) : I.SafeN p c G n Q ⟨[], regs, m⟩ :=
  Ascent.SafeN.stuck (fun _ h => h.elim) fun _ => hq

end SafeN

end MachineChecked.Lprog
