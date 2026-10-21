/-
  MachineChecked.Lprog.Sem

  The semantics of an Lprog body under an instruction set.

  catcrypt-compiler runs Lprog over a state fixed by its x86 back end: named word arrays and
  the flags `zf`/`cf`/`of`. Here an instruction set `Isa` chooses its operation type `Op` and
  the state `M` beside the registers (memory, flags, anything else), and gives the meaning of
  an operation and of a condition. Control flow is shared by every instruction set:
  `Llabel`/`Lalign` fall through, `Lgoto` and a taken `Lcond` jump to their label, `Lcall` with
  a link register jumps and stores the index after it, `Ligoto` jumps to the index a register
  holds, and `Lret` leaves the body (to the index past its end, so that a return and running
  off the end halt in different states). A run halts when no instruction is at the counter.

  Runs are the generic ones of `Ascent.Run` over `Isa.step`: `Isa.Reaches` is
  `Ascent.Reaches`, and `Isa.Halts` asks for a halted state.
-/

import MachineChecked.Lprog.Syntax
import MachineChecked.Ascent.Run

namespace MachineChecked.Lprog

/-- An instruction set for Lprog: operations, the state beside the registers, and the meaning
    of operations and conditions. -/
structure Isa where
  /-- The operations of `Lopn`. -/
  Op : Type
  /-- The machine state beside the registers. -/
  M : Type
  /-- An operation on registers and state; `none` is a fault. -/
  opn : Op → (String → BitVec 64) → M → Option ((String → BitVec 64) × M)
  /-- A branch condition; `none` is a fault. -/
  cond : LOperand → (String → BitVec 64) → M → Option Bool

/-- The state of a run: the instruction counter, the registers and the rest. -/
structure State (I : Isa) where
  pc : Nat
  regs : String → BitVec 64
  m : I.M

/-- A register file with one register changed. -/
def updReg (regs : String → BitVec 64) (r : String) (v : BitVec 64) : String → BitVec 64 :=
  fun r' => if r' = r then v else regs r'

/-- Is this the label `l`? -/
def isLabel {Op : Type} (l : LLabel) : LinstrR Op → Bool
  | .Llabel _ l' => l' == l
  | _ => false

/-- The index of label `l` in a body. -/
def labelIdx {Op : Type} (body : Lcmd Op) (l : LLabel) : Option Nat :=
  body.findIdx? (isLabel l)

namespace Isa

variable (I : Isa) (body : Lcmd I.Op)

/-- One step. -/
def step (s : State I) : Option (State I) :=
  match body[s.pc]? with
  | none => none
  | some (.Lopn o) =>
    (I.opn o s.regs s.m).map fun rm => ⟨s.pc + 1, rm.1, rm.2⟩
  | some (.Llabel ..) | some .Lalign => some ⟨s.pc + 1, s.regs, s.m⟩
  | some (.Lgoto (_, l)) => (labelIdx body l).map fun j => ⟨j, s.regs, s.m⟩
  | some (.Lcond c l) =>
    (I.cond c s.regs s.m).bind fun b =>
      if b then (labelIdx body l).map fun j => ⟨j, s.regs, s.m⟩ else some ⟨s.pc + 1, s.regs, s.m⟩
  | some (.Lcall (some r) (_, l)) =>
    (labelIdx body l).map fun j => ⟨j, updReg s.regs r (BitVec.ofNat 64 (s.pc + 1)), s.m⟩
  | some (.Ligoto (.reg r)) => some ⟨(s.regs r).toNat, s.regs, s.m⟩
  | some .Lret => some ⟨body.length + 1, s.regs, s.m⟩
  | some _ => none

/-- No instruction at the counter. -/
def halted (s : State I) : Prop := body[s.pc]? = none

instance (s : State I) : Decidable (I.halted body s) := inferInstanceAs (Decidable (_ = none))

/-- Some number of steps from `s` ends in a state satisfying `Q`: the generic `Reaches` of
    `step`. -/
abbrev Reaches (Q : State I → Prop) (s : State I) : Prop := Ascent.Reaches (I.step body) Q s

/-- The run from `s` halts in a state satisfying `Q`. -/
abbrev Halts (Q : State I → Prop) (s : State I) : Prop :=
  I.Reaches body (fun t => I.halted body t ∧ Q t) s

theorem not_halted_of_step {s s' : State I} (hs : I.step body s = some s') : ¬ I.halted body s := by
  intro hh
  simp only [halted] at hh
  simp [Isa.step, hh] at hs

theorem Halts.halt {Q : State I → Prop} {s : State I} (hh : I.halted body s) (hQ : Q s) :
    I.Halts body Q s :=
  Ascent.Reaches.done ⟨hh, hQ⟩

end Isa

end MachineChecked.Lprog
