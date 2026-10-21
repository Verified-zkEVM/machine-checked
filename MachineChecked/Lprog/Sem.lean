/-
  MachineChecked.Lprog.Sem

  The semantics of an Lprog body under an instruction set, and the ascent's correspondence
  over it, `CorresIsa`: catcrypt-compiler's `CorresIsa` (`Ascent/CorresIsa.lean`, `69ffea9f`;
  MIT, see `MachineChecked/Ascent/LICENSE-catcrypt`) over a semantics written here.

  catcrypt-compiler runs Lprog over a state fixed by its x86 back end: named word arrays and
  the flags `zf`/`cf`/`of`. Here an instruction set `Isa` chooses its operation type `Op` and
  the state `M` beside the registers (memory, flags, anything else), and gives the meaning of
  an operation and of a condition. Control flow is shared by every instruction set:
  `Llabel`/`Lalign` fall through, `Lgoto` and a taken `Lcond` jump to their label, `Lcall` with
  a link register jumps and stores the index after it, `Ligoto` jumps to the index a register
  holds, and `Lret` leaves the body (to the index past its end, so that a return and running
  off the end halt in different states). A run halts when no instruction is at the counter.
-/

import MachineChecked.Lprog.Syntax
import MachineChecked.Ascent.Corres

namespace MachineChecked.Lprog

open MachineChecked.Ascent

/-- An instruction set for Lprog: operations, the state beside the registers, and the meaning
    of operations and conditions. -/
structure Isa where
  /-- The operations of `Lopn`. -/
  Op : Type
  /-- The machine state beside the registers. -/
  M : Type
  /-- An operation on registers and state; `none` is a fault. -/
  opn : List LOperand → Op → List LOperand → (String → BitVec 64) → M →
    Option ((String → BitVec 64) × M)
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
  | some (.Lopn d o src) =>
    (I.opn d o src s.regs s.m).map fun rm => ⟨s.pc + 1, rm.1, rm.2⟩
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

/-- A run with fuel: a halted state, or a step and the rest of the run. -/
def run : Nat → State I → Option (State I)
  | n, s =>
    if I.halted body s then some s
    else match n with
      | 0 => none
      | n + 1 => (I.step body s).bind (run n)

theorem run_halt {n : Nat} {s : State I} (h : I.halted body s) : I.run body n s = some s := by
  cases n <;> simp [run, h]

theorem run_succ {n : Nat} {s : State I} (h : ¬ I.halted body s) :
    I.run body (n + 1) s = (I.step body s).bind (I.run body n) := by
  simp [run, h]

/-- A successful run halts. -/
theorem run_halted : ∀ (n : Nat) (s t : State I), I.run body n s = some t → I.halted body t := by
  intro n
  induction n with
  | zero =>
    intro s t h
    by_cases hs : I.halted body s
    · rw [run_halt I body hs] at h; cases h; exact hs
    · simp [run, hs] at h
  | succ n ih =>
    intro s t h
    by_cases hs : I.halted body s
    · rw [run_halt I body hs] at h; cases h; exact hs
    · rw [run_succ I body hs] at h
      cases hstep : I.step body s with
      | none => rw [hstep] at h; cases h
      | some s' => rw [hstep] at h; exact ih s' t h

/-- More fuel gives the same result. -/
theorem run_add : ∀ (n k : Nat) (s t : State I), I.run body n s = some t →
    I.run body (n + k) s = some t := by
  intro n
  induction n with
  | zero =>
    intro k s t h
    by_cases hs : I.halted body s
    · rw [run_halt I body hs] at h ⊢; exact h
    · simp [run, hs] at h
  | succ n ih =>
    intro k s t h
    by_cases hs : I.halted body s
    · rw [run_halt I body hs] at h ⊢; exact h
    · rw [run_succ I body hs] at h
      rw [show n + 1 + k = (n + k) + 1 by omega, run_succ I body hs]
      cases hstep : I.step body s with
      | none => rw [hstep] at h; cases h
      | some s' => rw [hstep] at h; exact ih k s' t h

/-- Exactly `n` steps. -/
def steps : Nat → State I → Option (State I)
  | 0, s => some s
  | n + 1, s => (I.step body s).bind (steps n)

/-- Some number of steps from `s` ends in a state satisfying `Q`. -/
def Reaches (Q : State I → Prop) (s : State I) : Prop := ∃ n t, I.steps body n s = some t ∧ Q t

/-- The run from `s` halts in a state satisfying `Q`. -/
def Halts (Q : State I → Prop) (s : State I) : Prop := I.Reaches body (fun t => I.halted body t ∧ Q t) s

theorem not_halted_of_step {s s' : State I} (hs : I.step body s = some s') : ¬ I.halted body s := by
  intro hh
  simp only [halted] at hh
  simp [Isa.step, hh] at hs

/-- Steps that end halted are a run. -/
theorem run_of_steps : ∀ (n : Nat) (s t : State I), I.steps body n s = some t → I.halted body t →
    I.run body n s = some t := by
  intro n
  induction n with
  | zero => intro s t h ht; cases h; exact run_halt I body ht
  | succ n ih =>
    intro s t h ht
    simp only [steps] at h
    cases hstep : I.step body s with
    | none => rw [hstep] at h; cases h
    | some s' =>
      rw [hstep, Option.bind_some] at h
      rw [run_succ I body (I.not_halted_of_step body hstep), hstep, Option.bind_some]
      exact ih s' t h ht

namespace Reaches

variable {I body} {Q : State I → Prop}

theorem done {s : State I} (hQ : Q s) : I.Reaches body Q s := ⟨0, s, rfl, hQ⟩

theorem step {s s' : State I} (hs : I.step body s = some s') (h : I.Reaches body Q s') :
    I.Reaches body Q s := by
  obtain ⟨n, t, hn, hQ⟩ := h
  exact ⟨n + 1, t, by simp only [steps, hs, Option.bind_some]; exact hn, hQ⟩

theorem mono {R : State I → Prop} {s : State I} (h : I.Reaches body Q s) (hQR : ∀ t, Q t → R t) :
    I.Reaches body R s := by
  obtain ⟨n, t, hn, hQ⟩ := h
  exact ⟨n, t, hn, hQR t hQ⟩

end Reaches

theorem Halts.halt {Q : State I → Prop} {s : State I} (hh : I.halted body s) (hQ : Q s) :
    I.Halts body Q s :=
  Reaches.done ⟨hh, hQ⟩

end Isa

/-- **The correspondence over an instruction set** (`CorresIsa` of catcrypt-compiler): from a
    state related by `SR` to an abstract state satisfying `Pre`, the run of `body` with `fuel`
    steps halts in a state related to `fa a`. -/
def CorresIsa {AState : Type} (I : Isa) (body : Lcmd I.Op) (SR : State I → AState → Prop)
    (Pre : AState → Prop) (fa : AState → AState) (fuel : Nat) : Prop :=
  CorresM (I.run body) SR Pre fa fuel

section CorresIsa

variable {AState : Type} {I : Isa} {body : Lcmd I.Op} {SR : State I → AState → Prop}
  {Pre : AState → Prop} {fa : AState → AState}

/-- The correspondence at a fuel holds at every larger fuel. -/
theorem CorresIsa.fuel_mono {n n' : Nat} (h : CorresIsa I body SR Pre fa n) (hle : n ≤ n') :
    CorresIsa I body SR Pre fa n' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  intro m a hSR hP
  obtain ⟨m', hrun, hSR'⟩ := h m a hSR hP
  exact ⟨m', I.run_add body n k m m' hrun, hSR'⟩

/-- `CorresIsa` as the family of step triples over all postconditions. -/
theorem CorresIsa.iff_post {fuel : Nat} :
    CorresIsa I body SR Pre fa fuel ↔ ∀ Q : State I → Prop,
      StepTriple (I.run body) (fun m => ∃ a, SR m a ∧ Pre a ∧ ∀ m', SR m' (fa a) → Q m') fuel Q :=
  corresM_iff_post

end CorresIsa

end MachineChecked.Lprog
