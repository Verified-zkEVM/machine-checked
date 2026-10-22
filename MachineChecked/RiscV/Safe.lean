/-
  MachineChecked.RiscV.Safe

  The judgement every proof in this framework is written in.

  `SafeN G n P s`: every accepting state reached from `s` in fewer than `n` steps, along a
  run every state of which satisfies the guard `G`, satisfies `P`. Partial correctness: a
  run that traps, rejects or diverges is safe. Accepting is SP1's `HALT` with exit code `0`
  (`Accepted`), and an accepting state is stuck, so a state that steps is never accepting
  and a step never has to be checked for acceptance. The guard is where premises about runs
  go (the checker's `Env.Cfi`: the targets of the indirect jumps no analysis resolves);
  with `G = fun _ => True` it is plain safety.

  A function specification is in continuation form, with one budget on both sides:

      ∀ G n P s, s.pc = entry → Pre s → (∀ t, Post s t → SafeN G n P t) → SafeN G n P s

  "if the caller is safe for `n` steps from every state the function can return in, it is
  safe for `n` steps from the call". The form composes by application, covers the paths on
  which the function does not return at all (a panic inside it discharges `SafeN` there and
  then), and quantifies over `P`, so one proof serves every caller. A step never lowers the
  budget a proof needs (`SafeN.of_step`), so a symbolic execution carries `n` through
  unchanged; the checker's soundness uses a callee's specification at a smaller budget than
  its own, which is what makes recursion and loops compose. Proved for every `n`, a
  specification gives the unbounded `Safe`.
-/

import MachineChecked.RiscV.Accept
import MachineChecked.Ascent.Run
import MachineChecked.Ascent.Safe
import MachineChecked.RiscV.State

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64

/-! ## Runs -/

/-- `n` steps of the SP1 backend: the generic run (`Ascent.steps`) of `stepSp1`. -/
abbrev stepsSp1 : Nat → MachineState → Option MachineState := Ascent.steps stepSp1

@[simp] theorem stepsSp1_zero (s : MachineState) : stepsSp1 0 s = some s := rfl

theorem stepsSp1_succ' (n : Nat) (s : MachineState) :
    stepsSp1 (n + 1) s = (stepSp1 s).bind (stepsSp1 n) := rfl

theorem stepsSp1_succ {n : Nat} {s s' : MachineState} (h : stepsSp1 (n + 1) s = some s') :
    ∃ s1, stepSp1 s = some s1 ∧ stepsSp1 n s1 = some s' := by
  simpa [stepsSp1_succ', Option.bind_eq_some_iff] using h

theorem stepsSp1_succ_of_step {n : Nat} {s s₁ : MachineState} (h : stepSp1 s = some s₁) :
    stepsSp1 (n + 1) s = stepsSp1 n s₁ :=
  Ascent.steps_succ_of_step h

theorem stepsSp1_add (m n : Nat) (s : MachineState) :
    stepsSp1 (m + n) s = (stepsSp1 m s).bind (stepsSp1 n) :=
  Ascent.steps_add m n s

/-- A stuck state ends the run where it is. -/
theorem stepsSp1_of_stuck {s s' : MachineState} {k : Nat} (hstuck : stepSp1 s = none)
    (h : stepsSp1 k s = some s') : k = 0 ∧ s' = s := by
  cases k with
  | zero => simp at h; exact ⟨rfl, h.symm⟩
  | succ k => rw [stepsSp1_succ', hstuck] at h; exact absurd h (by simp)

/-- A state that steps is not accepting. -/
theorem not_accepted_of_step {s t : MachineState} (h : stepSp1 s = some t) : ¬ Accepted s :=
  fun ha => by rw [Accepted.stuck ha] at h; cases h

/-! ## The judgement -/

/-- The generic judgement (`Ascent.SafeN`) at `stepSp1`, which never goes `wrong`, with
    `Accepted` as the accepting states. -/
def SafeN (G : MachineState → Prop) (n : Nat) (P : Prop) (s : MachineState) : Prop :=
  Ascent.SafeN (Ascent.detStep stepSp1) Accepted G n P s

def Safe (G : MachineState → Prop) (P : Prop) (s : MachineState) : Prop := ∀ n, SafeN G n P s

namespace SafeN

variable {G : MachineState → Prop}

theorem zero {P : Prop} {s : MachineState} : SafeN G 0 P s :=
  Ascent.SafeN.zero

theorem mono {P : Prop} {s : MachineState} {k n : Nat} (hk : k ≤ n) (h : SafeN G n P s) :
    SafeN G k P s := Ascent.SafeN.mono hk h

/-- A step from a state that does not accept: one budget unit is spent. -/
theorem step {P : Prop} {s t : MachineState} {n : Nat} (hna : ¬ Accepted s)
    (hs : stepSp1 s = some t) (ht : SafeN G n P t) : SafeN G (n + 1) P s :=
  Ascent.SafeN.step hna (fun _ => (Ascent.detStep_of_some hs).1) ht

/-- A step does not need budget: `SafeN n` passes back along it. -/
theorem of_step {P : Prop} {s t : MachineState} {n : Nat} (hna : ¬ Accepted s)
    (hs : stepSp1 s = some t) (ht : SafeN G n P t) : SafeN G n P s :=
  mono (Nat.le_succ n) (step hna hs ht)

/-- A state with no step: safe unless it accepts. -/
theorem stuck {P : Prop} {s : MachineState} {n : Nat} (hs : stepSp1 s = none)
    (hp : Accepted s → P) : SafeN G n P s :=
  Ascent.SafeN.stuck (fun _ => (Ascent.detStep_of_none hs).1) hp

/-- From a state that does not accept, safe for `n + 1` steps if every successor is safe
    for `n`. -/
theorem intro {P : Prop} {s : MachineState} {n : Nat} (hna : ¬ Accepted s)
    (h : ∀ t, stepSp1 s = some t → SafeN G n P t) : SafeN G (n + 1) P s := by
  cases hs : stepSp1 s with
  | none => exact stuck hs (fun ha => absurd ha hna)
  | some t => exact step hna hs (h t hs)

/-- The guard holds at the current state of every run it constrains. -/
theorem assume {P : Prop} {s : MachineState} {n : Nat} (h : G s → SafeN G n P s) :
    SafeN G n P s :=
  Ascent.SafeN.assume h

/-! ### The symbolic executor's forms

A step is given by its equation `stepSp1 s = some t`, which already says `s` does not
accept. The executor never states a successor state by hand: it hands `step_gen` a
continuation `∀ s', t = s' → SafeN G n P s'` and then introduces `s'`. -/

/-- A step: safety is inherited from the successor, at the same budget. -/
theorem step_of {P : Prop} {s t : MachineState} {n : Nat} (hs : stepSp1 s = some t)
    (ht : SafeN G n P t) : SafeN G n P s :=
  of_step (not_accepted_of_step hs) hs ht

/-- A step, with the successor given by an equation. -/
theorem step_eq {P : Prop} {s t t' : MachineState} {n : Nat} (hs : stepSp1 s = some t)
    (heq : t = t') (ht : SafeN G n P t') : SafeN G n P s :=
  step_of (heq ▸ hs) ht

theorem step_gen {P : Prop} {s t : MachineState} {n : Nat} (hs : stepSp1 s = some t)
    (k : ∀ s', t = s' → SafeN G n P s') : SafeN G n P s :=
  step_of hs (k t rfl)

/-- Many steps. -/
theorem steps {P : Prop} {s t : MachineState} {n k : Nat} (h : stepsSp1 k s = some t)
    (ht : SafeN G n P t) : SafeN G n P s := by
  induction k generalizing s with
  | zero => simp at h; subst h; exact ht
  | succ k ih =>
    rw [stepsSp1_succ'] at h
    cases hs : stepSp1 s with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some s₁ => rw [hs] at h; exact step_of hs (ih h)

/-- The `HALT` syscall: safe when `a0 = 0` gives `P`. -/
theorem halt {P : Prop} {s : MachineState} {n : Nat} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = 0) (hp : s.getReg .x10 = 0 → P) : SafeN G n P s :=
  stuck (stepSp1_halt hfetch ht0) (fun ha => hp ha.2.2)

/-- A halt with a nonzero exit code is safe for every `P`. -/
theorem reject {P : Prop} {s : MachineState} {n : Nat} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = 0) (ha0 : s.getReg .x10 ≠ 0) : SafeN G n P s :=
  halt hfetch ht0 (fun h => absurd h ha0)

/-- A trap (no instruction at the pc) is safe for every `P`. -/
theorem trap {P : Prop} {s : MachineState} {n : Nat} (h : s.code s.pc = none) : SafeN G n P s :=
  stuck (by simp [stepSp1, h]) (fun ha => absurd (h.symm.trans ha.1) (by simp))

/-- Anything is safe for a true `P`. -/
theorem of_true {P : Prop} {n : Nat} (hp : P) (s : MachineState) : SafeN G n P s :=
  Ascent.SafeN.of_true (fun _ => Ascent.detStep_ne_wrong) hp s

/-- Monotonicity in `P`. -/
theorem imp {P Q : Prop} {s : MachineState} {n : Nat} (h : SafeN G n P s) (hpq : P → Q) :
    SafeN G n Q s :=
  Ascent.SafeN.imp h hpq

/-- Name a value: the executor's way of introducing an atom. -/
theorem gen {P : Prop} {s : MachineState} {n : Nat} {α : Sort _} (e : α)
    (k : ∀ a, e = a → SafeN G n P s) : SafeN G n P s :=
  k e rfl

theorem cases {P : Prop} {s : MachineState} {n : Nat} (c : Prop)
    (h₁ : c → SafeN G n P s) (h₂ : ¬ c → SafeN G n P s) : SafeN G n P s :=
  (Classical.em c).elim h₁ h₂

theorem by_cases {P : Prop} {s : MachineState} {n : Nat} (c : Prop) [Decidable c]
    (h₁ : c → SafeN G n P s) (h₂ : ¬ c → SafeN G n P s) : SafeN G n P s :=
  if hc : c then h₁ hc else h₂ hc

/-! ### Loops

A loop is a family of states `Inv i` indexed by the iteration count. Each body execution
takes `Inv i` to `Inv (i+1)` (in continuation form, so a body may also panic), and `Inv N`
hands over to the code after the loop. The iteration count is the induction; the budget
`n` is untouched. -/

theorem loop {P : Prop} {n : Nat} (Inv : Nat → MachineState → Prop) (N : Nat)
    (hbody : ∀ i, i < N → ∀ s, Inv i s → (∀ t, Inv (i + 1) t → SafeN G n P t) → SafeN G n P s)
    (hN : ∀ s, Inv N s → SafeN G n P s) : ∀ s, Inv 0 s → SafeN G n P s :=
  Ascent.loop Inv N hbody hN

/-- A loop whose iteration count is not known in advance: a measure that decreases on
    every iteration that does not exit. -/
theorem loop_measure {P : Prop} {n : Nat} (Inv : MachineState → Prop) (μ : MachineState → Nat)
    (hbody : ∀ s, Inv s → (∀ t, Inv t → μ t < μ s → SafeN G n P t) → SafeN G n P s) :
    ∀ s, Inv s → SafeN G n P s :=
  Ascent.loop_measure Inv μ hbody

end SafeN

/-- **The bridge for a run.** A run from `s` to states that are all safe for `n` steps makes
    `s` safe for `n` steps. -/
theorem SafeN.of_reaches {G : MachineState → Prop} {n : Nat} {P : Prop} {Q : MachineState → Prop}
    {s : MachineState} (h : Ascent.Reaches stepSp1 Q s) (hk : ∀ t, Q t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨k, t, hk', ht⟩ := h
  exact SafeN.steps hk' (hk t ht)

/-- The unbounded judgement, from the bounded one at every budget. -/
theorem Safe.safeN {G : MachineState → Prop} {P : Prop} {s : MachineState} (h : Safe G P s)
    (n : Nat) : SafeN G n P s := h n

end MachineChecked.RiscV
