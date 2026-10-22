/-
  MachineChecked.Ascent.Safe

  The judgement every result is stated in, for any machine.

  A machine is a step relation `step : σ → Outcome σ → Prop`: from a state, a step ends in a
  state (`ok`), in a stop that proves nothing (`trap`: the machine is stuck, a fault, a
  refused access), or in `wrong`, a violated assumption (for a lifted program: a bad return
  address, an indirect target off its list). A relation, so that a step may have many
  results (an external call). A deterministic partial step function is one (`detStep`).

  `SafeN step accept G n Q s`: every run from `s` of fewer than `n` steps, every state of
  which satisfies the guard `G`, never ends in `wrong`, and ends only in accepting states that
  satisfy `Q`. Partial correctness: a run that traps or diverges is safe. Contracts are stated
  in continuation form,

      ∀ G n Q s, Pre s → (∀ t, Post s t → SafeN … G n Q t) → SafeN … G n Q s,

  and compose by application; a callee used at a smaller budget than its caller makes
  recursion compose (`budget_induction`). RISC-V's judgement (`MachineChecked.RiscV.SafeN`)
  is the instance at riscv-zkvm's `stepSp1` with a constant `Q`; the low logical program's is
  the instance at its step relation, where `Q` also says what a function returning to code
  outside the program leaves behind.

  ## Main definitions

  * `Outcome`, `detStep`, `Run`, `SafeN`, `Good`

  ## Main results

  * `SafeN.zero`, `mono`, `assume`, `imp`, `of_true`: the structural rules
  * `SafeN.intro`, `stuck`, `of_step`, `step`: a step, and a stuck state
  * `SafeN.next`, `not_wrong`, `of_accept`: what a judgement says about the first step
  * `loop`, `loop_measure`, `budget_induction`: induction principles for continuation-form
    judgements, stated for any predicate
-/

import MachineChecked.Ascent.Run

namespace MachineChecked.Ascent

/-- How a step ends: in a state, in a trap (safe), or in `wrong` (unsafe). -/
inductive Outcome (σ : Type) where
  | ok (s : σ)
  | trap
  | wrong

variable {σ : Type}

/-- A deterministic partial step function as a step relation: a step to its result, or a
    trap where it has none. It never goes `wrong`. -/
def detStep (f : σ → Option σ) (s : σ) (o : Outcome σ) : Prop :=
  match f s with
  | some t => o = .ok t
  | none => o = .trap

theorem detStep_of_some {f : σ → Option σ} {s t : σ} (h : f s = some t) {o : Outcome σ} :
    detStep f s o ↔ o = .ok t := by
  simp [detStep, h]

theorem detStep_of_none {f : σ → Option σ} {s : σ} (h : f s = none) {o : Outcome σ} :
    detStep f s o ↔ o = .trap := by
  simp [detStep, h]

theorem detStep_ne_wrong {f : σ → Option σ} {s : σ} : ¬ detStep f s .wrong := by
  unfold detStep; split <;> simp

/-- A run of exactly `m` steps from `s` ending in `o`, every state of which satisfies `G`. -/
inductive Run (step : σ → Outcome σ → Prop) (G : σ → Prop) : Nat → σ → Outcome σ → Prop
  | done {s : σ} : G s → Run step G 0 s (.ok s)
  | next {n : Nat} {s t : σ} {o : Outcome σ} : G s → step s (.ok t) → Run step G n t o →
      Run step G (n + 1) s o
  | trap {s : σ} : G s → step s .trap → Run step G 1 s .trap
  | wrong {s : σ} : G s → step s .wrong → Run step G 1 s .wrong

theorem Run.guard {step : σ → Outcome σ → Prop} {G : σ → Prop} {m : Nat} {s : σ}
    {o : Outcome σ} (h : Run step G m s o) : G s := by
  cases h <;> assumption

/-- A run of a machine that never goes `wrong` does not end in `wrong`. -/
theorem Run.ne_wrong {step : σ → Outcome σ → Prop} {G : σ → Prop}
    (hw : ∀ s, ¬ step s .wrong) {m : Nat} {s : σ} {o : Outcome σ} (h : Run step G m s o) :
    o ≠ .wrong := by
  induction h with
  | done => nofun
  | next _ _ _ ih => exact ih
  | trap => nofun
  | wrong _ hs => exact absurd hs (hw _)

/-- What a run may end in: not `wrong`, and an accepting state only if it satisfies `Q`. -/
def Good (accept : σ → Prop) (Q : σ → Prop) : Outcome σ → Prop
  | .ok t => accept t → Q t
  | .trap => True
  | .wrong => False

/-- **The judgement.** Every run from `s` of fewer than `n` steps along which `G` holds ends
    `Good`: never `wrong`, and accepting only in a state satisfying `Q`. -/
def SafeN (step : σ → Outcome σ → Prop) (accept : σ → Prop) (G : σ → Prop) (n : Nat)
    (Q : σ → Prop) (s : σ) : Prop :=
  ∀ m < n, ∀ o, Run step G m s o → Good accept Q o

namespace SafeN

variable {R : σ → Outcome σ → Prop} {accept : σ → Prop} {G : σ → Prop} {Q : σ → Prop}

theorem zero {s : σ} : SafeN R accept G 0 Q s :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem mono {s : σ} {k n : Nat} (hk : k ≤ n) (h : SafeN R accept G n Q s) :
    SafeN R accept G k Q s :=
  fun m hm => h m (Nat.lt_of_lt_of_le hm hk)

/-- The guard holds at the current state of every run it constrains. -/
theorem assume {s : σ} {n : Nat} (h : G s → SafeN R accept G n Q s) :
    SafeN R accept G n Q s :=
  fun m hm o hr => h hr.guard m hm o hr

/-- Monotonicity in `Q`. -/
theorem imp {Q' : σ → Prop} {s : σ} {n : Nat} (h : SafeN R accept G n Q s)
    (hq : ∀ t, accept t → Q t → Q' t) : SafeN R accept G n Q' s := by
  intro m hm o hr
  have := h m hm o hr
  cases o with
  | ok t => exact fun ha => hq t ha (this ha)
  | trap => trivial
  | wrong => exact this

/-- A machine that never goes `wrong` is safe from anywhere for a `Q` that always holds. -/
theorem of_true (hw : ∀ s, ¬ R s .wrong) (hq : ∀ t, Q t) {n : Nat} (s : σ) :
    SafeN R accept G n Q s := by
  intro m _ o hr
  cases o with
  | ok t => exact fun _ => hq t
  | trap => trivial
  | wrong => exact Run.ne_wrong hw hr rfl

/-- **One step.** A state is safe for `n + 1` steps if it satisfies `Q` when it accepts, and every
    result of its step is safe: not `wrong`, and every successor safe for `n`. -/
theorem intro {s : σ} {n : Nat} (hacc : accept s → Q s)
    (h : ∀ o, R s o → match o with
      | .ok t => SafeN R accept G n Q t
      | .trap => True
      | .wrong => False) :
    SafeN R accept G (n + 1) Q s := by
  intro m hm o hr
  cases hr with
  | done _ => exact hacc
  | next _ hs hr' => exact h _ hs _ (by omega) _ hr'
  | trap _ _ => trivial
  | wrong _ hs => exact h _ hs

/-- A stuck state: every result of its step is a trap. Safe unless it accepts. -/
theorem stuck {s : σ} {n : Nat} (hs : ∀ o, R s o → o = .trap) (hacc : accept s → Q s) :
    SafeN R accept G n Q s := by
  intro m _ o hr
  cases hr with
  | done _ => exact hacc
  | next _ h _ => cases hs _ h
  | trap _ _ => trivial
  | wrong _ h => cases hs _ h

/-- A step with one result, from a state that does not accept: one budget unit is spent. -/
theorem step {s t : σ} {n : Nat} (hna : ¬ accept s) (hs : ∀ o, R s o → o = .ok t)
    (ht : SafeN R accept G n Q t) : SafeN R accept G (n + 1) Q s :=
  intro (fun ha => absurd ha hna) fun o ho => by
    obtain rfl := hs o ho
    exact ht

/-- A step with one result does not need budget: `SafeN n` passes back along it. -/
theorem of_step {s t : σ} {n : Nat} (hna : ¬ accept s) (hs : ∀ o, R s o → o = .ok t)
    (ht : SafeN R accept G n Q t) : SafeN R accept G n Q s :=
  mono (Nat.le_succ n) (step hna hs ht)

/-- A successor of a state safe for `n + 1` steps is safe for `n`. -/
theorem next {s t : σ} {n : Nat} (hg : G s) (hs : R s (.ok t)) (h : SafeN R accept G (n + 1) Q s) :
    SafeN R accept G n Q t :=
  fun m hm o hr => h (m + 1) (by omega) o (.next hg hs hr)

/-- A state safe for a step does not step to `wrong`. -/
theorem not_wrong {s : σ} {n : Nat} (hg : G s) (hs : R s .wrong) (h : SafeN R accept G (n + 2) Q s) :
    False :=
  h 1 (by omega) .wrong (.wrong hg hs)

/-- An accepting state safe for a step satisfies `Q`. -/
theorem of_accept {s : σ} {n : Nat} (hg : G s) (ha : accept s) (h : SafeN R accept G (n + 1) Q s) :
    Q s :=
  h 0 (by omega) (.ok s) (.done hg) ha

/-- On a deterministic machine whose accepting states are stuck, `SafeN` passes back along a
    run that reaches states it holds in. -/
theorem of_reaches {f : σ → Option σ} (hacc : ∀ s, accept s → f s = none) {P : σ → Prop}
    {s : σ} {n : Nat} (h : Reaches f P s) (hk : ∀ t, P t → SafeN (detStep f) accept G n Q t) :
    SafeN (detStep f) accept G n Q s := by
  obtain ⟨k, t, hk', ht⟩ := h
  induction k generalizing s with
  | zero => cases hk'; exact hk t ht
  | succ k ih =>
    rw [steps_succ] at hk'
    cases hs : f s with
    | none => rw [hs] at hk'; cases hk'
    | some s₁ =>
      rw [hs, Option.bind_some] at hk'
      exact of_step (fun ha => by rw [hacc s ha] at hs; cases hs)
        (fun _ => (detStep_of_some hs).1) (ih hk')

end SafeN

/-! ## Induction principles

These hold for any predicate, and so for every continuation-form judgement. -/

/-- **A loop** of `N` iterations: each takes `Inv i` to `Inv (i + 1)` in continuation form
    (so an iteration may also leave by another way), and `Inv N` hands over to the code after
    the loop. -/
theorem loop {S : σ → Prop} (Inv : Nat → σ → Prop) (N : Nat)
    (hbody : ∀ i, i < N → ∀ s, Inv i s → (∀ t, Inv (i + 1) t → S t) → S s)
    (hN : ∀ s, Inv N s → S s) : ∀ s, Inv 0 s → S s := by
  have : ∀ j, j ≤ N → ∀ s, Inv (N - j) s → S s := by
    intro j
    induction j with
    | zero => intro _ s hs; simpa using hN s hs
    | succ j ih =>
      intro hj s hs
      have hlt : N - (j + 1) < N := by omega
      refine hbody _ hlt s hs ?_
      intro t ht
      have : N - (j + 1) + 1 = N - j := by omega
      exact ih (by omega) t (this ▸ ht)
  intro s hs
  exact this N (Nat.le_refl N) s (by simpa using hs)

/-- **A loop with a measure** that decreases on every iteration that does not leave. -/
theorem loop_measure {S : σ → Prop} (Inv : σ → Prop) (μ : σ → Nat)
    (hbody : ∀ s, Inv s → (∀ t, Inv t → μ t < μ s → S t) → S s) :
    ∀ s, Inv s → S s := by
  have : ∀ m s, μ s ≤ m → Inv s → S s := by
    intro m
    induction m with
    | zero =>
      intro s hμ hs
      exact hbody s hs (fun t _ hlt => absurd hlt (by omega))
    | succ m ih =>
      intro s hμ hs
      exact hbody s hs (fun t ht hlt => ih t (by omega) ht)
  intro s hs
  exact this _ s (Nat.le_refl _) hs

/-- **Composition of a table of contracts.** If each contract holds at a budget assuming every
    contract of the table holds at every smaller budget, every contract holds at every budget.
    This is how mutually recursive functions compose: a callee is used at a smaller budget
    than its caller. -/
theorem budget_induction {ι : Type} (H : ι → Nat → Prop)
    (h : ∀ i n, (∀ j, ∀ m < n, H j m) → H i n) : ∀ i n, H i n := by
  intro i n
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih => exact h i n fun j m hm => ih m hm j

end MachineChecked.Ascent
