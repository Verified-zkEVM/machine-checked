/-
  MachineChecked.Ascent.Refine

  When two programs are the same to an observer.

  A system is a step relation with events and its accepting states. An observer sees the
  events a run makes and how it ends: still running, accepting, trapped, or `wrong`. One
  system refines another when everything it shows, the other shows too; two are equivalent
  when each refines the other. `wrong` is undefined behaviour of the one refined: once it can
  go `wrong`, having made a prefix of the events, anything refines it.

  This is the equivalence of a decompiler and a compiler (`docs/design/Decompiler.md`): the
  same events, and the same end. Registers and memory are compared only through the events
  they reach.

  ## Main definitions

  * `System`, `Steps`, `End`, `Behaves`
  * `Refines`, `Equivalent`

  ## Main results

  * `Refines.of_sim`: a simulation gives a refinement
  * `Refines.refl`, `Equivalent.symm`
-/

import MachineChecked.Ascent.Safe

namespace MachineChecked.Ascent

/-- A system: a step relation with events of type `E`, and its accepting states. -/
structure System (σ E : Type) where
  step : σ → Outcome (σ × List E) → Prop
  accept : σ → Prop

variable {σ τ υ E : Type}

/-- The system that stops where `P` holds, and accepts there. -/
def System.stopAt (A : System σ E) (P : σ → Prop) : System σ E where
  step s o := ¬ P s ∧ A.step s o
  accept s := A.accept s ∨ P s

/-- Some number of steps from `s` to `t`, making the events `tr`. -/
inductive Steps (A : System σ E) : σ → List E → σ → Prop
  | refl (s : σ) : Steps A s [] s
  | step {s t u : σ} {es tr : List E} : A.step s (.ok (t, es)) → Steps A t tr u →
      Steps A s (es ++ tr) u

theorem Steps.one {A : System σ E} {s t : σ} {es : List E} (h : A.step s (.ok (t, es))) :
    Steps A s es t := by
  simpa using Steps.step h (.refl t)

theorem Steps.trans {A : System σ E} {s t u : σ} {tr tr' : List E} (h : Steps A s tr t)
    (h' : Steps A t tr' u) : Steps A s (tr ++ tr') u := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => rw [List.append_assoc]; exact .step hs (ih h')

/-- How a run is seen to end. -/
inductive End where
  /-- Not ended: the observer stopped looking. -/
  | running
  | accepted
  | trapped
  | wrong
  deriving DecidableEq, Repr

/-- `Behaves A s tr e`: a run of `A` from `s` makes the events `tr` and is seen to end in
    `e`. A state that accepts is seen to accept, not to trap. -/
inductive Behaves (A : System σ E) : σ → List E → End → Prop
  | running (s : σ) : Behaves A s [] .running
  | accepted {s : σ} : A.accept s → Behaves A s [] .accepted
  | trapped {s : σ} : ¬ A.accept s → A.step s .trap → Behaves A s [] .trapped
  | wrong {s : σ} : A.step s .wrong → Behaves A s [] .wrong
  | step {s t : σ} {es tr : List E} {e : End} : A.step s (.ok (t, es)) → Behaves A t tr e →
      Behaves A s (es ++ tr) e

theorem Behaves.of_steps {A : System σ E} {s t : σ} {tr tr' : List E} {e : End}
    (h : Steps A s tr t) (h' : Behaves A t tr' e) : Behaves A s (tr ++ tr') e := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => rw [List.append_assoc]; exact .step hs (ih h')

/-- A run that is seen to go `wrong` is some steps and then a step to `wrong`. -/
theorem Behaves.wrong_iff {A : System σ E} {s : σ} {tr : List E} :
    Behaves A s tr .wrong ↔ ∃ t, Steps A s tr t ∧ A.step t .wrong := by
  constructor
  · intro h
    generalize he : End.wrong = e at h
    induction h with
    | running | accepted | trapped => cases he
    | wrong hw => exact ⟨_, .refl _, hw⟩
    | step hs _ ih =>
      obtain ⟨t, hst, hw⟩ := ih he
      exact ⟨t, .step hs hst, hw⟩
  · rintro ⟨t, hst, hw⟩
    simpa using Behaves.of_steps hst (.wrong hw)

/-- `A` can go `wrong` from `s` having made a prefix of `tr`. -/
def GoesWrong (A : System σ E) (s : σ) (tr : List E) : Prop :=
  ∃ tr', tr' <+: tr ∧ Behaves A s tr' .wrong

/-- What `A` shows from `s` for the events `tr` and the end `e`: a run that makes exactly
    `tr` and ends in `e`, or, for a run still going, one that makes at least `tr`. -/
def Shows (A : System σ E) (s : σ) (tr : List E) : End → Prop
  | .running => ∃ tr', tr <+: tr' ∧ Behaves A s tr' .running
  | e => Behaves A s tr e

theorem Shows.of_behaves {A : System σ E} {s : σ} {tr : List E} {e : End} (h : Behaves A s tr e) :
    Shows A s tr e := by
  cases e
  case running => exact ⟨tr, List.prefix_refl _, h⟩
  all_goals exact h

theorem GoesWrong.of_steps {A : System σ E} {s t : σ} {tr tr' : List E} (h : Steps A s tr t)
    (h' : GoesWrong A t tr') : GoesWrong A s (tr ++ tr') := by
  obtain ⟨tr₁, hp, hb⟩ := h'
  exact ⟨tr ++ tr₁, (List.prefix_append_right_inj tr).2 hp, hb.of_steps h⟩

theorem GoesWrong.mono {A : System σ E} {s : σ} {tr tr' : List E} (h : GoesWrong A s tr)
    (hp : tr <+: tr') : GoesWrong A s tr' := by
  obtain ⟨tr₁, hp₁, hb⟩ := h
  exact ⟨tr₁, hp₁.trans hp, hb⟩

theorem Shows.of_steps {A : System σ E} {s t : σ} {tr tr' : List E} {e : End}
    (h : Steps A s tr t) (h' : Shows A t tr' e) : Shows A s (tr ++ tr') e := by
  cases e
  case running =>
    obtain ⟨tr₁, hp, hb⟩ := h'
    exact ⟨tr ++ tr₁, (List.prefix_append_right_inj tr).2 hp, hb.of_steps h⟩
  all_goals exact Behaves.of_steps h h'

/-- **Refinement.** Everything `A` shows from `a`, `B` shows from `b`, unless `B` can go
    `wrong` on the way. -/
def Refines (A : System σ E) (a : σ) (B : System τ E) (b : τ) : Prop :=
  ∀ tr e, Behaves A a tr e → GoesWrong B b tr ∨ Shows B b tr e

/-- **Equivalence**: each refines the other. -/
def Equivalent (A : System σ E) (a : σ) (B : System τ E) (b : τ) : Prop :=
  Refines A a B b ∧ Refines B b A a

theorem Equivalent.symm {A : System σ E} {a : σ} {B : System τ E} {b : τ}
    (h : Equivalent A a B b) : Equivalent B b A a :=
  ⟨h.2, h.1⟩

theorem Refines.refl (A : System σ E) (a : σ) : Refines A a A a :=
  fun _ _ h => .inr (.of_behaves h)

/-- **A simulation gives a refinement.** `S` relates states of `A` to states of `B`. Each
    step of `A` from a related state is matched by steps of `B` making the same events, to a
    related state; where `A` accepts, traps or goes `wrong`, `B` does after steps that make no
    events. At each point `B` may go `wrong` instead. -/
theorem Refines.of_sim {A : System σ E} {B : System τ E} (S : σ → τ → Prop)
    (hacc : ∀ a b, S a b → A.accept a →
      GoesWrong B b [] ∨ ∃ b', Steps B b [] b' ∧ B.accept b')
    (hstep : ∀ a b a' es, S a b → A.step a (.ok (a', es)) →
      GoesWrong B b es ∨ ∃ b', Steps B b es b' ∧ S a' b')
    (htrap : ∀ a b, S a b → ¬ A.accept a → A.step a .trap →
      GoesWrong B b [] ∨ ∃ b', Steps B b [] b' ∧ ¬ B.accept b' ∧ B.step b' .trap)
    (hwrong : ∀ a b, S a b → A.step a .wrong → GoesWrong B b [])
    {a : σ} {b : τ} (h : S a b) : Refines A a B b := by
  intro tr e hb
  induction hb generalizing b with
  | running s => exact .inr ⟨[], List.prefix_refl _, .running b⟩
  | accepted ha =>
    rcases hacc _ _ h ha with hw | ⟨b', hs, hb'⟩
    · exact .inl hw
    · exact .inr (.of_behaves (by simpa using Behaves.of_steps hs (.accepted hb')))
  | trapped hna ht =>
    rcases htrap _ _ h hna ht with hw | ⟨b', hs, hnb, hb'⟩
    · exact .inl hw
    · exact .inr (.of_behaves (by simpa using Behaves.of_steps hs (.trapped hnb hb')))
  | wrong hw => exact .inl (hwrong _ _ h hw)
  | step hs _ ih =>
    rcases hstep _ _ _ _ h hs with hw | ⟨b', hsteps, h'⟩
    · exact .inl (hw.mono (List.prefix_append _ _))
    · rcases ih h' with hw | hsh
      · exact .inl (hw.of_steps hsteps)
      · exact .inr (hsh.of_steps hsteps)

end MachineChecked.Ascent
