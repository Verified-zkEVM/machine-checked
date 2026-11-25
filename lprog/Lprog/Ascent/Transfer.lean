/-
  Lprog.Ascent.Transfer

  **The transfer theorem**, for any two systems: a judgement proved of a program `A` holds of
  the machine that runs it, given a relation between their states along which every machine
  step is matched by steps of `A`.

  This is the part of a lift's correctness that does not depend on the instruction set. An
  instruction set supplies the relations and `back`: from related states, `A` can go `wrong`
  or the machine's step is `Matched`. `S` relates the states of a program still running, `T`
  those where `A` has stopped and the machine goes on (a function that has returned to its
  caller, which `A` does not model), and `U` those where both accept.

  ## Main definitions

  * `AllSafe`: safe along every run, at every budget
  * `Matched`: what the machine does at a state, at the program

  ## Main results

  * `transfer`: `AllSafe` of the program gives `SafeN` of the machine
-/

import Lprog.Ascent.Refine

namespace Lprog.Ascent

variable {σ τ E : Type}

/-- Safe along every run, at every budget. -/
def AllSafe (A : System σ E) (Q : σ → Prop) (s : σ) : Prop :=
  ∀ k, SafeN (erase A.step) A.accept (fun _ => True) k Q s

namespace AllSafe

variable {A : System σ E} {Q : σ → Prop} {s t : σ}

theorem next {es : List E} (h : AllSafe A Q s) (hs : A.step s (.ok (t, es))) : AllSafe A Q t :=
  fun k => SafeN.next trivial ⟨es, hs⟩ (h (k + 1))

theorem not_wrong (h : AllSafe A Q s) (hs : A.step s .wrong) : False :=
  SafeN.not_wrong trivial hs (h 2)

theorem acc (h : AllSafe A Q s) (ha : A.accept s) : Q s :=
  SafeN.of_accept trivial ha (h 1)

theorem steps {tr : List E} (h : AllSafe A Q s) (hs : Steps A s tr t) : AllSafe A Q t := by
  induction hs with
  | refl => exact h
  | step h1 _ ih => exact ih (h.next h1)

theorem not_goesWrong {tr : List E} (h : AllSafe A Q s) (hw : GoesWrong A s tr) : False := by
  obtain ⟨tr', -, hb⟩ := hw
  obtain ⟨u, hs, hw⟩ := Behaves.wrong_iff.1 hb
  exact (h.steps hs).not_wrong hw

end AllSafe

/-- **What the machine does at `t`, at the program's state `s`**, after steps of the program
    that make no events: a machine step is a state related by `S`, or by `T` where the
    program has stopped; an accepting machine is an accepting program, related by `U`; and a
    machine that traps without accepting is a program that does. -/
structure Matched (A : System σ E) (step : τ → Outcome τ → Prop) (accept : τ → Prop)
    (S T U : σ → τ → Prop) (s : σ) (t : τ) : Prop where
  next : ∀ t', step t (.ok t') → ∃ s', Steps A s [] s' ∧ (S s' t' ∨ T s' t')
  acc : accept t → ∃ s', Steps A s [] s' ∧ A.accept s' ∧ U s' t
  trap : step t .trap → ¬ accept t → ∃ s', Steps A s [] s' ∧ ¬ A.accept s' ∧ A.step s' .trap

/-- **The transfer theorem.** Where every machine step from related states is matched or the
    program can go `wrong` (`back`), and the machine never goes `wrong` by itself, a program
    state safe at every budget makes the related machine state safe: `Q` gives `P` where both
    accept (`hacc`), and the machine's continuation where the program has stopped (`hret`). -/
theorem transfer {A : System σ E} {step : τ → Outcome τ → Prop} {accept : τ → Prop}
    {S T U : σ → τ → Prop} {G : τ → Prop} {N : Nat} {Q : σ → Prop} {P : τ → Prop}
    (back : ∀ s t, S s t → GoesWrong A s [] ∨ Matched A step accept S T U s t)
    (hw : ∀ t, ¬ step t .wrong)
    (hacc : ∀ s t, U s t → A.accept s → Q s → P t)
    (hret : ∀ s t, T s t → AllSafe A Q s → SafeN step accept G N P t) :
    ∀ n, n ≤ N → ∀ s t, S s t → AllSafe A Q s → SafeN step accept G n P t := by
  intro n
  induction n with
  | zero => intros; exact SafeN.zero
  | succ n ih =>
    intro hn s t hs hL
    rcases back s t hs with hwr | hm
    · exact (hL.not_goesWrong hwr).elim
    refine SafeN.intro (fun ha => ?_) fun o ho => ?_
    · obtain ⟨s', hs', ha', hu⟩ := hm.acc ha
      exact hacc s' t hu ha' ((hL.steps hs').acc ha')
    · cases o with
      | ok t' =>
        obtain ⟨s', hs', hsim | hstop⟩ := hm.next t' ho
        · exact ih (by omega) s' t' hsim (hL.steps hs')
        · exact SafeN.mono (by omega) (hret s' t' hstop (hL.steps hs'))
      | trap => trivial
      | wrong => exact hw t ho

end Lprog.Ascent
