/-
  MachineChecked.Ascent.Corres

  The correspondence of a machine with an abstract function, independent of any machine.

  After catcrypt-compiler's `CorresM` and `CorresIsaRun` (`HaxAscent/Calculus/CorresMCore.lean`,
  `Ascent/CorresIsa.lean` at `69ffea9f`; MIT, Copyright (c) 2024-2026 CatCrypt Contributors;
  see `LICENSE-catcrypt`), stated as a contract in continuation form over the judgement
  (`Ascent.SafeN`), so that one notion serves straight-line code, loops, functions and
  machines with more than one result per step.

  `Corres step accept SR P fa`: whatever a machine state related by `SR` to an abstract state
  satisfying `P` continues with is safe if it is safe from every state related to `fa` of it.
  Every run, not some run, must reach a related state or stop safely. On a deterministic
  machine the form over `Reaches` (some run reaches a related state) implies it
  (`Corres.of_reaches`). Correspondences compose along a run (`Corres.seq`).

  ## Main definitions

  * `Corres`

  ## Main results

  * `Corres.refl`, `Corres.weaken`, `Corres.seq`, `Corres.of_reaches`
-/

import MachineChecked.Ascent.Safe
import MachineChecked.Ascent.Run

namespace MachineChecked.Ascent

/-- **The correspondence**: from a state related by `SR` to an abstract state satisfying `P`,
    every continuation safe from the states related to `fa` of it is safe. -/
def Corres {σ AState : Type} (step : σ → Outcome σ → Prop) (accept : σ → Prop)
    (SR : σ → AState → Prop) (P : AState → Prop) (fa : AState → AState) : Prop :=
  ∀ (G : σ → Prop) (n : Nat) (Q : σ → Prop) m a, SR m a → P a →
    (∀ t, SR t (fa a) → SafeN step accept G n Q t) → SafeN step accept G n Q m

namespace Corres

variable {σ AState : Type} {step : σ → Outcome σ → Prop} {accept : σ → Prop}
  {SR : σ → AState → Prop} {P P' : AState → Prop}

theorem refl : Corres step accept SR P id := fun _ _ _ m _ hSR _ hk => hk m hSR

/-- A stronger precondition. -/
theorem weaken {fa : AState → AState} (h : Corres step accept SR P fa) (hP : ∀ a, P' a → P a) :
    Corres step accept SR P' fa :=
  fun G n Q m a hSR hP' hk => h G n Q m a hSR (hP a hP') hk

/-- Sequencing: `f`, then `g`. -/
theorem seq {f g : AState → AState} (h₁ : Corres step accept SR P f)
    (h₂ : Corres step accept SR P' g) (hPP' : ∀ a, P a → P' (f a)) :
    Corres step accept SR P (fun a => g (f a)) :=
  fun G n Q m a hSR hP hk => h₁ G n Q m a hSR hP fun t ht => h₂ G n Q t (f a) ht (hPP' a hP) hk

/-- **On a deterministic machine, reaching is corresponding**, when accepting states are
    stuck. -/
theorem of_reaches {f : σ → Option σ} (hacc : ∀ s, accept s → f s = none)
    (h : ∀ m a, SR m a → P a → Reaches f (fun t => SR t (fa a)) m) :
    Corres (detStep f) accept SR P fa :=
  fun _ _ _ m a hSR hP hk => SafeN.of_reaches hacc (h m a hSR hP) hk

end Corres

end MachineChecked.Ascent
