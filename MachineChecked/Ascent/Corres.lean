/-
  MachineChecked.Ascent.Corres

  The correspondence of a machine with an abstract function, independent of any machine.

  After catcrypt-compiler's `CorresM` and `CorresIsaRun` (`HaxAscent/Calculus/CorresMCore.lean`,
  `Ascent/CorresIsa.lean` at `69ffea9f`; MIT, Copyright (c) 2024-2026 CatCrypt Contributors;
  see `LICENSE-catcrypt`), stated over `Reaches`: the number of steps is chosen per initial
  state rather than fixed, so one notion serves straight-line code, loops and functions.

  `Corres step SR P fa`: from a machine state related by `SR` to an abstract state satisfying
  `P`, the machine reaches a state related to `fa` of it. Correspondences compose along a run
  (`Corres.seq`).

  ## Main definitions

  * `Corres`

  ## Main results

  * `Corres.refl`, `Corres.weaken`, `Corres.seq`
-/

import MachineChecked.Ascent.Run

namespace MachineChecked.Ascent

/-- **The correspondence**: from a state related by `SR` to an abstract state satisfying `P`,
    the machine reaches a state related to `fa` of it. -/
def Corres {σ AState : Type} (step : σ → Option σ) (SR : σ → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) : Prop :=
  ∀ m a, SR m a → P a → Reaches step (fun t => SR t (fa a)) m

namespace Corres

variable {σ AState : Type} {step : σ → Option σ} {SR : σ → AState → Prop} {P Q : AState → Prop}

theorem refl : Corres step SR P id := fun _ _ hSR _ => Reaches.done hSR

/-- A stronger precondition. -/
theorem weaken {fa : AState → AState} (h : Corres step SR P fa) (hQP : ∀ a, Q a → P a) :
    Corres step SR Q fa :=
  fun m a hSR hQ => h m a hSR (hQP a hQ)

/-- Sequencing: `f`, then `g`. -/
theorem seq {f g : AState → AState} (h₁ : Corres step SR P f) (h₂ : Corres step SR Q g)
    (hPQ : ∀ a, P a → Q (f a)) : Corres step SR P (fun a => g (f a)) :=
  fun m a hSR hP => (h₁ m a hSR hP).trans fun t ht => h₂ t (f a) ht (hPQ a hP)

end Corres

end MachineChecked.Ascent
