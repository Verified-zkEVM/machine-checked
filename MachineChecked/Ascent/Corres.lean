/-
  MachineChecked.Ascent.Corres

  Ported from catcrypt-compiler `HaxAscent/Calculus/CorresMCore.lean` and
  `HaxAscent/Calculus/CorresGenericSpec.lean` at `69ffea9f` (MIT, Copyright (c) 2024-2026
  CatCrypt Contributors; see `LICENSE-catcrypt`). The link to `CatCryptCore`'s relational
  refinement (`corresM_iff_rrelPT`, `corresM_trans_of_rrelPT`) is not ported; the
  composition along a run (`CorresM.seq`) is new here.
-/

import MachineChecked.Ascent.Refines

/-!
# The machine-generic correspondence `CorresM`

`CorresM step SR P fa c` is the forward simulation of a machine with step function
`step : C → M → Option M` against an abstract state transformer `fa`, under the state
relation `SR` and the abstract precondition `P`: from a machine state related to an
abstract state satisfying `P`, `step c` makes progress to a state related to `fa a`. It is
`RefinesP` of `fa` by `step c` with `SR` on inputs and outputs. The module imports no
machine model; an instruction set supplies `step` (for RISC-V, `stepsSp1` with the
program coordinate the number of steps, `MachineChecked.RiscV.Corres`).

`StepTriple step pre c post` is the total triple over an `Option`-valued step. The
correspondence is equivalent to the family of triples

    StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q

over all `Q` (`corresM_iff_post`).

## Main definitions

* `CorresM`, `StepTriple`, `StepTriple.consequence`

## Main results

* `corresM_post`, `corresM_of_post`, `corresM_iff_post`
* `CorresM.weaken`, `CorresM.seq`: a stronger precondition, and the composition of two
  correspondences along a run whose step counts add
-/

namespace MachineChecked.Ascent

/-- The machine-generic forward simulation: from a machine state `m` related by `SR` to an
    abstract state satisfying `P`, the step `step c` makes progress (`= some m'`) to a state
    related to the abstract result `fa a`. -/
abbrev CorresM {M : Type} {C : Type} {AState : Type} (step : C → M → Option M)
    (SR : M → AState → Prop) (P : AState → Prop) (fa : AState → AState) (c : C) : Prop :=
  RefinesP (step c) SR SR P fa

/-! ## The total triple over a step -/

/-- The total triple over an `Option`-valued step: from every machine state satisfying
    `pre`, the step `step c` succeeds in a state satisfying `post`. -/
def StepTriple {M C : Type} (step : C → M → Option M) (pre : M → Prop) (c : C)
    (post : M → Prop) : Prop :=
  ∀ m, pre m → ∃ m', step c m = some m' ∧ post m'

/-- Consequence: strengthen the precondition, weaken the postcondition. -/
theorem StepTriple.consequence {M C : Type} {step : C → M → Option M}
    {pre pre' post post' : M → Prop} {c : C} (hpre : ∀ m, pre' m → pre m)
    (hpost : ∀ m, post m → post' m) (h : StepTriple step pre c post) :
    StepTriple step pre' c post' := by
  intro m hm
  obtain ⟨m', hstep, hm'⟩ := h m (hpre m hm)
  exact ⟨m', hstep, hpost m' hm'⟩

/-! ## The correspondence as a family of triples -/

section Generic

variable {M C AState : Type} {step : C → M → Option M} {SR : M → AState → Prop}
  {P : AState → Prop} {fa : AState → AState} {c : C}

/-- A `CorresM` correspondence gives a step triple for every postcondition `Q`: the
    precondition holds at `m` when some abstract state `a` is related to `m`, satisfies `P`,
    and every machine state related to `fa a` satisfies `Q`. -/
theorem corresM_post (h : CorresM step SR P fa c) (Q : M → Prop) :
    StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q := by
  rintro m ⟨a, hSR, hP, hQ⟩
  obtain ⟨m', hstep, hSR'⟩ := h m a hSR hP
  exact ⟨m', hstep, hQ m' hSR'⟩

/-- The family of triples of `corresM_post` over all postconditions gives the
    correspondence, by instantiating `Q` with `SR · (fa a)`. -/
theorem corresM_of_post
    (h : ∀ Q : M → Prop,
      StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q) :
    CorresM step SR P fa c :=
  fun m a hSR hP => h (fun m' => SR m' (fa a)) m ⟨a, hSR, hP, fun _ h' => h'⟩

/-- `CorresM step SR P fa c` is equivalent to the family of step triples of `corresM_post`
    over all postconditions. -/
theorem corresM_iff_post :
    CorresM step SR P fa c ↔ ∀ Q : M → Prop,
      StepTriple step (fun m => ∃ a, SR m a ∧ P a ∧ ∀ m', SR m' (fa a) → Q m') c Q :=
  ⟨corresM_post, corresM_of_post⟩

/-- A stronger abstract precondition. -/
theorem CorresM.weaken {P' : AState → Prop} (h : CorresM step SR P fa c)
    (himp : ∀ a, P' a → P a) : CorresM step SR P' fa c :=
  fun m a hSR hP' => h m a hSR (himp a hP')

/-- The abstract transformer may be replaced by an equal one. -/
theorem CorresM.congr {fa' : AState → AState} (h : CorresM step SR P fa c)
    (he : ∀ a, P a → fa a = fa' a) : CorresM step SR P fa' c := by
  intro m a hSR hP
  obtain ⟨m', hstep, hSR'⟩ := h m a hSR hP
  exact ⟨m', hstep, he a hP ▸ hSR'⟩

end Generic

/-! ## Composition along a run -/

/-- **Sequencing.** For a run `run : Nat → M → Option M` whose step counts add, a
    correspondence of `j` steps for `f` under `P`, followed by one of `k` steps for `g` under
    `Q`, where `f` establishes `Q`, is a correspondence of `j + k` steps for `g ∘ f`. -/
theorem CorresM.seq {M AState : Type} {run : Nat → M → Option M}
    (hadd : ∀ j k m, run (j + k) m = (run j m).bind (run k))
    {SR : M → AState → Prop} {P Q : AState → Prop} {f g : AState → AState} {j k : Nat}
    (h₁ : CorresM run SR P f j) (h₂ : CorresM run SR Q g k) (hPQ : ∀ a, P a → Q (f a)) :
    CorresM run SR P (fun a => g (f a)) (j + k) := by
  intro m a hSR hP
  obtain ⟨m₁, hr₁, hSR₁⟩ := h₁ m a hSR hP
  obtain ⟨m₂, hr₂, hSR₂⟩ := h₂ m₁ (f a) hSR₁ (hPQ a hP)
  exact ⟨m₂, by rw [hadd, hr₁, Option.bind_some, hr₂], hSR₂⟩

end MachineChecked.Ascent
