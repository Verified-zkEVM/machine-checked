/-
  MachineChecked.RiscV.Corres

  The ascent's correspondence on riscv-zkvm, and the bridge into the framework's judgement.

  `Corres SR P fa k` is `Ascent.CorresM` at the run `stepsSp1` of the SP1 backend, with the
  program coordinate the number of steps: from a state related by `SR` to an abstract state
  satisfying `P`, `k` steps of `stepSp1` succeed and end in a state related to `fa a`. There
  is one step function, riscv-zkvm's `stepSp1`; a correspondence is a statement about its
  runs and nothing else.

  A correspondence is total and `SafeN` is partial, so the bridge goes the easy way: `k`
  successful steps pass `SafeN` back from the end state to the start (`SafeN.steps`), for
  every guard and budget. No step of the run is an accepting halt, since an accepting state
  is stuck. The run may contain `ecall`s: the correspondence fixes their outcome, and the
  bridge does not care.

  * `SafeN.of_corres`: a correspondence gives the continuation form of a specification.
  * `Check.Iface.holds_of_corres`: a correspondence whose end relation implies the interface's
    `Post` proves the interface, so its function enters the contract table.
-/

import MachineChecked.Ascent.Corres
import MachineChecked.RiscV.Check.Spec

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64 MachineChecked.Ascent

/-- The correspondence over `k` steps of the SP1 backend. -/
abbrev Corres {AState : Type} (SR : MachineState → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (k : Nat) : Prop :=
  CorresM stepsSp1 SR P fa k

namespace Corres

variable {AState : Type} {SR : MachineState → AState → Prop} {P Q : AState → Prop}
  {f g : AState → AState}

/-- Zero steps: the identity abstraction. -/
theorem refl : Corres SR P id 0 :=
  fun m _ hSR _ => ⟨m, rfl, hSR⟩

/-- One step: a step from every related state to a state related to the abstract result. -/
theorem one (h : ∀ m a, SR m a → P a → ∃ t, stepSp1 m = some t ∧ SR t (f a)) :
    Corres SR P f 1 := by
  intro m a hSR hP
  obtain ⟨t, hs, ht⟩ := h m a hSR hP
  exact ⟨t, by simp [stepsSp1, hs], ht⟩

/-- Sequencing: step counts add, transformers compose. -/
theorem seq {j k : Nat} (h₁ : Corres SR P f j) (h₂ : Corres SR Q g k)
    (hPQ : ∀ a, P a → Q (f a)) : Corres SR P (fun a => g (f a)) (j + k) :=
  CorresM.seq stepsSp1_add h₁ h₂ hPQ

end Corres

/-- **The bridge.** A correspondence from `s` gives the continuation form of `SafeN`: if every
    state related to the abstract result is safe for `n` steps, so is `s`, for every guard and
    every `P`. -/
theorem SafeN.of_corres {AState : Type} {SR : MachineState → AState → Prop}
    {Pre : AState → Prop} {fa : AState → AState} {k : Nat} (h : Corres SR Pre fa k)
    {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} {a : AState}
    (hSR : SR s a) (hPre : Pre a) (hk : ∀ t, SR t (fa a) → SafeN G n P t) : SafeN G n P s := by
  obtain ⟨t, hrun, ht⟩ := h s a hSR hPre
  exact SafeN.steps hrun (hk t ht)

namespace Check

/-- **An interface from a correspondence.** If every state at the entry satisfying the
    interface's precondition is related to an abstract state satisfying `Pre`, and every
    state related to the abstract result is a return the interface's `Post` admits, then the
    correspondence proves the interface at every budget. The abstract state may record the
    entry state, so `Post`'s comparison of entry and return is a property of `fa`. -/
theorem Iface.holds_of_corres {env : Env} {C : Word → Option Instr} {σ : Iface}
    {AState : Type} {SR : MachineState → AState → Prop} {Pre : AState → Prop}
    {fa : AState → AState} {k : Nat} (h : Corres SR Pre fa k)
    (habs : ∀ s, s.pc = σ.entry → Check.Pre env C σ s →
      ∃ a, SR s a ∧ Pre a ∧ ∀ t, SR t (fa a) → Post env σ s t) :
    σ.Holds env C := by
  intro n G _ P s hpc hpre hk
  obtain ⟨a, hSR, hPa, hpost⟩ := habs s hpc hpre
  exact SafeN.of_corres h hSR hPa (fun t ht => hk t (hpost t ht))

end Check

end MachineChecked.RiscV
