/-
  MachineChecked.Ascent.Run

  Runs of a step function, independent of any machine.

  A machine is given by a partial step function `f : σ → Option σ` (`none` is a fault or a
  stuck state). `steps f n s` runs exactly `n` steps, and `Reaches f Q s` says some number
  of steps from `s` succeeds and ends in a state satisfying `Q`. This is the one notion of a
  run in MachineChecked: riscv-zkvm's machine (`MachineChecked.RiscV.stepsSp1`) and the low
  logical program (`MachineChecked.Lprog.Isa.step`) are both instances, and the lift between
  them carries a `Reaches` at one level to a `Reaches` at the other.

  ## Main definitions

  * `steps`, `Reaches`

  ## Main results

  * `steps_add`, `steps_succ_of_step`
  * `Reaches.step`, `Reaches.steps`, `Reaches.trans`: runs compose
  * `Reaches.loop`: a loop given by an invariant and a decreasing measure
-/

namespace MachineChecked.Ascent

variable {σ : Type} (f : σ → Option σ)

/-- Exactly `n` steps. -/
def steps : Nat → σ → Option σ
  | 0, s => some s
  | n + 1, s => (f s).bind (steps n)

@[simp] theorem steps_zero (s : σ) : steps f 0 s = some s := rfl

theorem steps_succ (n : Nat) (s : σ) : steps f (n + 1) s = (f s).bind (steps f n) := rfl

variable {f}

theorem steps_succ_of_step {n : Nat} {s s₁ : σ} (h : f s = some s₁) :
    steps f (n + 1) s = steps f n s₁ := by
  rw [steps_succ, h]; rfl

theorem steps_add (m n : Nat) (s : σ) :
    steps f (m + n) s = (steps f m s).bind (steps f n) := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, steps_succ, steps_succ]
    cases f s with
    | none => rfl
    | some s₁ => simpa using ih s₁

variable (f)

/-- Some number of steps from `s` succeeds and ends in a state satisfying `Q`. -/
def Reaches (Q : σ → Prop) (s : σ) : Prop := ∃ n t, steps f n s = some t ∧ Q t

namespace Reaches

variable {f} {Q R : σ → Prop}

theorem done {s : σ} (h : Q s) : Reaches f Q s := ⟨0, s, rfl, h⟩

theorem step {s t : σ} (h : f s = some t) (ht : Reaches f Q t) : Reaches f Q s := by
  obtain ⟨n, u, hn, hu⟩ := ht
  exact ⟨n + 1, u, by rw [steps_succ_of_step h, hn], hu⟩

theorem steps {s t : σ} {n : Nat} (h : Ascent.steps f n s = some t) (ht : Reaches f Q t) :
    Reaches f Q s := by
  obtain ⟨j, u, hj, hu⟩ := ht
  exact ⟨n + j, u, by rw [steps_add, h, Option.bind_some, hj], hu⟩

theorem mono {s : σ} (h : Reaches f Q s) (hQR : ∀ t, Q t → R t) : Reaches f R s := by
  obtain ⟨n, t, hn, ht⟩ := h
  exact ⟨n, t, hn, hQR t ht⟩

/-- Runs compose: reach `Q`, and from every state satisfying `Q` reach `R`. -/
theorem trans {s : σ} (h : Reaches f Q s) (hQR : ∀ t, Q t → Reaches f R t) :
    Reaches f R s := by
  obtain ⟨n, t, hn, ht⟩ := h
  exact steps hn (hQR t ht)

/-- **A loop.** If from every state satisfying the invariant the run either reaches `Q`, or
    reaches a state satisfying the invariant with a smaller measure, then from every state
    satisfying the invariant the run reaches `Q`. -/
theorem loop (Inv : σ → Prop) (μ : σ → Nat)
    (hbody : ∀ s, Inv s → Reaches f (fun t => Q t ∨ (Inv t ∧ μ t < μ s)) s) :
    ∀ s, Inv s → Reaches f Q s := by
  have : ∀ m s, μ s ≤ m → Inv s → Reaches f Q s := by
    intro m
    induction m with
    | zero =>
      intro s hμ hs
      exact trans (hbody s hs) fun t ht => ht.elim done fun h => absurd h.2 (by omega)
    | succ m ih =>
      intro s hμ hs
      exact trans (hbody s hs) fun t ht => ht.elim done fun h => ih t (by omega) h.1
  exact fun s hs => this _ s (Nat.le_refl _) hs

end Reaches

end MachineChecked.Ascent
