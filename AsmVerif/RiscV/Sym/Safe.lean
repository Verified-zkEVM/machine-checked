/-
  AsmVerif.RiscV.Sym.Safe

  The judgement the whole-program proof is written in.

  `Safe P s` says: every state the machine reaches from `s` that is accepting
  makes `P` true. The soundness theorem is `Safe (GuestStatement …) s₀`.

  It is a *partial*-correctness judgement, and that is deliberate. Soundness
  needs nothing about runs that never halt, and nothing about runs that halt
  rejecting; a panic path is `Safe` because it halts with `a0 ≠ 0`, a divergent
  loop is `Safe` because it never halts. So nothing here asks for termination.

  Function specifications are written in continuation form:

    ∀ s, Pre s → (∀ t, Post s t → Safe P t) → Safe P s

  "if the caller is safe from every state the function can return in, it is
  safe from the call". That form composes by application, covers the paths on
  which a function does not return at all (a panic inside it discharges `Safe`
  there and then), and quantifies over `P`, so one proof serves every caller.

  The one fact about the machine it needs is that an accepting state is stuck
  (`HALT` stops the machine), so any state that *steps* is not accepting and a
  step never has to be checked for acceptance.
-/

import AsmVerif.RiscV.Sym.Core

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

/-- Every accepting state reachable from `s` satisfies `P`. -/
def Safe (P : Prop) (s : MachineState) : Prop :=
  ∀ n s', run n s = some s' → Accepted s' → P

/-- A step: safety is inherited from the successor. -/
theorem Safe.step {P : Prop} {s t : MachineState} (h : stepSp1 s = some t) (ht : Safe P t) :
    Safe P s := by
  intro n s' hn ha
  cases n with
  | zero =>
    simp at hn; subst hn
    rw [stepSp1_of_accepted ha] at h; exact absurd h (by simp)
  | succ n =>
    rw [run_succ_of_step h] at hn
    exact ht n s' hn ha

/-- A step, with the successor given by an equation (the executor's form). -/
theorem Safe.step' {P : Prop} {s t t' : MachineState} (h : stepSp1 s = some t) (heq : t = t')
    (ht : Safe P t') : Safe P s :=
  Safe.step (heq ▸ h) ht

/-- Many steps. -/
theorem Safe.run {P : Prop} {s t : MachineState} {k : Nat} (h : run k s = some t) (ht : Safe P t) :
    Safe P s := by
  induction k generalizing s with
  | zero => simp at h; subst h; exact ht
  | succ k ih =>
    rw [run_succ] at h
    cases hs : stepSp1 s with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some s₁ => rw [hs] at h; exact Safe.step hs (ih h)

/-- A stuck state is safe exactly when it is not accepting or `P` holds. -/
theorem Safe.stuck {P : Prop} {s : MachineState} (h : stepSp1 s = none) (hp : Accepted s → P) :
    Safe P s := by
  intro n s' hn ha
  obtain ⟨rfl, rfl⟩ := run_of_stuck h hn
  exact hp ha

/-- The `HALT` syscall: safe when `a0 = 0` gives `P`. -/
theorem Safe.halt {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = 0) (hp : s.getReg .x10 = 0 → P) : Safe P s :=
  Safe.stuck (stepSp1_halt hfetch ht0) (fun ha => hp ha.2.2)

/-- A halt with a nonzero exit code is safe for every `P`. -/
theorem Safe.reject {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = 0) (ha0 : s.getReg .x10 ≠ 0) : Safe P s :=
  Safe.halt hfetch ht0 (fun h => absurd h ha0)

/-- A trap (no instruction at the pc) is safe for every `P`. -/
theorem Safe.trap {P : Prop} {s : MachineState} (h : s.code s.pc = none) : Safe P s :=
  Safe.stuck (stepSp1_none h) (fun ha => absurd (h.symm.trans ha.1) (by simp))

/-- Anything is safe for a true `P`. -/
theorem Safe.of_true {P : Prop} (hp : P) (s : MachineState) : Safe P s :=
  fun _ _ _ _ => hp

/-- Monotonicity in `P`. -/
theorem Safe.mono {P Q : Prop} {s : MachineState} (h : Safe P s) (hpq : P → Q) : Safe Q s :=
  fun n s' hn ha => hpq (h n s' hn ha)

/-! ## Case splits -/

theorem Safe.by_cases {P : Prop} {s : MachineState} (c : Prop) [Decidable c]
    (h₁ : c → Safe P s) (h₂ : ¬ c → Safe P s) : Safe P s :=
  if hc : c then h₁ hc else h₂ hc

/-! ## Loops

A loop is a family of states `Inv i` indexed by the iteration count. Each body
execution takes `Inv i` to `Inv (i+1)` (in continuation form, so a body may also
panic), and `Inv N` hands over to the code after the loop. The iteration count
is the induction; nothing here counts steps. -/

theorem Safe.loop {P : Prop} (Inv : Nat → MachineState → Prop) (N : Nat)
    (hbody : ∀ i, i < N → ∀ s, Inv i s → (∀ t, Inv (i + 1) t → Safe P t) → Safe P s)
    (hN : ∀ s, Inv N s → Safe P s) : ∀ s, Inv 0 s → Safe P s := by
  have : ∀ j, j ≤ N → ∀ s, Inv (N - j) s → Safe P s := by
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

/-- A loop whose iteration count is not known in advance: a measure that
    decreases on every iteration that does not exit. -/
theorem Safe.loop_measure {P : Prop} (Inv : MachineState → Prop) (μ : MachineState → Nat)
    (hbody : ∀ s, Inv s → (∀ t, Inv t → μ t < μ s → Safe P t) → Safe P s) :
    ∀ s, Inv s → Safe P s := by
  have : ∀ m s, μ s ≤ m → Inv s → Safe P s := by
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

end AsmVerif.RiscV.Sym

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

/-! ## The executor's forms

The executor never states a successor state by hand: it hands a lemma a
continuation `∀ s', shape = s' → Safe P s'` and then introduces `s'`. -/

theorem Safe.step_gen {P : Prop} {s t : MachineState} (h : stepSp1 s = some t)
    (k : ∀ s', t = s' → Safe P s') : Safe P s :=
  Safe.step h (k t rfl)

/-- Name a value: the executor's way of introducing an atom. -/
theorem Safe.gen {P : Prop} {s : MachineState} {α : Sort _} (e : α)
    (k : ∀ a, e = a → Safe P s) : Safe P s :=
  k e rfl

theorem Safe.cases {P : Prop} {s : MachineState} (c : Prop)
    (h₁ : c → Safe P s) (h₂ : ¬ c → Safe P s) : Safe P s :=
  (Classical.em c).elim h₁ h₂

end AsmVerif.RiscV.Sym
