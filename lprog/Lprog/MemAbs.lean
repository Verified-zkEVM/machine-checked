/-
  Lprog.MemAbs

  A program proved safe over a memory that refuses nothing is safe over a memory that refuses
  some accesses, seen through an abstraction of the second to the first.

  Two instruction sets over the shared operations that differ in their memory only step the
  same program the same way, but for a load or a store the second refuses: there it traps,
  which is safe. So a judgement proved over a simple memory (bytes by address) holds over a
  machine's memory with its permission checks, where the proof would otherwise carry a
  condition at each access. What is lost is only what partial correctness never had: that the
  program does not trap.

  The contexts are ones where an external call goes `wrong` and nothing accepts.

  ## Main definitions

  * `MemAbs`: a memory as another, through an abstraction
  * `absState`

  ## Main results

  * `step_abs`: a step over the second memory is the step over the first
  * `allSafe_abs`: safe over the first gives safe over the second
-/

import Lprog.Op
import Lprog.Ascent.Transfer

namespace Lprog

open Lprog.Ascent (Outcome AllSafe)

variable {Reg : Type} [DecidableEq Reg] {link sp : Reg} {M₁ M₂ : Type} {mem₁ : Mem M₁}
  {mem₂ : Mem M₂}

/-- **A memory as another, through `abs`**: an access the second allows is the access of the
    first. -/
structure MemAbs (mem₂ : Mem M₂) (mem₁ : Mem M₁) (abs : M₂ → M₁) : Prop where
  load : ∀ w a m v, mem₂.load w a m = some v → mem₁.load w a (abs m) = some v
  store : ∀ w a v m m', mem₂.store w a v m = some m' → mem₁.store w a v (abs m) = some (abs m')

/-- A state over the second memory, as one over the first. -/
def absState (abs : M₂ → M₁) (s : State (Isa.ofOps Reg link sp M₂ mem₂)) :
    State (Isa.ofOps Reg link sp M₁ mem₁) :=
  ⟨s.stack, s.regs, abs s.m⟩

theorem Op.eval_abs {abs : M₂ → M₁} (h : MemAbs mem₂ mem₁ abs) (o : Op Reg)
    {regs r' : Reg → BitVec 64} {m m' : M₂} (he : o.eval mem₂ regs m = some (r', m')) :
    o.eval mem₁ regs (abs m) = some (r', abs m') := by
  cases o with
  | set d e => cases he; rfl
  | skip => cases he; rfl
  | trap => cases he
  | load d w sg a =>
    simp only [Op.eval] at he ⊢
    cases hl : mem₂.load w (a.eval regs) m with
    | none => simp [hl] at he
    | some v =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      rw [h.load _ _ _ _ hl, ← he.1, ← he.2]
      rfl
  | store w a e =>
    simp only [Op.eval] at he ⊢
    cases hs : mem₂.store w (a.eval regs) (e.eval regs) m with
    | none => simp [hs] at he
    | some m1 =>
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      rw [h.store _ _ _ _ _ hs, ← he.1, ← he.2]
      rfl

section step

variable {abs : M₂ → M₁} {E : Type} (p : Lprog (Op Reg) Reg)
  (c₁ : Context (Isa.ofOps Reg link sp M₁ mem₁) E) (c₂ : Context (Isa.ofOps Reg link sp M₂ mem₂) E)

/-- The function a call calls does not depend on the memory. -/
theorem callee_abs (regs : Reg → BitVec 64) (tgt : Target Reg) :
    (Isa.ofOps Reg link sp M₂ mem₂).callee p regs tgt =
      (Isa.ofOps Reg link sp M₁ mem₁).callee p regs tgt := by
  cases tgt <;> rfl

/-- **A step over the second memory is the step over the first**, where it is to a state or
    to `wrong`. -/
theorem step_abs (h : MemAbs mem₂ mem₁ abs)
    (hext : ∀ n regs m o, c₂.ext n regs m o → o = .wrong ∧ c₁.ext n regs (abs m) .wrong)
    (s : State (Isa.ofOps Reg link sp M₂ mem₂)) :
    (∀ t es, (Isa.ofOps Reg link sp M₂ mem₂).step p c₂ s (.ok (t, es)) →
      (Isa.ofOps Reg link sp M₁ mem₁).step p c₁ (absState abs s) (.ok (absState abs t, es))) ∧
    ((Isa.ofOps Reg link sp M₂ mem₂).step p c₂ s .wrong →
      (Isa.ofOps Reg link sp M₁ mem₁).step p c₁ (absState abs s) .wrong) := by
  obtain ⟨stk, regs, m⟩ := s
  cases stk with
  | nil => exact ⟨fun _ _ h => h.elim, fun h => h.elim⟩
  | cons fr rest =>
    cases hf : p[fr.fn]? with
    | none =>
      simp only [Isa.step, absState, hf]
      exact ⟨fun _ _ h => (by cases h), fun _ => trivial⟩
    | some fd =>
      cases hi : fd.body[fr.pc]? with
      | none =>
        simp only [Isa.step, absState, hf, hi]
        exact ⟨fun _ _ h => (by cases h), fun _ => trivial⟩
      | some i =>
        simp only [Isa.step, absState, hf, hi]
        cases i with
        | Lopn o =>
          simp only [Isa.stepI]
          cases he : o.eval mem₂ regs m with
          | none => exact ⟨fun _ _ h => (by cases h), fun h => (by cases h)⟩
          | some rm =>
            obtain ⟨r', m'⟩ := rm
            rw [Op.eval_abs h o he]
            exact ⟨fun t es ht => (by cases ht; rfl), fun h => (by cases h)⟩
        | Lext n =>
          simp only [Isa.stepI]
          exact ⟨fun t es ht => (by cases (hext _ _ _ _ ht.2).1), fun hw => (hext _ _ _ _ hw).2⟩
        | _ =>
          simp only [Isa.stepI, callee_abs (M₁ := M₁) (mem₁ := mem₁) p]
          refine ⟨fun t es ht => ?_, fun hw => ?_⟩ <;> (repeat' split at *) <;> simp_all

/-- **Safe over the first memory gives safe over the second**: a program safe at every
    budget over a memory that refuses nothing is safe over one that refuses some accesses,
    with the postcondition read through the abstraction. -/
theorem allSafe_abs (h : MemAbs mem₂ mem₁ abs)
    (hext : ∀ n regs m o, c₂.ext n regs m o → o = .wrong ∧ c₁.ext n regs (abs m) .wrong)
    (hacc : ∀ n regs m, ¬ c₂.accept n regs m)
    {Q : State (Isa.ofOps Reg link sp M₁ mem₁) → Prop}
    (s : State (Isa.ofOps Reg link sp M₂ mem₂))
    (hs : AllSafe ((Isa.ofOps Reg link sp M₁ mem₁).system p c₁) Q (absState abs s)) :
    AllSafe ((Isa.ofOps Reg link sp M₂ mem₂).system p c₂) (fun s' => Q (absState abs s')) s := by
  intro k
  induction k generalizing s with
  | zero => exact Ascent.SafeN.zero
  | succ k ih =>
    obtain ⟨hok, hwr⟩ := step_abs p c₁ c₂ h hext s
    refine Ascent.SafeN.intro (fun ha => ?_) fun o ho => ?_
    · rcases ha with ha | ⟨n, -, ha⟩
      · exact hs.acc (Or.inl ha)
      · exact (hacc _ _ _ ha).elim
    · cases o with
      | ok t =>
        obtain ⟨es, hst⟩ := ho
        exact ih t (hs.next (hok t es hst))
      | trap => trivial
      | wrong => exact hs.not_wrong (hwr ho)

end step

end Lprog
