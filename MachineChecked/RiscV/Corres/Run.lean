/-
  MachineChecked.RiscV.Corres.Run

  Runs whose length depends on the state, and the rules for functions, calls and loops:
  the counterpart over `stepSp1` of catcrypt-compiler's `CorresIsaRun` (`Ascent/CorresIsa`)
  and of the `FnSpec`, `steps_call` and `steps_loop_inv` rules of its rv64 stack.

  * `Reach Q s`: some number of steps from `s` succeeds and ends in a state satisfying `Q`.
  * `CorresRun SR P fa`: the correspondence with the number of steps chosen per initial
    state; a fixed-length `Corres` gives one (`CorresRun.of_corres`).
  * `FnSpec entry pre post`: from every state at `entry` satisfying `pre`, the function runs to
    a state `post` relates to it. With `post` asking for `t.pc = ra`, it is a function that
    returns.
  * `Reach.call`: at a call of a function meeting its `FnSpec`, the run continues from every
    state the function may return in.
  * `Reach.loop`: a loop given by an invariant and a measure that every iteration decreases.

  The bridge is `SafeN.of_reach`: a run from `s` passes `SafeN` back from its end.
-/

import MachineChecked.RiscV.Corres.Block

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64 MachineChecked.Ascent

/-- Some number of steps from `s` succeeds and ends in a state satisfying `Q`. -/
def Reach (Q : MachineState → Prop) (s : MachineState) : Prop :=
  ∃ k t, stepsSp1 k s = some t ∧ Q t

namespace Reach

variable {Q R : MachineState → Prop}

theorem done {s : MachineState} (h : Q s) : Reach Q s := ⟨0, s, rfl, h⟩

theorem step {s t : MachineState} (h : stepSp1 s = some t) (ht : Reach Q t) : Reach Q s := by
  obtain ⟨k, u, hk, hu⟩ := ht
  exact ⟨k + 1, u, by rw [stepsSp1_succ_of_step h, hk], hu⟩

theorem steps {s t : MachineState} {k : Nat} (h : stepsSp1 k s = some t) (ht : Reach Q t) :
    Reach Q s := by
  obtain ⟨j, u, hj, hu⟩ := ht
  exact ⟨k + j, u, by rw [stepsSp1_add, h, Option.bind_some, hj], hu⟩

theorem mono {s : MachineState} (h : Reach Q s) (hQR : ∀ t, Q t → R t) : Reach R s := by
  obtain ⟨k, t, hk, ht⟩ := h
  exact ⟨k, t, hk, hQR t ht⟩

/-- Runs compose: reach `Q`, and from every state satisfying `Q` reach `R`. -/
theorem trans {s : MachineState} (h : Reach Q s) (hQR : ∀ t, Q t → Reach R t) : Reach R s := by
  obtain ⟨k, t, hk, ht⟩ := h
  exact steps hk (hQR t ht)

/-- A plain instruction (no memory access, no system call). -/
theorem plain {s : MachineState} {i : Instr} (hf : s.code s.pc = some i)
    (hm : i.isMemAccess = false) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (h : Reach Q (execInstrBr s i)) : Reach Q s :=
  step (MachineChecked.RiscV.Sym.stepSp1_plain hf hm he hb) h

/-- A load or store SP1 admits. -/
theorem mem {s : MachineState} {i : Instr} (hf : s.code s.pc = some i)
    (hm : i.isMemAccess = true) (hc : MachineChecked.RiscV.Sym.isCSRS i = false) (hok : memOkSp1 s i = true)
    (h : Reach Q (execInstrBr s i)) : Reach Q s :=
  step (MachineChecked.RiscV.Sym.stepSp1_mem hf hm hc hok) h

/-- **A loop.** If from every state satisfying the invariant the run either reaches `Q`, or
    reaches a state satisfying the invariant with a smaller measure, then from every state
    satisfying the invariant the run reaches `Q`. -/
theorem loop (Inv : MachineState → Prop) (μ : MachineState → Nat)
    (hbody : ∀ s, Inv s → Reach (fun t => Q t ∨ (Inv t ∧ μ t < μ s)) s) :
    ∀ s, Inv s → Reach Q s := by
  have : ∀ m s, μ s ≤ m → Inv s → Reach Q s := by
    intro m
    induction m with
    | zero =>
      intro s hμ hs
      exact trans (hbody s hs) fun t ht => ht.elim done fun h => absurd h.2 (by omega)
    | succ m ih =>
      intro s hμ hs
      exact trans (hbody s hs) fun t ht => ht.elim done fun h => ih t (by omega) h.1
  exact fun s hs => this _ s (Nat.le_refl _) hs

end Reach

/-- **The bridge for a run.** A run from `s` to states that are all safe for `n` steps makes
    `s` safe for `n` steps. -/
theorem SafeN.of_reach {G : MachineState → Prop} {n : Nat} {P : Prop} {Q : MachineState → Prop}
    {s : MachineState} (h : Reach Q s) (hk : ∀ t, Q t → SafeN G n P t) : SafeN G n P s := by
  obtain ⟨k, t, hk', ht⟩ := h
  exact SafeN.steps hk' (hk t ht)

/-- The correspondence with the number of steps chosen per initial state. -/
def CorresRun {AState : Type} (SR : MachineState → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) : Prop :=
  ∀ m a, SR m a → P a → Reach (fun t => SR t (fa a)) m

/-- A correspondence of fixed length is one with the length chosen per state. -/
theorem CorresRun.of_corres {AState : Type} {SR : MachineState → AState → Prop}
    {P : AState → Prop} {fa : AState → AState} {k : Nat} (h : Corres SR P fa k) :
    CorresRun SR P fa := by
  intro m a hSR hP
  obtain ⟨t, ht, hSR'⟩ := h m a hSR hP
  exact ⟨k, t, ht, hSR'⟩

/-- Sequencing. -/
theorem CorresRun.seq {AState : Type} {SR : MachineState → AState → Prop} {P Q : AState → Prop}
    {f g : AState → AState} (h₁ : CorresRun SR P f) (h₂ : CorresRun SR Q g)
    (hPQ : ∀ a, P a → Q (f a)) : CorresRun SR P (fun a => g (f a)) := by
  intro m a hSR hP
  exact Reach.trans (h₁ m a hSR hP) fun t ht => h₂ t (f a) ht (hPQ a hP)

/-- **A function**: from every state at `entry` satisfying `pre`, the run reaches a state `post`
    relates to it. -/
def FnSpec (entry : Word) (pre : MachineState → Prop) (post : MachineState → MachineState → Prop) :
    Prop :=
  ∀ s, s.pc = entry → pre s → Reach (post s) s

/-- **A call.** At a `jal ra, off` whose target is a function meeting its specification, the
    run continues from every state the function may return in, given the state after the
    `jal` (the return address in `ra`, the pc at the entry). -/
theorem Reach.call {Q : MachineState → Prop} {s : MachineState} {off : BitVec 21} {entry : Word}
    {pre : MachineState → Prop} {post : MachineState → MachineState → Prop}
    (hf : s.code s.pc = some (.JAL .x1 off)) (hentry : s.pc + signExtend21 off = entry)
    (hspec : FnSpec entry pre post)
    (hpre : pre (execInstrBr s (.JAL .x1 off)))
    (hk : ∀ t, post (execInstrBr s (.JAL .x1 off)) t → Reach Q t) : Reach Q s := by
  refine Reach.plain hf rfl (by simp) (by simp) ?_
  exact Reach.trans (hspec _ (by simp only [execInstrBr, pc_setPC', hentry]) hpre) hk

/-- The continuation form of a function's specification. -/
theorem SafeN.of_fnSpec {entry : Word} {pre : MachineState → Prop}
    {post : MachineState → MachineState → Prop} (h : FnSpec entry pre post)
    {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} (hpc : s.pc = entry)
    (hpre : pre s) (hk : ∀ t, post s t → SafeN G n P t) : SafeN G n P s :=
  SafeN.of_reach (h s hpc hpre) hk

end MachineChecked.RiscV
