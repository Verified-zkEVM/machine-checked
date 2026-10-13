/-
  AsmVerif.RiscV.Check.Spec

  What an interface means, against riscv-zkvm's `stepSp1`.

  ## The judgement

  `SafeN G n P s`: every accepting state reached from `s` in fewer than `n` steps, along a
  run every state of which satisfies the guard `G`, satisfies `P`. Partial correctness: a run
  that traps, rejects or diverges is safe. Accepting is SP1's `HALT` with exit code `0`. The
  guard is where premises about runs go: `Env.Cfi`, the targets of the indirect jumps no
  analysis resolves. With `G = fun _ => True` it is plain safety.

  A specification is in continuation form with one budget on both sides:

      ∀ G P s, s.pc = entry → Pre s → (∀ t, Post s t → SafeN G n P t) → SafeN G n P s

  ("if the caller is safe for `n` steps from wherever the function returns, it is safe for
  `n` steps from the call"). Proved for every `n`, it gives the unbounded `Safe`. A step
  never lowers the budget a proof needs (`SafeN.of_step`), so an executor proof carries `n`
  through unchanged; and the checker's soundness uses a callee's specification at a
  smaller budget than its own, which is what makes recursion and loops compose.

  ## Memory

  Memory is `Word → Word`, keyed by doubleword address. Every store `stepSp1` performs
  writes an 8-aligned key: a doubleword store must be aligned, a narrower one rewrites
  `alignToDword addr`. So what a function leaves unchanged is stated for aligned keys. A
  key `a` is *hit* by a byte range `[b, b + l)` when the doubleword `[a, a + 8)` overlaps it,
  modulo `2^64`.
-/

import AsmVerif.RiscV.Check.Domain
import AsmVerif.RiscV.Frame.Sound

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

/-! ## Accepting, and `SafeN` -/

/-- SP1's accepting halt: `ecall` with `t0 = 0` (HALT) and exit code `a0 = 0`. -/
def Accepted (s : MachineState) : Prop :=
  s.code s.pc = some .ECALL ∧ s.getReg .x5 = 0 ∧ s.getReg .x10 = 0

theorem stepSp1_halt {s : MachineState} (h : s.code s.pc = some .ECALL) (h5 : s.getReg .x5 = 0) :
    stepSp1 s = none := by
  have hacc : Sp1.isAccelId 0#64 = false := by decide
  have hhost : Sp1.isHostId 0#64 = true := by decide
  simp [stepSp1, h, sp1Ecall, h5, hacc, hhost, step, Sp1.HINT_LEN, Sp1.HINT_READ,
    Sp1.COMMIT, Sp1.COMMIT_DEFERRED_PROOFS]

theorem Accepted.stuck {s : MachineState} (h : Accepted s) : stepSp1 s = none :=
  stepSp1_halt h.1 h.2.1

theorem not_accepted_of_code {s : MachineState} {i : Instr} (h : s.code s.pc = some i)
    (hi : i ≠ .ECALL) : ¬ Accepted s := by
  intro ha; have h1 := ha.1; rw [h] at h1; exact hi (Option.some.inj h1)

def SafeN (G : MachineState → Prop) (n : Nat) (P : Prop) (s : MachineState) : Prop :=
  ∀ m < n, ∀ s', stepsSp1 m s = some s' → (∀ j ≤ m, ∀ x, stepsSp1 j s = some x → G x) →
    Accepted s' → P

def Safe (G : MachineState → Prop) (P : Prop) (s : MachineState) : Prop := ∀ n, SafeN G n P s

namespace SafeN

variable {G : MachineState → Prop}

theorem zero {P : Prop} {s : MachineState} : SafeN G 0 P s :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem mono {P : Prop} {s : MachineState} {k n : Nat} (hk : k ≤ n) (h : SafeN G n P s) :
    SafeN G k P s := fun m hm => h m (Nat.lt_of_lt_of_le hm hk)

/-- A step from a state that does not accept: one budget unit is spent. -/
theorem step {P : Prop} {s t : MachineState} {n : Nat} (hna : ¬ Accepted s)
    (hs : stepSp1 s = some t) (ht : SafeN G n P t) : SafeN G (n + 1) P s := by
  intro m hm s' hr hg ha
  cases m with
  | zero => simp [stepsSp1] at hr; subst hr; exact absurd ha hna
  | succ m =>
    obtain ⟨s1, h1, h2⟩ := stepsSp1_succ hr
    rw [hs] at h1; cases h1
    exact ht m (by omega) s' h2
      (fun j hj x hx => hg (j + 1) (by omega) x (by simp [stepsSp1, hs, hx])) ha

/-- A step does not need budget: `SafeN n` passes back along it. -/
theorem of_step {P : Prop} {s t : MachineState} {n : Nat} (hna : ¬ Accepted s)
    (hs : stepSp1 s = some t) (ht : SafeN G n P t) : SafeN G n P s :=
  mono (Nat.le_succ n) (step hna hs ht)

/-- A state with no step: safe unless it accepts. -/
theorem stuck {P : Prop} {s : MachineState} {n : Nat} (hs : stepSp1 s = none)
    (hp : Accepted s → P) : SafeN G n P s := by
  intro m _ s' hr _ ha
  cases m with
  | zero => simp [stepsSp1] at hr; subst hr; exact hp ha
  | succ m => simp [stepsSp1, hs] at hr

/-- From a state that does not accept, safe for `n + 1` steps if every successor is safe
    for `n`. -/
theorem intro {P : Prop} {s : MachineState} {n : Nat} (hna : ¬ Accepted s)
    (h : ∀ t, stepSp1 s = some t → SafeN G n P t) : SafeN G (n + 1) P s := by
  cases hs : stepSp1 s with
  | none => exact stuck hs (fun ha => absurd ha hna)
  | some t => exact step hna hs (h t hs)

/-- The guard holds at the current state of every run it constrains. -/
theorem assume {P : Prop} {s : MachineState} {n : Nat} (h : G s → SafeN G n P s) :
    SafeN G n P s := by
  intro m hm s' hr hg ha
  exact h (hg 0 (Nat.zero_le _) s rfl) m hm s' hr hg ha

end SafeN

/-! ## Memory regions -/

/-- The doubleword at key `a` overlaps the bytes `[b, b + l)`, modulo `2^64`. -/
def Hits (b : Word) (l : Nat) (a : Word) : Prop :=
  (a - b).toNat < l ∨ (0 < l ∧ (b - a).toNat < 8)

def Aligned (a : Word) : Prop := a &&& 7#64 = 0

def _root_.AsmVerif.RiscV.Frame.AVal.eval (E : Ent) : AVal → Word
  | .lin r k => E r + k
  | .const c => c
  | .top => 0
  | .oneOf _ => 0
  | .cell r ks k => E.deref (E r) ks + k

def Len.eval (E : Ent) : Len → Nat
  | .n l => l
  | .reg r => (E r).toNat
  | .regPlus r c => (E r).toNat + c

def Item.Hits (E : Ent) (it : Item) (a : Word) : Prop :=
  Check.Hits (it.base.eval E) (it.len.eval E) a

/-- The frame window of a function entered with stack pointer `e`. -/
def InWin (e : Word) (D : Nat) (a : Word) : Prop := Hits (e - BitVec.ofNat 64 D) D a

def Env.InProt (env : Env) (a : Word) : Prop := ∃ R ∈ env.prot, Hits R.1 R.2 a

/-- The protected regions lie above the stack and do not wrap. -/
def Env.wf (env : Env) : Bool :=
  decide (env.stackTop + 8 ≤ 2 ^ 63) &&
  env.prot.all fun (b, l) => decide (env.stackTop + 8 ≤ b.toNat) && decide (b.toNat + l + 8 ≤ 2 ^ 64)

/-- What a function with interface `σ`, entered with registers `E`, may write. -/
def Written (σ : Iface) (E : Ent) (a : Word) : Prop :=
  InWin (E .x2) σ.depth a ∨ ∃ it ∈ σ.foot, it.Hits E a

/-- The registers and memory of a state, as the entry valuation of a function. -/
def regsOf (s : MachineState) : Ent := ⟨s.getReg, s.getMem⟩

/-- A cell's address, given the entry valuation. -/
def Cell.addr (E : Ent) (c : Cell) : Word := E.deref (E c.r) c.ks + c.k

/-- The precondition: the code is the program's; the stack has room for the window and lies
    below the program; the protected regions hold their contents; footprint items avoid the
    window and the protected regions; the `nz` values are nonzero; the `vals` registers hold
    one of their candidates; each cell is aligned, not something the function may write,
    and holds one of its candidates. -/
def Pre (env : Env) (C : Word → Option Instr) (σ : Iface) (s : MachineState) : Prop :=
  s.code = C ∧ σ.depth ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ env.stackTop ∧
  Aligned (s.getReg .x2) ∧
  (∀ a, Aligned a → env.InProt a → s.getMem a = env.init a) ∧
  (∀ it ∈ σ.foot, ∀ a, Aligned a → it.Hits (regsOf s) a →
    ¬ InWin (s.getReg .x2) σ.depth a ∧ ¬ env.InProt a) ∧
  (∀ v ∈ σ.nz, v.eval (regsOf s) ≠ 0) ∧
  (∀ p ∈ σ.vals, s.getReg p.1 ∈ p.2) ∧
  (∀ c ∈ σ.cells, Aligned (c.addr (regsOf s)) ∧ ¬ Written σ (regsOf s) (c.addr (regsOf s)) ∧
    ∀ cs, c.vals = some cs → s.getMem (c.addr (regsOf s)) ∈ cs)

/-- The postcondition: it returns, to `ra`, with the callee-saved registers restored and
    memory unchanged outside what it may write. -/
def Post (σ : Iface) (s t : MachineState) : Prop :=
  σ.returns = true ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
  (∀ r ∈ savedRegs, t.getReg r = s.getReg r) ∧
  (∀ a, Aligned a → ¬ Written σ (regsOf s) a → t.getMem a = s.getMem a) ∧
  t.code = s.code

/-- The control-flow premise at a state: a listed `jalr` lands on one of its candidates. -/
def Env.Cfi (env : Env) (x : MachineState) : Prop :=
  ∀ p ∈ env.cfi, x.pc = p.1 → ∀ rd rs off, x.code x.pc = some (.JALR rd rs off) →
    (x.getReg rs + signExtend12 off) &&& ~~~1#64 ∈ p.2

/-- `σ` holds for budget `n`, along every run that keeps the program's control-flow
    premise (and whatever else a guard `G` asks). -/
def Iface.HoldsN (env : Env) (C : Word → Option Instr) (σ : Iface) (n : Nat) : Prop :=
  ∀ (G : MachineState → Prop), (∀ x, G x → env.Cfi x) →
  ∀ (P : Prop) (s : MachineState), s.pc = σ.entry → Pre env C σ s →
    (∀ t, Post σ s t → SafeN G n P t) → SafeN G n P s

def Iface.Holds (env : Env) (C : Word → Option Instr) (σ : Iface) : Prop :=
  ∀ n, σ.HoldsN env C n

/-- The unbounded form: from a state satisfying the precondition, safe if safe from every
    return. -/
theorem Iface.Holds.safe {env : Env} {C : Word → Option Instr} {σ : Iface}
    (h : σ.Holds env C) {G : MachineState → Prop} (hG : ∀ x, G x → env.Cfi x) {P : Prop}
    {s : MachineState} (hpc : s.pc = σ.entry)
    (hpre : Pre env C σ s) (hk : ∀ t, Post σ s t → Safe G P t) : Safe G P s :=
  fun n => h n G hG P s hpc hpre (fun t ht => hk t ht n)

end AsmVerif.RiscV.Check
