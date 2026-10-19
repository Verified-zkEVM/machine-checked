/-
  MachineChecked.RiscV.Check.Spec

  What an interface means, against riscv-zkvm's `stepSp1`.

  ## The judgement

  `SafeN G n P s` (`MachineChecked.RiscV.Safe`): every accepting state reached from `s` in fewer
  than `n` steps, along a run every state of which satisfies the guard `G`, satisfies `P`.
  The guard is where premises about runs go: `Env.Cfi`, the targets of the indirect jumps
  no analysis resolves. A specification is in continuation form with one budget on both
  sides; the checker's soundness uses a callee's specification at a smaller budget than its
  own, which is what makes recursion and loops compose.

  ## Memory

  Memory is `Word → Word`, keyed by doubleword address. Every store `stepSp1` performs
  writes an 8-aligned key: a doubleword store must be aligned, a narrower one rewrites
  `alignToDword addr`. So what a function leaves unchanged is stated for aligned keys. A
  key `a` is *hit* by a byte range `[b, b + l)` when the doubleword `[a, a + 8)` overlaps it,
  modulo `2^64`.
-/

import MachineChecked.RiscV.Safe
import MachineChecked.RiscV.Check.Domain
import MachineChecked.RiscV.Frame.Sound

namespace MachineChecked.RiscV.Check

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

/-! ## Accepting, and `SafeN`

`Accepted` (SP1's `HALT` with exit code `0`), `stepsSp1`, `SafeN` and `Safe` are
`MachineChecked.RiscV.Safe`, shared with the symbolic executor (`MachineChecked.RiscV.Sym`). -/

export MachineChecked.RiscV (Accepted stepSp1_halt Accepted.stuck not_accepted_of_code)

/-! ## Memory regions -/

/-- The doubleword at key `a` overlaps the bytes `[b, b + l)`, modulo `2^64`. -/
def Hits (b : Word) (l : Nat) (a : Word) : Prop :=
  (a - b).toNat < l ∨ (0 < l ∧ (b - a).toNat < 8)

def _root_.MachineChecked.RiscV.Frame.AVal.eval (E : Ent) : AVal → Word
  | .lin r k => E r + k
  | .const c => c
  | .top => 0
  | .oneOf _ => 0
  | .cell r ks k => E.deref (E r) ks + k
  | .sym i j k => E.sym i j + k

def Len.eval (E : Ent) : Len → Nat
  | .n l => l
  | .reg r => (E r).toNat
  | .regPlus r c => (E r).toNat + c

def Item.Hits (E : Ent) (it : Item) (a : Word) : Prop :=
  Check.Hits (it.base.eval E) (it.len.eval E) a

/-- The frame window of a function entered with stack pointer `e`. -/
def InWin (e : Word) (D : Nat) (a : Word) : Prop := Hits (e - BitVec.ofNat 64 D) D a

def Env.InProt (env : Env) (a : Word) : Prop := ∃ R ∈ env.prot, Hits R.1 R.2 a

def Env.InOwn (env : Env) (a : Word) : Prop := ∃ R ∈ env.own, Hits R.1 R.2 a

open Classical in
/-- The owned statics of a memory, everything else zero: all the invariant may look at. -/
noncomputable def Env.ownPart (env : Env) (m : Word → Word) (a : Word) : Word :=
  if Aligned a ∧ env.InOwn a then m a else 0

/-- The module invariant holds of a memory: of its owned statics. -/
def Env.Inv (env : Env) (m : Word → Word) : Prop := env.inv (env.ownPart m)

/-- The protected and owned regions lie above the stack and do not wrap, and no owned
    region comes within a doubleword of a protected one. -/
def Env.wf (env : Env) : Bool :=
  decide (env.stackTop + 8 ≤ 2 ^ 63) &&
  env.prot.all (fun (b, l) => decide (env.stackTop + 8 ≤ b.toNat) && decide (b.toNat + l + 8 ≤ 2 ^ 64)) &&
  env.own.all (fun (b, l) => decide (env.stackTop + 8 ≤ b.toNat) && decide (b.toNat + l + 8 ≤ 2 ^ 64) &&
    env.prot.all fun (b', l') => decide (b.toNat + l + 8 ≤ b'.toNat) || decide (b'.toNat + l' + 8 ≤ b.toNat))

/-- What a function with interface `σ`, entered with registers `E`, may write. -/
def Written (σ : Iface) (E : Ent) (a : Word) : Prop :=
  InWin (E .x2) σ.depth a ∨ ∃ it ∈ σ.foot, it.Hits E a

/-- The registers and memory of a state, as the entry valuation of a function. -/
def regsOf (s : MachineState) : Ent := { reg := s.getReg, mem := s.getMem }

/-- A postcondition's variable, from the entry state `s` and the exit state `t`. -/
def postVal (s t : MachineState) : PVal → Word
  | .ent v => v.eval (regsOf s)
  | .ret r => t.getReg r
  | .out a => t.getMem (a.eval (regsOf s))

/-- What a program's `Env` must satisfy for the typed stores: the heap is owned, and a
    store inside an allocated block keeps the module invariant. -/
def Env.Ok (env : Env) : Prop :=
  (∀ a, env.model.heap a → env.InOwn a) ∧
  ∀ m a v, env.Inv m → env.model.payload m a → env.Inv (fun b => if b = a then v else m b)

/-- A cell's address, given the entry valuation. -/
def Cell.addr (E : Ent) (c : Cell) : Word := E.deref (E c.r) c.ks + c.k

/-! ## Writers

What an interface's `strs` mean (`Check.Model`). -/

/-- A key of a writer the function was lent, as of memory `m`. -/
def StrHit (env : Env) (σ : Iface) (E : Ent) (m : Word → Word) (a : Word) : Prop :=
  ∃ e ∈ σ.strs, env.model.hit (e.2.eval E) (e.1.eval E) m a

/-- At entry: each writer is well-typed; its keys are none the function writes and none
    protected; its field keys and stable keys are aligned and not owned; and no cell is a
    writer's key. -/
def StrsPre (env : Env) (σ : Iface) (E : Ent) (m : Word → Word) : Prop :=
  (∀ e ∈ σ.strs, env.model.writerOk (e.2.eval E) (e.1.eval E) m ∧
    (∀ a, env.model.hit (e.2.eval E) (e.1.eval E) m a → ¬ Written σ E a ∧ ¬ env.InProt a) ∧
    (∀ a, env.model.stable (e.2.eval E) (e.1.eval E) m a → Aligned a ∧ ¬ env.InOwn a) ∧
    (∀ a, env.model.fields (e.2.eval E) (e.1.eval E) m a → Aligned a ∧ ¬ env.InOwn a)) ∧
  ∀ c ∈ σ.cells, ¬ StrHit env σ E m (c.addr E)

/-- At return: each writer is kept (`Model.Keeps`); and, if the function leaves the heap's
    structure alone, so is every writer whose keys it neither writes nor was lent. -/
def StrsPost (env : Env) (σ : Iface) (E : Ent) (m m' : Word → Word) : Prop :=
  (∀ e ∈ σ.strs, env.model.Keeps (e.2.eval E) (e.1.eval E) m m') ∧
  (σ.heap = false → ∀ k p, env.model.writerOk k p m →
    (∀ a, env.model.hit k p m a → ¬ Written σ E a ∧ ¬ StrHit env σ E m a) →
    (∀ a, env.model.fields k p m a → ¬ env.InOwn a) →
    (∀ a, env.model.stable k p m a → ¬ env.InOwn a) →
    env.model.Keeps k p m m')

/-- The precondition: the code is the program's; the stack has room for the window and lies
    below the program; the protected regions hold their contents; footprint items avoid the
    window and the protected regions; the `nz` values are nonzero; the `vals` registers hold
    one of their candidates; each cell is aligned, not something the function may write,
    and holds one of its candidates; the invariant holds; the writers are well-typed. -/
def Pre (env : Env) (C : Word → Option Instr) (σ : Iface) (s : MachineState) : Prop :=
  s.code = C ∧ σ.depth ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ env.stackTop ∧
  Aligned (s.getReg .x2) ∧
  (∀ a, Aligned a → env.InProt a → s.getMem a = env.init a) ∧
  (∀ it ∈ σ.foot, ∀ a, Aligned a → it.Hits (regsOf s) a →
    ¬ InWin (s.getReg .x2) σ.depth a ∧ ¬ env.InProt a ∧ ¬ env.InOwn a) ∧
  (∀ v ∈ σ.nz, v.eval (regsOf s) ≠ 0) ∧
  (∀ p ∈ σ.vals, s.getReg p.1 ∈ p.2) ∧
  (∀ c ∈ σ.cells, Aligned (c.addr (regsOf s)) ∧ ¬ Written σ (regsOf s) (c.addr (regsOf s)) ∧
    ¬ env.InOwn (c.addr (regsOf s)) ∧ ∀ cs, c.vals = some cs → s.getMem (c.addr (regsOf s)) ∈ cs) ∧
  env.Inv s.getMem ∧ StrsPre env σ (regsOf s) s.getMem ∧
  (∀ f ∈ σ.pre, f.Holds (env.model.atomIn s.getMem) (AVal.eval (regsOf s)))

/-- The postcondition: it returns, to `ra`, with the callee-saved registers restored and
    memory unchanged outside what it may write and the writers it was lent; the invariant
    holds; the writers are kept; the `post` facts hold; and if it leaves the heap's
    structure alone, the heap changed only inside the blocks allocated at entry. -/
def Post (env : Env) (σ : Iface) (s t : MachineState) : Prop :=
  σ.returns = true ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
  (∀ r ∈ savedRegs, t.getReg r = s.getReg r) ∧
  (∀ a, Aligned a → ¬ Written σ (regsOf s) a → ¬ env.InOwn a →
    ¬ StrHit env σ (regsOf s) s.getMem a → t.getMem a = s.getMem a) ∧
  t.code = s.code ∧ env.Inv t.getMem ∧ StrsPost env σ (regsOf s) s.getMem t.getMem ∧
  (∀ f ∈ σ.post, f.Holds (env.model.atomIn t.getMem) (postVal s t)) ∧
  (σ.heap = false → ∀ a, env.model.heap a → ¬ env.model.payload s.getMem a →
    t.getMem a = s.getMem a)

/-- The control-flow premise at a state: a listed `jalr` lands on one of its candidates. -/
def Env.Cfi (env : Env) (x : MachineState) : Prop :=
  ∀ p ∈ env.cfi, x.pc = p.1 → ∀ rd rs off, x.code x.pc = some (.JALR rd rs off) →
    (x.getReg rs + signExtend12 off) &&& ~~~1#64 ∈ p.2

/-- `σ` holds for budget `n`, along every run that keeps the program's control-flow
    premise (and whatever else a guard `G` asks). -/
def Iface.HoldsN (env : Env) (C : Word → Option Instr) (σ : Iface) (n : Nat) : Prop :=
  ∀ (G : MachineState → Prop), (∀ x, G x → env.Cfi x) →
  ∀ (P : Prop) (s : MachineState), s.pc = σ.entry → Pre env C σ s →
    (∀ t, Post env σ s t → SafeN G n P t) → SafeN G n P s

def Iface.Holds (env : Env) (C : Word → Option Instr) (σ : Iface) : Prop :=
  ∀ n, σ.HoldsN env C n

/-- The unbounded form: from a state satisfying the precondition, safe if safe from every
    return. -/
theorem Iface.Holds.safe {env : Env} {C : Word → Option Instr} {σ : Iface}
    (h : σ.Holds env C) {G : MachineState → Prop} (hG : ∀ x, G x → env.Cfi x) {P : Prop}
    {s : MachineState} (hpc : s.pc = σ.entry)
    (hpre : Pre env C σ s) (hk : ∀ t, Post env σ s t → Safe G P t) : Safe G P s :=
  fun n => h n G hG P s hpc hpre (fun t ht => hk t ht n)

end MachineChecked.RiscV.Check
