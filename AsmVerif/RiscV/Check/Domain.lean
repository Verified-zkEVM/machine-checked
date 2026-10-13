/-
  AsmVerif.RiscV.Check.Domain

  The contract checker: from a function's code, an untrusted annotation and the interfaces
  of its callees, a Boolean check that the function meets its own interface. Soundness
  against `stepSp1` is `Check.Sound`; what an interface *means* is `Check.Spec`.

  ## Interfaces

  An `Iface` is what a caller may rely on about a function, in terms of the registers at
  its entry (`E`):

    * `depth`: the stack it may use, callees included. Its *frame window* is
      `[E sp - depth, E sp)`.
    * `foot`: the memory outside its window that it may write, as `Item`s: `len` bytes from
      an abstract value (`a0 + 16`, a constant address), the length a constant or an entry
      register.
    * `nz`: values that must be nonzero at entry (an exit code that reaches `HALT`).
    * `returns`: whether it can return at all.
    * `strs`: the writers it is lent (`Check.Model`); `pre`, `post`: facts it needs at
      entry and gives at return; `heap`: whether it may change the heap's structure.

  Running from its entry in a state that satisfies the precondition, it does not accept,
  and if it returns it does so to `ra` with `sp`, `gp`, `tp`, `s0`-`s11` restored and
  memory outside window, footprint and writers unchanged.

  ## The checker

  It reuses `Frame`'s abstract states (entry-register-relative values, frame slots), with
  *symbols* for values known only through *facts* (`Check.Fact`): a value an instruction
  computes from unknowns is a fresh symbol with the fact that it is that operation's
  result; a branch adds the comparison it decided; certificates in the context derive
  more. A symbol is named by the instruction that made it and killed wherever it is
  remade (loops). At a jump, the target annotation's symbols named by the target are its
  own: they stand for whatever the source state has in their place.

  What a store and a call owe:

    * a store through `sp` must land in the window; a store elsewhere must be covered by a
      footprint item, be a field of a writer the function has (the field's new content is
      tracked, `wmem`), or land in a writer's buffer (`ptr ≤ a`, `a + n ≤ ptr + cap` by the
      facts; `Env.Ok` says such keys keep the module invariant);
    * a call instantiates the callee's interface with the caller's abstract registers. Its
      window must fit under the caller's, its footprint items must be covered by the
      caller's (or lie in the caller's frame, above the callee's stack pointer), its `nz`
      values must be nonzero constants or the caller's own `nz`, its `pre` facts must be
      among the caller's, and its writers must be ones the caller has, well-typed now.
      After the call the callee's return registers and the fields of the writers it was
      lent are fresh symbols, with the callee's `post` facts and the writers' invariants.
-/

import AsmVerif.RiscV.Check.Model

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

/-- An abstract state given by how it differs from the entry state: the registers listed
    take the given values, the others their entry values. The compact form certificates are
    written in. -/
def _root_.AsmVerif.RiscV.Frame.AState.ofDiff (regs : List (Reg × AVal))
    (slots : List (Word × AVal)) (facts : List (Fact AVal) := []) (wmem : List (AVal × AVal) := [])
    (fw : List (AVal × AVal) := []) : AState :=
  { regs := allRegs.map fun r => (regs.lookup r).getD (.lin r 0), slots, facts, wmem, fw }

/-- An abstract state given by its known registers; the others are unknown. -/
def _root_.AsmVerif.RiscV.Frame.AState.ofKnown (regs : List (Reg × AVal))
    (slots : List (Word × AVal)) (facts : List (Fact AVal) := []) (wmem : List (AVal × AVal) := [])
    (fw : List (AVal × AVal) := []) : AState :=
  { regs := allRegs.map fun r => (regs.lookup r).getD .top, slots, facts, wmem, fw }

/-! ## Values -/


/-- A value with one concretization: entry-relative, loaded through an entry pointer,
    constant, or a symbol. -/
def _root_.AsmVerif.RiscV.Frame.AVal.isPtr : AVal → Bool
  | .lin _ _ | .const _ | .cell _ _ _ | .sym _ _ _ => true
  | _ => false

/-- Symbol `j` of instruction `i`, at any offset. -/
def _root_.AsmVerif.RiscV.Frame.AVal.mentions (i j : Nat) : AVal → Bool
  | .sym i' j' _ => i == i' && j == j'
  | _ => false

/-- Any symbol of instruction `i`. -/
def _root_.AsmVerif.RiscV.Frame.AVal.mentionsAt (i : Nat) : AVal → Bool
  | .sym i' _ _ => i == i'
  | _ => false

def _root_.AsmVerif.RiscV.Frame.AVal.symFree : AVal → Bool
  | .sym _ _ _ => false
  | _ => true

/-- The value without its offset, and the offset. -/
def _root_.AsmVerif.RiscV.Frame.AVal.base : AVal → AVal × Word
  | .lin r k => (.lin r 0, k)
  | .const c => (.const 0, c)
  | .cell r ks k => (.cell r ks 0, k)
  | .sym i j k => (.sym i j 0, k)
  | v => (v, 0)

/-- Replace the symbols made at `j` by `θ`, keeping offsets. -/
def _root_.AsmVerif.RiscV.Frame.AVal.substSym (j : Nat) (θ : List (Nat × AVal)) : AVal → AVal
  | .sym i k off =>
    if i = j then
      match θ.lookup k with
      | some v => v.addK off
      | none => .sym i k off
    else .sym i k off
  | v => v

def _root_.AsmVerif.RiscV.Frame.AVal.constVal : AVal → Word
  | .const c => c
  | _ => 0

def _root_.AsmVerif.RiscV.Frame.AVal.isConst : AVal → Bool
  | .const _ => true
  | _ => false


/-- A value as a linear term: constants by their value. -/
def LinTerm.ofVal : AVal → LinTerm AVal
  | .const c => LinTerm.ofNat c.toNat
  | v => LinTerm.var v

def Fact.mentionsSym (i j : Nat) (f : Fact AVal) : Bool := f.any (·.mentions i j)
def Fact.mentionsAt (i : Nat) (f : Fact AVal) : Bool := f.any (·.mentionsAt i)
def Fact.symFree (f : Fact AVal) : Bool := !f.any (fun v => !v.symFree)
def Fact.substSym (j : Nat) (θ : List (Nat × AVal)) (f : Fact AVal) : Fact AVal :=
  f.map (AVal.substSym j θ)

/-! ## Footprints -/

inductive Len where
  | n (k : Nat)
  /-- The entry value of a register, as a byte count. -/
  | reg (r : Reg)
  /-- The entry value of a register plus a constant, as a byte count. -/
  | regPlus (r : Reg) (c : Nat)
  deriving DecidableEq, Repr

/-- `len` bytes from `base`. -/
structure Item where
  base : AVal
  len : Len
  deriving DecidableEq, Repr

/-- `decl` covers `it`: same base, `it` inside `decl`. -/
def Item.within (decl it : Item) : Bool :=
  decl == it ||
  match decl.base, it.base, decl.len, it.len with
  | .lin r k0, .lin r' k, .n l0, .n l => r == r' && decide ((k - k0).toNat + l ≤ l0) &&
      decide (l0 < 2 ^ 63)
  | .const c0, .const c, .n l0, .n l => decide ((c - c0).toNat + l ≤ l0) && decide (l0 < 2 ^ 63)
  | .cell r ks k0, .cell r' ks' k, .n l0, .n l => r == r' && ks == ks' &&
      decide ((k - k0).toNat + l ≤ l0) && decide (l0 < 2 ^ 63)
  | _, _, _, _ => false

/-- What every function of a program shares: the top of the stack (everything the image
    places lies above it), the protected regions (byte ranges no function may write, whose
    contents are fixed), and those contents. -/
structure Env where
  stackTop : Nat
  prot : List (Word × Nat)
  init : Word → Word
  /-- The control-flow premise (`CfiOk`): at each listed `jalr`, the target is one of the
      candidates. A premise about runs, not a theorem; `SafeN` is relative to it. -/
  cfi : List (Word × List Word) := []
  /-- Owned statics: byte ranges that functions change only through their own interfaces
      (an allocator's state, a hasher). No footprint may name them; any call may change
      them, keeping `inv`. -/
  own : List (Word × Nat) := []
  /-- The module invariant over the owned statics: every interface's precondition asks
      for it and its postcondition gives it back. Only owned keys are visible to it
      (`Env.Inv`). -/
  inv : (Word → Word) → Prop := fun _ => True
  /-- The typed resources functions may be lent (`Check.Model`). -/
  model : Model := Model.trivial

/-- An aligned doubleword key inside a protected region. -/
def Env.protKey (env : Env) (a : Word) : Bool :=
  decide (a.toNat % 8 = 0) &&
  env.prot.any fun (b, l) => decide (b.toNat ≤ a.toNat) && decide (a.toNat + 8 ≤ b.toNat + l)

/-- A doubleword reached from an entry register: from `r`'s entry value, the loads `ks` of
    the entry memory, then offset `k` (`a0 + 8`; or the second field of the struct `a1`
    points to's first field: `r = a1`, `ks = [0]`, `k = 8`). As a premise: it is aligned,
    the activation does not write it, and with `vals`, it holds one of them. -/
structure Cell where
  r : Reg
  ks : List Word := []
  k : Word
  vals : Option (List Word) := none
  deriving DecidableEq, Repr

/-- A variable of a postcondition: an entry value, the exit value of a register, or the
    doubleword at an entry-relative address at exit. -/
inductive PVal where
  | ent (v : AVal)
  | ret (r : Reg)
  | out (a : AVal)
  deriving DecidableEq, Repr, Inhabited

structure Iface where
  entry : Word
  depth : Nat
  foot : List Item := []
  nz : List AVal := []
  returns : Bool := true
  /-- Registers whose entry value is one of the listed constants: a function pointer or a
      vtable among candidates (the control-flow premise of an indirect call). -/
  vals : List (Reg × List Word) := []
  /-- Doublewords of the entry memory the function reads and relies on staying put. -/
  cells : List Cell := []
  /-- The writers the function is lent: each a pointer and a kind (`Env.model`), in terms
      of the entry registers. At entry they are well-typed; at return they are again. -/
  strs : List (AVal × AVal) := []
  /-- Facts over the entry values the function needs. -/
  pre : List (Fact AVal) := []
  /-- Facts it gives at return. -/
  post : List (Fact PVal) := []
  /-- Whether it may change the heap's structure (allocate or free). -/
  heap : Bool := false
  deriving DecidableEq, Repr

/-- The value of a declared cell: the symbolic load. Its candidates, if declared, are
    found from it (`cands`): the value keeps saying where it came from. -/
def cellVal (σ : Iface) (r : Reg) (ks : List Word) (k : Word) : Option AVal :=
  if σ.cells.any fun c => c.r == r && c.ks == ks && c.k == k then some (.cell r (ks ++ [k]) 0)
  else none

/-- The doubleword at an entry-memory address, if it is one of the function's cells. -/
def cellAt (σ : Iface) : AVal → Option AVal
  | .lin r k => cellVal σ r [] k
  | .cell r ks d => cellVal σ r ks d
  | _ => none

/-- The content of the doubleword at an address: the symbolic load. -/
def _root_.AsmVerif.RiscV.Frame.AVal.cellOf : AVal → Option AVal
  | .lin r k => some (.cell r [k] 0)
  | .cell r ks d => some (.cell r (ks ++ [d]) 0)
  | _ => none

/-- A path of loads from a value. -/
def _root_.AsmVerif.RiscV.Frame.AVal.path : AVal → List Word → Option AVal
  | v, [] => some v
  | .lin r k, k1 :: ks => some (.cell r ((k + k1) :: ks) 0)
  | .cell r ks0 d, k1 :: ks => some (.cell r (ks0 ++ ((d + k1) :: ks)) 0)
  | _, _ => none

/-! ### Candidates

A value that is one of finitely many constants: the candidates of a `vals` register, of a
cell with candidates, or of a load through such a value from protected memory (a vtable
slot). The *root* is where the candidates come from; the value is a path of loads from it,
and under the hypothesis that the root is one candidate the value is determined. -/

/-- The declared candidates of a cell. -/
def cellCands (σ : Iface) (r : Reg) (ks : List Word) (k : Word) : Option (List Word) :=
  (σ.cells.find? fun c => c.r == r && c.ks == ks && c.k == k).bind (·.vals)

/-- The longest prefix of a path that is a cell with candidates. -/
def rootGo (σ : Iface) (r : Reg) : List Word → Option (AVal × List Word) → List Word →
    Option (AVal × List Word)
  | _, best, [] => best
  | pre, best, k :: ks =>
      rootGo σ r (pre ++ [k]) (match cellCands σ r pre k with
        | some cs => some (.cell r (pre ++ [k]) 0, cs)
        | none => best) ks

/-- The root of a value's candidates, with them. -/
def root? (σ : Iface) : AVal → Option (AVal × List Word)
  | .lin r _ => (σ.vals.lookup r).map fun cs => (.lin r 0, cs)
  | .cell r ks _ => rootGo σ r [] ((σ.vals.lookup r).map fun cs => (.lin r 0, cs)) ks
  | .const c => some (.const c, [c])
  | .oneOf cs => some (.oneOf cs, cs)
  | .top => none
  | .sym _ _ _ => none

/-- Follow a path of loads through protected memory. -/
def derefProt (env : Env) : Word → List Word → Option Word
  | a, [] => some a
  | a, k :: ks => if env.protKey (a + k) then derefProt env (env.init (a + k)) ks else none

/-- The value, given that its root (`ref.1`) is the constant `ref.2`. -/
def refineVal (env : Env) (ref : AVal × Word) (v : AVal) : Option Word :=
  if v = ref.1 then some ref.2 else
  match ref.1 with
  | .lin r k0 =>
    if k0 = 0 then
      match v with
      | .lin r' k => if r = r' then some (ref.2 + k) else none
      | .cell r' ks d => if r = r' then (derefProt env ref.2 ks).map (· + d) else none
      | _ => none
    else none
  | .cell r ks0 d0 =>
    if d0 = 0 then
      match v with
      | .cell r' ks d =>
        if r = r' ∧ ks0.isPrefixOf ks then
          (derefProt env ref.2 (ks.drop ks0.length)).map (· + d)
        else none
      | _ => none
    else none
  | _ => none

/-- What a function knows about its writers, under a refinement (`Ctx.fanOut`) at a call:
    the writers available (its own, and the one each structural writer wraps); the stable
    doublewords along the wrapped writers' paths (address, content); the kinds of the
    wrapped writers; and which writer each wrapped one belongs to. -/
structure Kn where
  strs : List (AVal × AVal) := []
  cells : List (AVal × AVal) := []
  roots : List (AVal × List Word) := []
  subs : List ((AVal × AVal) × (AVal × AVal)) := []

/-- A value's root and candidates, the knowledge's first. -/
def rootK (σ : Iface) (kn : Kn) (v : AVal) : Option (AVal × List Word) :=
  match kn.roots.lookup v with
  | some cs => some (v, cs)
  | none => root? σ v

/-- The candidates of a value. -/
def cands (env : Env) (σ : Iface) (kn : Kn) (v : AVal) : Option (List Word) :=
  (rootK σ kn v).bind fun (root, cs) => cs.mapM fun c => refineVal env (root, c) v

/-- A value is one of `cs`. -/
def inCands (env : Env) (σ : Iface) (kn : Kn) (v : AVal) (cs : List Word) : Bool :=
  match cands env σ kn v with
  | some ws => ws.all cs.contains
  | none => false

/-! ## Frames

A frame offset is a negative `Word` `k`, `m = -k` bytes below the entry stack pointer. -/

def negOff (k : Word) : Nat := (0 - k).toNat

/-- The bytes of a store that determine the doubleword it rewrites: all 8 of a doubleword
    store; for a narrower one, its first byte (its doubleword is `alignToDword` of it). -/
def wbytes : Width → Nat
  | .d => 8
  | .sub => 1

/-- A store of width `w` at frame offset `k` lands in a window of `D` bytes. -/
def winOk (D : Nat) (k : Word) (w : Width) : Bool :=
  decide (wbytes w ≤ negOff k) && decide (negOff k ≤ D)

/-! ## Facts and symbols -/

/-- The facts true of the values by what they are: a constant's value, the offset of a
    value from its base, and a frame address's distance from the top of the stack. -/
def axOk (env : Env) (σ : Iface) : Fact AVal → Bool
  | .le ⟨[(.const c, 1)], 0⟩ ⟨[], n⟩ => n == c.toNat
  | .le ⟨[], n⟩ ⟨[(.const c, 1)], 0⟩ => n == c.toNat
  | .le ⟨[(.lin .x2 k, 1)], m⟩ ⟨[], n⟩ =>
      m == negOff k && decide (negOff k ≤ σ.depth) && n == env.stackTop
  | .op .add v [b, .const off] => v.isPtr && (b, off) == v.base
  | .le l r => l == r
  | _ => false

/-- The theory certificates run in: the model's rules and the axioms. -/
def thy (env : Env) (σ : Iface) : Thy AVal := { rules := env.model.rules, ax := axOk env σ }


/-- Forget everything that mentions symbol `j` of instruction `i`: before it is remade. -/
def _root_.AsmVerif.RiscV.Frame.AState.kill (i j : Nat) (A : AState) : AState :=
  { regs := A.regs.map fun v => if v.mentions i j then .top else v
    slots := A.slots.filter fun p => !p.2.mentions i j
    facts := A.facts.filter fun f => !f.mentionsSym i j
    wmem := A.wmem.filter fun p => !(p.1.mentions i j || p.2.mentions i j)
    fw := A.fw }

/-- Forget everything that mentions a symbol of instruction `i`: before they are remade. -/
def _root_.AsmVerif.RiscV.Frame.AState.killAll (i : Nat) (A : AState) : AState :=
  { regs := A.regs.map fun v => if v.mentionsAt i then .top else v
    slots := A.slots.filter fun p => !p.2.mentionsAt i
    facts := A.facts.filter fun f => !f.mentionsAt i
    wmem := A.wmem.filter fun p => !(p.1.mentionsAt i || p.2.mentionsAt i)
    fw := A.fw }

def _root_.AsmVerif.RiscV.Frame.AState.addFacts (A : AState) (fs : List (Fact AVal)) : AState := { A with facts := A.facts ++ fs }

/-- Replace the symbols made at `j`. -/
def _root_.AsmVerif.RiscV.Frame.AState.subst (j : Nat) (θ : List (Nat × AVal)) (A : AState) : AState :=
  { regs := A.regs.map (AVal.substSym j θ)
    slots := A.slots.map fun p => (p.1, p.2.substSym j θ)
    facts := A.facts.map (·.substSym j θ)
    wmem := A.wmem.map fun p => (p.1.substSym j θ, p.2.substSym j θ)
    fw := A.fw }


/-- What the symbols made at `j` in `C` stand for in `B`: the value `B` has where `C` has
    the symbol, in a register or a slot. -/
def phiOf (j : Nat) (B C : AState) : List (Nat × AVal) :=
  (allRegs.filterMap fun r => match C.get r with
    | .sym i k off => if i = j ∧ (B.get r).isPtr then some (k, (B.get r).addK (0 - off)) else none
    | _ => none) ++
  C.slots.filterMap fun p => match p.2 with
    | .sym i k off =>
      if i = j then (B.slots.lookup p.1).bind fun v =>
        if v.isPtr then some (k, v.addK (0 - off)) else none
      else none
    | _ => none

/-- `B ≤ C` as the state at instruction `j`: every fact of `C`, its symbols standing for
    what `B` has in their place, is a fact of `B`. -/
def leAt (j : Nat) (B C : AState) : Bool :=
  let C := C.subst j (phiOf j B C)
  allRegs.all (fun r => (B.get r).le (C.get r)) &&
  C.slots.all (fun p => B.slots.contains p) &&
  C.facts.all B.facts.contains &&
  C.wmem.all (fun p => B.wmem.any fun q => q.1 == p.1 && q.2.le p.2) &&
  C.fw.all B.fw.contains

/-! ## Straight-line instructions -/

/-- The value a load produces: a frame slot, a protected doubleword, or unknown. -/
def loadVal (env : Env) (σ : Iface) (kn : Kn) (A : AState) (b : AVal) (isD : Bool) : AVal :=
  if isD then
    match b.frameOff? with
    | some k => (A.slots.lookup k).getD .top
    | none => match b with
      | .const c => if env.protKey c then .const (env.init c) else .top
      | .oneOf cs => if cs.all env.protKey then .oneOf (cs.map env.init) else .top
      | b => match cellAt σ b with
        | some v => v
        | none => match kn.cells.lookup b with
          -- a stable doubleword of one of the function's writers
          | some v => v
          | none => match A.wmem.lookup b with
            -- a field of a writer, as last stored
            | some v => v
            -- a load through a value with candidates, all protected: the symbolic load, whose
            -- candidates follow
            | none => match cands env σ kn b with
              | some cs => if cs.all env.protKey then b.cellOf.getD .top else .top
              | none => .top
  else .top

/-- What a narrow unsigned load is bounded by. -/
def loadBound (i : Instr) (s : AVal) : List (Fact AVal) :=
  match i with
  | .LBU _ _ _ => [.le (.var s) (.ofNat 255)]
  | .LHU _ _ _ => [.le (.var s) (.ofNat 65535)]
  | .LWU _ _ _ => [.le (.var s) (.ofNat (2 ^ 32 - 1))]
  | _ => []

/-- The operation an ALU instruction computes, with its operands in `A`. -/
def aluOp (A : AState) : Instr → Option (Reg × Op × List AVal)
  | .ADD rd rs1 rs2 => some (rd, .add, [A.get rs1, A.get rs2])
  | .ADDI rd rs imm => some (rd, .add, [A.get rs, .const (signExtend12 imm)])
  | .SUB rd rs1 rs2 => some (rd, .sub, [A.get rs1, A.get rs2])
  | .AND rd rs1 rs2 => some (rd, .and, [A.get rs1, A.get rs2])
  | .ANDI rd rs imm => some (rd, .and, [A.get rs, .const (signExtend12 imm)])
  | .OR rd rs1 rs2 => some (rd, .or, [A.get rs1, A.get rs2])
  | .ORI rd rs imm => some (rd, .or, [A.get rs, .const (signExtend12 imm)])
  | .XOR rd rs1 rs2 => some (rd, .xor, [A.get rs1, A.get rs2])
  | .XORI rd rs imm => some (rd, .xor, [A.get rs, .const (signExtend12 imm)])
  | .SLTU rd rs1 rs2 => some (rd, .sltu, [A.get rs1, A.get rs2])
  | .SLTIU rd rs imm => some (rd, .sltu, [A.get rs, .const (signExtend12 imm)])
  | .SLT rd rs1 rs2 => some (rd, .slt, [A.get rs1, A.get rs2])
  | .SLTI rd rs imm => some (rd, .slt, [A.get rs, .const (signExtend12 imm)])
  | .SLLI rd rs sh => some (rd, .shl sh.toNat, [A.get rs])
  | .SRLI rd rs sh => some (rd, .shr sh.toNat, [A.get rs])
  | .SRAI rd rs sh => some (rd, .sra sh.toNat, [A.get rs])
  | .SLL rd rs1 rs2 => match A.get rs2 with
    | .const c => some (rd, .shl (c.toNat % 64), [A.get rs1])
    | _ => none
  | .SRL rd rs1 rs2 => match A.get rs2 with
    | .const c => some (rd, .shr (c.toNat % 64), [A.get rs1])
    | _ => none
  | .SRA rd rs1 rs2 => match A.get rs2 with
    | .const c => some (rd, .sra (c.toNat % 64), [A.get rs1])
    | _ => none
  | .MUL rd rs1 rs2 => some (rd, .mul, [A.get rs1, A.get rs2])
  | .MULHU rd rs1 rs2 => some (rd, .mulhu, [A.get rs1, A.get rs2])
  | .DIVU rd rs1 rs2 => some (rd, .divu, [A.get rs1, A.get rs2])
  | .REMU rd rs1 rs2 => some (rd, .remu, [A.get rs1, A.get rs2])
  | .ADDIW rd rs imm => some (rd, .addw, [A.get rs, .const (signExtend12 imm)])
  | .SUBW rd rs1 rs2 => some (rd, .subw, [A.get rs1, A.get rs2])
  | .SLLIW rd rs sh => some (rd, .shlw sh.toNat, [A.get rs])
  | .SRLIW rd rs sh => some (rd, .shrw sh.toNat, [A.get rs])
  | .SRLW rd rs1 rs2 => match A.get rs2 with
    | .const c => some (rd, .shrw (c.toNat % 32), [A.get rs1])
    | _ => none
  | _ => none

/-- An ALU instruction: `Frame`'s value if it has one; else the operation on constants;
    else a fresh symbol with the operation as a fact, if the operands are known. -/
def aluStep (pc : Word) (A : AState) (i : Instr) : Option AState :=
  match aluResult pc A i with
  | none => none
  | some (rd, v) =>
    if v != .top then some (A.set rd v) else
    match aluOp A i with
    | none => some (A.set rd .top)
    | some (_, o, args) =>
      if args.all AVal.isConst then some (A.set rd (.const (o.eval (args.map AVal.constVal))))
      else
        let A := A.kill pc.toNat 0
        match aluOp A i with
        | some (_, o, args) =>
          if args.all AVal.isPtr then
            let s := AVal.sym pc.toNat 0 0
            some ((A.set rd s).addFacts [.op o s args])
          else some (A.set rd .top)
        | none => some (A.set rd .top)

/-- A load: its value if known, else a fresh symbol, bounded if the load is narrow. -/
def loadStep (env : Env) (σ : Iface) (kn : Kn) (pc : Word) (A : AState) (i : Instr) (rd rs : Reg)
    (off : BitVec 12) (isD : Bool) : AState :=
  let v := loadVal env σ kn A ((A.get rs).addK (signExtend12 off)) isD
  if v != .top then A.set rd v else
  let A := A.kill pc.toNat 0
  let s := AVal.sym pc.toNat 0 0
  (A.set rd s).addFacts (loadBound i s)

/-! ### Writers' fields -/

/-- The kind a constant denotes. -/
def kindOf (env : Env) : AVal → Option Kind
  | .const K => env.model.kinds K
  | _ => none

/-- The kind a value denotes, under the refinement. -/
def kindConst (env : Env) (ref : Option (AVal × Word)) (k : AVal) : Option Word :=
  match k with
  | .const c => some c
  | k => ref.bind fun rf => refineVal env rf k

/-- The current content of the writer's field at `addr`: a slot, or a tracked field. -/
def fieldAt (A : AState) (addr : AVal) : Option AVal :=
  match addr.frameOff? with
  | some f => A.slots.lookup f
  | none => A.wmem.lookup addr

/-- The current values of the writer's fields, if all known. -/
def writerFields (A : AState) (d : AVal) (kd : Kind) : Option (List AVal) :=
  kd.fields.mapM fun off => (fieldAt A (d.addK off)).bind fun v => if v.isPtr then some v else none

/-- A kind's invariant over a writer's pointer and field values. -/
def instInv (kd : Kind) (d : AVal) (vals : List AVal) : List (Fact AVal) :=
  kd.inv.map (·.map fun j => if j = 0 then d else vals.getD (j - 1) .top)

/-- The kinds a writer's kind value may denote: the constant, the refinement's, or the
    candidates. -/
def writerKinds (env : Env) (σ : Iface) (kn : Kn) (ref : Option (AVal × Word)) (k : AVal) :
    Option (List Word) :=
  match k with
  | .const K => some [K]
  | _ => match kindConst env ref k with
    | some K => some [K]
    | none => cands env σ kn k

/-- The writer is well-typed now: for each kind it may have, a structural kind wraps a
    writer the function has that is well-typed now; a unit needs nothing; any other kind
    has its fields known and its invariant among the facts. -/
def writerOkNow (env : Env) (σ : Iface) (kn : Kn) (ref : Option (AVal × Word)) (A : AState) :
    Nat → AVal × AVal → Bool
  | 0, _ => false
  | fuel + 1, e =>
    match writerKinds env σ kn ref e.2 with
    | none => false
    | some Ks => Ks.all fun K => match env.model.kinds K with
      | none => false
      | some kd =>
        if kd.pure then
          match kd.sub with
          | none => true
          | some s => match e.1.path s.dp, e.1.path s.kp with
            | some d', some k' =>
              kn.strs.contains (d', k') && writerOkNow env σ kn ref A fuel (d', k')
            | _, _ => false
        else kd.sub.isNone && match writerFields A e.1 kd with
          | some vals => (instInv kd e.1 vals).all A.facts.contains
          | none => false

/-- A frame slot: aligned, within the window. -/
def slotOk (σ : Iface) (f : Word) : Bool :=
  decide (negOff f % 8 = 0) && decide (8 ≤ negOff f) && decide (negOff f ≤ σ.depth)

/-- A frame address, aligned, within the window. -/
def frameAddrOk (σ : Iface) (d : AVal) : Bool :=
  match d.frameOff? with
  | some f => slotOk σ f
  | none => false

/-- The frame writers of a state are frame addresses of non-structural kinds. -/
def fwOk (env : Env) (σ : Iface) (A : AState) : Bool :=
  A.fw.all fun e => frameAddrOk σ e.1 && match kindOf env e.2 with
    | some kd => !kd.pure && kd.sub.isNone
    | none => false

/-! ### Stores -/

/-- A store at a writer's field: the field's new content is tracked; every other tracked
    field that may be the same doubleword is forgotten (the writers' pointers may alias). -/
def fieldStore (env : Env) (σ : Iface) (A : AState) (b : AVal) (w : Width) (v : AVal) :
    Option AState :=
  if w != .d ∨ σ.strs.length > 1 then none else
  if σ.strs.any (fun e => match kindOf env e.2 with
      | some kd => !kd.pure && kd.sub.isNone && e.1.isPtr && e.1.base.1 == b.base.1 &&
          kd.fields.contains (b.base.2 - e.1.base.2) && !kd.stable.contains (b.base.2 - e.1.base.2)
      | none => false) then
    let kept := A.wmem.filter fun p => p.1 != b && p.1.base.1 == b.base.1
    some { A with wmem := if v.isPtr then (b, v) :: kept else kept }
  else none

/-- A store into the buffer of the writer `e`: `ptr ≤ a` and `a + n ≤ ptr + cap` are among
    the facts, the writer well-typed now. -/
def bufStore (env : Env) (σ : Iface) (kn : Kn) (A : AState) (b : AVal) (w : Width)
    (e : AVal × AVal) : Bool :=
  (kn.strs.contains e || A.fw.contains e) && writerOkNow env σ kn none A 4 e &&
  match kindOf env e.2 with
  | some kd => match kd.buf, writerFields A e.1 kd with
    | some (pi, ci), some vals =>
      match vals[pi]?, vals[ci]? with
      | some ptr, some cap =>
        A.facts.contains (.le (LinTerm.ofVal ptr) (LinTerm.ofVal b)) &&
        A.facts.contains (.le (LinTerm.ofVal b + LinTerm.ofNat (wbytes w))
          (LinTerm.ofVal ptr + LinTerm.ofVal cap))
      | _, _ => false
    | _, _ => false
  | none => false

/-- A store: through the frame (slots updated), covered by the footprint, at a writer's
    field, or into a writer's buffer (the writer named by the hint). `none` if none. -/
def storeStep (env : Env) (σ : Iface) (kn : Kn) (A : AState) (rs1 rs2 : Reg) (off : BitVec 12)
    (w : Width) (wtr : Option (AVal × AVal)) : Option AState :=
  let b := (A.get rs1).addK (signExtend12 off)
  match b.frameOff? with
  | some k =>
      if winOk σ.depth k w then
        let kept := A.slots.filter (fun p => !mayHit w k p.1)
        let new := match w, A.get rs2 with
          | .d, .top => kept
          | .d, v => if negOff k % 8 = 0 then (k, v) :: kept else kept
          | .sub, _ => kept
        some { A with slots := new }
      else none
  | none =>
      if !b.isPtr then none
      else if σ.foot.any (·.within { base := b, len := .n (wbytes w) }) then some A
      else match fieldStore env σ A b w (A.get rs2) with
        | some B => some B
        | none => match wtr with
          | some e => if bufStore env σ kn A b w e then some A else none
          | none => none

def plainStep (env : Env) (σ : Iface) (kn : Kn) (pc : Word) (A : AState) (i : Instr)
    (wtr : Option (AVal × AVal) := none) : Option AState :=
  match aluStep pc A i with
  | some B => some B
  | none =>
  match loadOf i with
  | some (rd, rs, off, isD) => some (loadStep env σ kn pc A i rd rs off isD)
  | none =>
  match storeOf i with
  | some (rs1, rs2, off, w) => storeStep env σ kn A rs1 rs2 off w wtr
  | none =>
  match i with
  | .NOP | .FENCE => some A
  | _ => none

/-! ### Branches -/

/-- The facts a conditional branch decides: when taken, and when not. -/
def branchFacts (A : AState) : Instr → List (Fact AVal) × List (Fact AVal)
  | .BLTU rs1 rs2 _ => cmp (A.get rs1) (A.get rs2) fun u v =>
      ([.le (u + .ofNat 1) v], [.le v u])
  | .BGEU rs1 rs2 _ => cmp (A.get rs1) (A.get rs2) fun u v =>
      ([.le v u], [.le (u + .ofNat 1) v])
  | .BEQ rs1 rs2 _ => cmp (A.get rs1) (A.get rs2) fun u v =>
      ([.le u v, .le v u], [])
  | .BNE rs1 rs2 _ => cmp (A.get rs1) (A.get rs2) fun u v =>
      ([], [.le u v, .le v u])
  | _ => ([], [])
where
  cmp (a b : AVal) (k : LinTerm AVal → LinTerm AVal → List (Fact AVal) × List (Fact AVal)) :
      List (Fact AVal) × List (Fact AVal) :=
    if a.isPtr && b.isPtr then k (LinTerm.ofVal a) (LinTerm.ofVal b) else ([], [])

/-! ## Calls -/

/-- The current contents of a doubleword the caller knows: a frame slot, one of its cells,
    a stable doubleword of a writer it was lent, or a tracked field. -/
def contentAt (σ : Iface) (kn : Kn) (A : AState) (a : AVal) : Option AVal :=
  match a.frameOff? with
  | some f => A.slots.lookup f
  | none => match cellAt σ a with
    | some v => some v
    | none => match kn.cells.lookup a with
      | some v => some v
      | none => A.wmem.lookup a

/-- Follow a callee's path of loads from a caller value. -/
def instPath (σ : Iface) (kn : Kn) (A : AState) : AVal → List Word → Option AVal
  | v, [] => some v
  | v, k :: ks => (contentAt σ kn A (v.addK k)).bind (instPath σ kn A · ks)

/-- A callee's value, in the caller's terms. -/
def instVal (σ : Iface) (kn : Kn) (A : AState) : AVal → AVal
  | .lin r k => (A.get r).addK k
  | .cell r ks d => ((instPath σ kn A (A.get r) ks).map (·.addK d)).getD .top
  | .sym _ _ _ => .top
  | v => v

def instLen (A : AState) : Len → Option Len
  | .n l => some (.n l)
  | .reg r => match A.get r with
    | .const c => some (.n c.toNat)
    | .lin r' k => if k = 0 then some (.reg r') else none
    | _ => none
  | .regPlus r c => match A.get r with
    | .const v => some (.n (v.toNat + c))
    | .lin r' k => if k = 0 then some (.regPlus r' c) else none
    | _ => none

def instItem (σ : Iface) (kn : Kn) (A : AState) (it : Item) : Option Item :=
  (instLen A it.len).map fun l => { base := instVal σ kn A it.base, len := l }

/-- An instantiated callee item, checked against the caller. A frame-based item must lie
    in the caller's frame, at or above the callee's stack pointer (`m` bytes below the
    caller's entry `sp`); anything else must be covered by the caller's footprint. -/
def itemOk (σ : Iface) (m : Nat) (it : Item) : Bool :=
  match it.base.frameOff?, it.len with
  | some k, .n l => decide (l ≤ negOff k) && decide (negOff k ≤ m) && decide (m ≤ σ.depth)
  | some _, _ => false
  | none, _ => it.base.isPtr && σ.foot.any (·.within it)

/-- A frame slot `k` cannot be written by a callee item. -/
def slotClear (k : Word) (it : Item) : Bool :=
  match it.base.frameOff?, it.len with
  | some k', .n l => decide (negOff k' ≤ negOff k - 8) || decide (negOff k + l ≤ negOff k')
  | some _, _ => false
  | none, _ => true

/-- A value known nonzero: a nonzero constant, or one of the function's own `nz`. -/
def nzVal (σ : Iface) : AVal → Bool
  | .const c => c != 0
  | .lin r k => σ.nz.contains (.lin r k)
  | .top => false
  | .oneOf cs => cs.all (· != 0)
  | .cell r ks k => σ.nz.contains (.cell r ks k)
  | .sym _ _ _ => false

/-- A callee's `nz` value, in the caller's terms, is nonzero. `σ` is the caller. -/
def nzOk (σ : Iface) (kn : Kn) (A : AState) (v : AVal) : Bool :=
  v.isPtr && nzVal σ (instVal σ kn A v)

/-- A callee's `pre` fact, in the caller's terms, is among the caller's facts. -/
def preOk (σ : Iface) (kn : Kn) (A : AState) (f : Fact AVal) : Bool :=
  f.symFree && (f.map (instVal σ kn A)).any (fun v => !v.isPtr) == false &&
  A.facts.contains (f.map (instVal σ kn A))

/-- The callee-saved registers: `sp`, `gp`, `tp`, `s0`-`s11`. -/
def savedRegs : List Reg :=
  [.x2, .x3, .x4, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- A callee's `vals` premise, discharged by the caller's value: its candidates are among
    the callee's. -/
def valOk (env : Env) (σ : Iface) (kn : Kn) (A : AState) (p : Reg × List Word) : Bool :=
  inCands env σ kn (A.get p.1) p.2

/-- The doubleword at `a` stays put while the callee runs, and its contents: a caller frame
    slot at or above the callee's stack pointer (`m` bytes below the caller's entry `sp`)
    that no callee item hits, or one of the caller's cells. A tail call (`m = none`) has
    no frame left. -/
def stableAt (σ : Iface) (A : AState) (m : Option Nat) (its : List Item) (a : AVal) :
    Option AVal :=
  match a.frameOff? with
  | some f => match m with
    | some m => if negOff f ≤ m && its.all (slotClear f) then A.slots.lookup f else none
    | none => none
  | none => cellAt σ a

/-- A callee's cell premise, discharged by the caller. A frame slot the callee's writers
    are built from (`fs`) is not a cell: the callee may rely on it only as a writer's. -/
def cellOk (env : Env) (σ : Iface) (kn : Kn) (fs : List Word) (A : AState) (m : Option Nat)
    (its : List Item) (c : Cell) : Bool :=
  match instPath σ kn A (A.get c.r) c.ks with
  | none => false
  | some v =>
    let a := v.addK c.k
    (match a.frameOff? with
      | some f => !fs.contains f
      | none => true) &&
    match stableAt σ A m its a with
    | none => false
    | some w => match c.vals with
      | none => true
      | some cs => inCands env σ kn w cs

/-- The stack pointer is `m` bytes below its entry value, `m` a multiple of 8. -/
def spOff (A : AState) : Option Nat :=
  match (A.get .x2).frameOff? with
  | some k => if negOff k % 8 = 0 then some (negOff k) else none
  | none => none

/-! ### Writers

A callee's writer, in the caller's terms, must be one the caller has (`Kn.strs`: lent to
it, or wrapped by one lent to it, its kind refined; or built in its frame, `AState.fw`), or
a structural writer the caller builds in its frame around one it has (`passEntry`); it
must be well-typed now. After the call, every writer of the caller must be *recovered*:
given back by the callee, or wrapping one given back (`recov`); or the callee has no
writers, and gives back every writer it was not lent. -/

/-- The stable doublewords along a path from a value: address, content. -/
def pathCells : AVal → List Word → List (AVal × AVal)
  | _, [] => []
  | v, k :: ks => match v.path [k] with
    | some u => (v.addK k, u) :: pathCells u ks
    | none => []

/-- The writer a structural writer wraps: the sub-writer, its pointer and its kind. -/
def subEntry (env : Env) (ref : Option (AVal × Word)) (e : AVal × AVal) :
    Option (Sub × AVal × AVal) :=
  match (kindConst env ref e.2).bind env.model.kinds with
  | none => none
  | some kd =>
    if kd.pure then
      match kd.sub with
      | none => none
      | some s => match e.1.path s.dp, e.1.path s.kp with
        | some d', some k' => some (s, d', k')
        | _, _ => none
    else none

/-- A writer, and the one it wraps if its kind is structural. -/
def addEntry (env : Env) (ref : Option (AVal × Word)) (kn : Kn) (e : AVal × AVal) : Kn :=
  match subEntry env ref e with
  | none => { kn with strs := e :: kn.strs }
  | some (s, d', k') =>
    { strs := (d', k') :: e :: kn.strs,
      cells := kn.cells ++ pathCells e.1 s.dp ++ pathCells e.1 s.kp,
      roots := (k', s.kinds) :: kn.roots,
      subs := ((d', k'), e) :: kn.subs }

/-- What the function knows under a refinement. -/
def closure (env : Env) (σ : Iface) (ref : Option (AVal × Word)) : Kn :=
  σ.strs.foldl (addEntry env ref) {}

/-- A writer the caller has stands for a callee's: same pointer, and the kind the same or
    refined to the callee's constant. -/
def matchEntry (env : Env) (ref : Option (AVal × Word)) (e e' : AVal × AVal) : Bool :=
  e.1 == e'.1 && (e.2 == e'.2 || match kindConst env ref e.2 with
    | some K => e'.2 == .const K
    | none => false)

/-- Follow a path through the caller's frame, at or above the callee's stack pointer and
    clear of its items: the content, and the slots read. -/
def framePath (A : AState) (m : Nat) (its : List Item) : AVal → List Word →
    Option (AVal × List Word)
  | v, [] => some (v, [])
  | v, k :: ks => match (v.addK k).frameOff? with
    | some f =>
      if negOff f ≤ m && its.all (slotClear f) then
        match A.slots.lookup f with
        | some u => (framePath A m its u ks).map fun (w, fs) => (w, f :: fs)
        | none => none
      else none
    | none => none

/-- The frame slots a frame writer's fields are in. -/
def fieldSlots (d : AVal) (kd : Kind) : List Word :=
  kd.fields.filterMap fun off => (d.addK off).frameOff?

/-- A callee writer `(d, k)`, in the caller's terms: the caller's writers it is lent (whose
    fields it may change), and the frame slots it is built from. Directly one of the
    caller's, well-typed now; a frame writer of the caller; or a structural writer built in
    the caller's frame around one of them. -/
def passEntry (env : Env) (σ : Iface) (kn : Kn) (ref : Option (AVal × Word)) (A : AState)
    (m : Option Nat) (its : List Item) (d k : AVal) : Option (List (AVal × AVal) × List Word) :=
  match kn.strs.find? (matchEntry env ref · (d, k)) with
  | some e => if writerOkNow env σ kn ref A 4 e then some ([e], []) else none
  | none => match k, m with
    | .const K, some m =>
      match env.model.kinds K with
      | some kd =>
        if kd.pure then
          match kd.sub with
          | some s =>
            match framePath A m its d s.dp, framePath A m its d s.kp with
            | some (d2, fs1), some (k2, fs2) =>
              match kn.strs.find? (matchEntry env ref · (d2, k2)) with
              | some e =>
                if inCands env σ kn k2 s.kinds && writerOkNow env σ kn ref A 4 e then
                  some ([e], fs1 ++ fs2)
                else none
              | none => none
            | _, _ => none
          -- a unit: nothing to pass, as long as it is a frame address
          | none => match d.frameOff? with
            | some f => if negOff f % 8 = 0 then some ([], []) else none
            | none => none
        else
          -- a frame writer of the caller: its fields are slots the callee may change
          if A.fw.contains (d, k) && writerOkNow env σ kn ref A 4 (d, k) then
            let fs := fieldSlots d kd
            if fs.all (fun f => negOff f ≤ m && its.all (slotClear f)) then some ([(d, k)], fs)
            else none
          else none
      | none => none
    | _, _ => none

/-- A caller writer is recovered after the call: given back, or wrapping one given back
    (and then the callee was given nothing else). -/
def recov (env : Env) (ref : Option (AVal × Word)) (kn : Kn) (passed : List (AVal × AVal)) :
    Nat → AVal × AVal → Bool
  | 0, e => passed.contains e
  | fuel + 1, e =>
    passed.contains e ||
    match subEntry env ref e with
    | some (_, d2, k2) =>
      recov env ref kn passed fuel (d2, k2) && passed.all fun p => kn.subs.contains (p, e)
    | none => false

/-- The callee's writers are the caller's, and the caller's are recovered: the writers
    lent, and the frame slots the callee's writers are built from. -/
def strsOk (env : Env) (σ : Iface) (kn : Kn) (ref : Option (AVal × Word)) (A : AState)
    (m : Option Nat) (its : List Item) (g : Iface) : Option (List (AVal × AVal) × List Word) :=
  match g.strs.mapM fun e =>
      passEntry env σ kn ref A m its (instVal σ kn A e.1) (instVal σ kn A e.2) with
  | none => none
  | some ps =>
    let passed := (ps.map (·.1)).flatten
    if g.strs.isEmpty || σ.strs.all (recov env ref kn passed 2) then
      some (passed, (ps.map (·.2)).flatten)
    else none

/-- What a call established: the callee's stack pointer offset, its items in the caller's
    terms, and the caller's writers it was lent. -/
structure CallOut where
  m : Nat
  its : List Item
  lent : List (AVal × AVal)

/-- A call to `g` from a state `A`, under a refinement `ref` of the state: the callee's
    precondition, instantiated. -/
def callOk (env : Env) (σ : Iface) (A : AState) (g : Iface) (ref : Option (AVal × Word)) :
    Option CallOut :=
  let kn := closure env σ ref
  match spOff A with
  | none => none
  | some m =>
    if m + g.depth ≤ σ.depth && (!g.heap || σ.heap) then
      match g.foot.mapM (instItem σ kn A) with
      | none => none
      | some its =>
        match strsOk env σ kn ref A (some m) its g with
        | none => none
        | some (lent, fs) =>
          if its.all (itemOk σ m) && g.nz.all (nzOk σ kn A) && g.vals.all (valOk env σ kn A) &&
              g.cells.all (cellOk env σ kn fs A (some m) its) && g.pre.all (preOk σ kn A) then
            some ⟨m, its, lent⟩
          else none
    else none

/-! ### After a call

The callee-saved registers are kept, and the slots the callee cannot write. The return
registers, the fields of the writers lent, and the doublewords the callee's `post` names
are fresh symbols; the lent writers' invariants and the `post` facts, instantiated, are
added. Atoms survive unless the callee may change the heap. Tracked fields of writers not
lent are forgotten: the writers' pointers may alias. -/

/-- The symbols a call makes, in order: `a0`, `a1`, the lent writers' fields, the `post`'s
    `out` doublewords. Each with where it goes. -/
inductive FreshAt where
  | reg (r : Reg)
  | slot (f : Word)
  | field (a : AVal)
  deriving DecidableEq, Repr

def outAddrs (g : Iface) : List AVal :=
  (g.post.flatMap fun f => match f with
    | .le l r => (l.coeffs.map (·.1)) ++ (r.coeffs.map (·.1))
    | .op _ x args => x :: args
    | .atom _ args => args).filterMap (fun v => match v with
      | .out a => some a
      | _ => none) |>.eraseDups

/-- The fresh symbols of a call at `pc`: targets, in order. A field in the frame window is
    a slot; any other is a tracked field. An `out` doubleword is named only in the window. -/
def freshList (env : Env) (σ : Iface) (kn : Kn) (A : AState) (g : Iface) (lent : List (AVal × AVal)) :
    List FreshAt :=
  [.reg .x10, .reg .x11] ++
  (lent.flatMap fun e => match kindOf env e.2 with
    | some kd => kd.fields.map fun off => match (e.1.addK off).frameOff? with
      | some f => if slotOk σ f then .slot f else .field (e.1.addK off)
      | none => .field (e.1.addK off)
    | none => []) ++
  (outAddrs g).filterMap fun a => match (instVal σ kn A a).frameOff? with
    | some f => if slotOk σ f then some (.slot f) else none
    | none => none

/-- The fresh symbol standing for a target, if any. -/
def freshFor (n : Nat) (fl : List FreshAt) (t : FreshAt) : Option AVal :=
  (fl.idxOf? t).map fun j => .sym n j 0

/-- The symbol standing for a target: `.top` if none. -/
def freshOf (n : Nat) (fl : List FreshAt) (t : FreshAt) : AVal := (freshFor n fl t).getD .top

/-- A `post` variable in the caller's terms, after the call. -/
def postVar (σ : Iface) (kn : Kn) (A : AState) (n : Nat) (fl : List FreshAt) : PVal → Option AVal
  | .ent v => let w := instVal σ kn A v; if w.isPtr then some w else none
  | .ret r => freshFor n fl (.reg r)
  | .out a => match (instVal σ kn A a).frameOff? with
    | some f => freshFor n fl (.slot f)
    | none => none

/-- A `post` fact in the caller's terms, if all its variables are nameable. -/
def instPost (σ : Iface) (kn : Kn) (A : AState) (n : Nat) (fl : List FreshAt) (f : Fact PVal) :
    Option (Fact AVal) :=
  let g := f.map fun p => (postVar σ kn A n fl p).getD .top
  if g.any (fun v => !v.isPtr) then none else some g

/-- The registers after a call: the return registers fresh, the callee-saved ones kept. -/
def callRegs (n : Nat) (fl : List FreshAt) (A : AState) : List AVal :=
  allRegs.map fun r =>
    if r = .x10 ∨ r = .x11 then freshOf n fl (.reg r)
    else if savedRegs.contains r then A.get r else .top

/-- The slots after a call: those the callee cannot write, with the fresh ones in place. -/
def callSlots (n : Nat) (fl : List FreshAt) (co : CallOut) (A : AState) : List (Word × AVal) :=
  fl.foldl (fun sl t => match t with
    | .slot f => (f, freshOf n fl t) :: sl.filter (·.1 != f)
    | _ => sl)
    (A.slots.filter fun p => decide (negOff p.1 ≤ co.m) && co.its.all (slotClear p.1))

/-- The tracked fields a call makes. -/
def callFresh (n : Nat) (fl : List FreshAt) : List (AVal × AVal) :=
  fl.filterMap fun t => match t with
    | .field a => some (a, freshOf n fl t)
    | _ => none

/-- The tracked fields after a call: the fresh ones; the old ones survive only if every
    writer lent is one built in the frame, which no other writer can alias. -/
def callWmem (n : Nat) (fl : List FreshAt) (kn : Kn) (co : CallOut) (A : AState) :
    List (AVal × AVal) :=
  let fresh' := callFresh n fl
  if co.lent.all (fun e => A.fw.contains e && !kn.strs.contains e) then
    fresh' ++ A.wmem.filter (fun p => !(fresh'.any (·.1 == p.1))) else fresh'

/-- The lent writers' invariants over their fields after the call. -/
def callInvs (env : Env) (co : CallOut) (A : AState) : List (Fact AVal) :=
  co.lent.flatMap fun e => match kindOf env e.2 with
    | some kd => match writerFields A e.1 kd with
      | some vals => instInv kd e.1 vals
      | none => []
    | none => []

/-- The state after a call at `pc` returns. The call's symbols are first forgotten (a
    loop may run it again). -/
def afterCall (env : Env) (σ : Iface) (kn : Kn) (pc : Word) (A : AState) (co : CallOut) (g : Iface) :
    AState :=
  let n := pc.toNat
  let A := A.killAll n
  let fl := freshList env σ kn A g co.lent
  let slots := callSlots n fl co A
  let wmem := callWmem n fl kn co A
  let posts := g.post.filterMap (instPost σ kn A n fl)
  let facts := (if g.heap then A.facts.filter (fun f => match f with
      | .atom i _ => env.model.fixed i
      | _ => true)
    else A.facts) ++ callInvs env co { A with slots, wmem } ++ posts
  { regs := callRegs n fl A, slots, facts, wmem, fw := A.fw }

def okExit (A : AState) : Bool :=
  A.get .x1 == .lin .x1 0 && savedRegs.all fun r => A.get r == .lin r 0

/-- A `post` variable at the function's own return. -/
def retVar (σ : Iface) (kn : Kn) (A : AState) : PVal → Option AVal
  | .ent v => if v.isPtr && v.symFree then some v else none
  | .ret r => let v := A.get r; if v.isPtr then some v else none
  | .out a => if a.isPtr && a.symFree then (contentAt σ kn A a).bind fun v =>
      if v.isPtr then some v else none else none

/-- At return: every writer the function has is well-typed, and its `post` facts hold. -/
def retOk (env : Env) (σ : Iface) (kn : Kn) (A : AState) : Bool :=
  σ.strs.all (writerOkNow env σ kn none A 4) &&
  σ.post.all fun f => match f.mapM (retVar σ kn A) with
    | some g => A.facts.contains g
    | none => false

/-- A tail call: `f` leaves for `g` with every callee-saved register and `ra` restored, and
    `g`'s footprint covered by `f`'s; `f` promises no `post` facts, its writers are well-typed
    now, and if it has any, `g` either takes writers or leaves the heap's structure alone. -/
def tailOk (env : Env) (σ : Iface) (A : AState) (g : Iface) (ref : Option (AVal × Word)) : Bool :=
  let kn := closure env σ ref
  okExit A && decide (g.depth ≤ σ.depth) && (σ.returns || !g.returns) && (!g.heap || σ.heap) &&
  σ.post.isEmpty && σ.strs.all (writerOkNow env σ kn ref A 4) &&
  (σ.strs.isEmpty || !g.heap || !g.strs.isEmpty) &&
  match g.foot.mapM (instItem σ kn A) with
  | none => false
  | some its => its.all (fun it => it.base.frameOff?.isNone && it.base.isPtr &&
      σ.foot.any (·.within it)) && g.nz.all (nzOk σ kn A) && g.vals.all (valOk env σ kn A) &&
      g.cells.all (cellOk env σ kn [] A none its) && g.pre.all (preOk σ kn A) &&
      (strsOk env σ kn ref A none its g).isSome

/-! ## Syscalls

`ecall` dispatches on `t0`, as SP1 does (`sp1Ecall`): a precompile writes its result over
the operand at `a0`; `HINT_LEN` writes `t0`; `HINT_READ` writes the hint at `a0`, `a1 + 8`
bytes at most; `COMMIT` and `COMMIT_DEFERRED_PROOFS` write no memory or register; `HALT`
stops, and must not accept: its exit code must be known nonzero; `WRITE` writes no memory;
`read_input` writes the doublewords at `a0` and `a1`; any other id traps. -/

/-- The doublewords a precompile writes at `a0`, for those with a fixed-size result. -/
def accelLen (t : Word) : Option Nat :=
  if t = Sp1.SECP256K1_ADD ∨ t = Sp1.SECP256K1_DOUBLE ∨ t = Sp1.PALLAS_ADD ∨
      t = Sp1.PALLAS_DOUBLE ∨ t = Sp1.BN254_ADD ∨ t = Sp1.BN254_DOUBLE ∨
      t = Sp1.BN254_FP2_ADD ∨ t = Sp1.BN254_FP2_SUB ∨ t = Sp1.BN254_FP2_MUL then some 8
  else if t = Sp1.BLS12381_ADD ∨ t = Sp1.BLS12381_DOUBLE ∨ t = Sp1.BLS12381_FP2_ADD ∨
      t = Sp1.BLS12381_FP2_SUB ∨ t = Sp1.BLS12381_FP2_MUL then some 12
  else if t = Sp1.UINT256_MUL then some 4
  else none

/-- The byte count of a value, plus `c`, as a footprint length. -/
def lenPlus (v : AVal) (c : Nat) : Option Len :=
  match v with
  | .const n => some (.n (n.toNat + c))
  | .lin r k => if k = 0 then some (.regPlus r c) else none
  | _ => none

inductive SysOut where
  /-- No successor: a halt with a nonzero exit code, or a trap. -/
  | stop
  /-- Continue at `pc + 4` in this state, having written these items. -/
  | next (B : AState) (its : List Item)

def sysStep (σ : Iface) (A : AState) : Option SysOut :=
  match A.get .x5 with
  | .const t =>
    if Sp1.isAccelId t then
      (accelLen t).map fun L => .next A [⟨A.get .x10, .n (8 * L)⟩]
    else if t = Sp1.HINT_LEN then some (.next (A.set .x5 .top) [])
    else if t = Sp1.HINT_READ then
      (lenPlus (A.get .x11) 8).map fun l => .next A [⟨A.get .x10, l⟩]
    else if t = Sp1.COMMIT ∨ t = Sp1.COMMIT_DEFERRED_PROOFS then some (.next A [])
    else if t = 0 then (if nzVal σ (A.get .x10) then some .stop else none)
    else if t = 2 then some (.next A [])
    else if t = 0xF2 then some (.next A [⟨A.get .x10, .n 8⟩, ⟨A.get .x11, .n 8⟩])
    else some .stop
  | _ => none

/-! ## Control flow -/

inductive Edge where
  | goto (j : Nat) (A : AState)
  | ret (A : AState)

/-- What the checker needs besides the function: its interface, its callees', the
    program's `Env`, and the certificates: at `(pc, pc)` the proofs to run before the
    instruction at `pc`, at `(pc, tgt)` those to run on the edge from `pc` to `tgt`; and
    the writer whose buffer the store at `pc` writes. -/
structure Ctx where
  env : Env
  tbl : List Iface
  σ : Iface
  f : Fn
  certs : List ((Word × Word) × List (Proof AVal)) := []
  wtr : List (Word × (AVal × AVal)) := []
  /-- The writers built in the frame: at `pc`, the writer is in place (its fields are
      slots, its invariant among the facts). -/
  fws : List (Word × (AVal × AVal)) := []

def Ctx.lookup (c : Ctx) (pc : Word) : Option Iface := c.tbl.find? (·.entry == pc)

/-- The frame writer declared at `pc`, added. -/
def Ctx.withFw (c : Ctx) (pc : Word) (A : AState) : AState :=
  match c.fws.lookup pc with
  | some e => { A with fw := e :: A.fw }
  | none => A

/-- Run the certificate at `key`. -/
def Ctx.saturate (c : Ctx) (key : Word × Word) (A : AState) : AState :=
  match c.certs.lookup key with
  | some pfs => { A with facts := Proof.runAll (thy c.env c.σ) A.facts pfs }
  | none => A

/-- A jump from `pc` to `tgt`: pruned if the facts on the edge are contradictory; inside
    the function; or a tail call (under a refinement, for an indirect one). -/
def Ctx.jump (c : Ctx) (pc : Word) (A : AState) (tgt : Word) (ref : Option (AVal × Word) := none) :
    Option (List Edge) :=
  let A := c.saturate (pc, tgt) A
  if A.facts.contains falseFact then some [] else
  match c.f.idx? tgt with
  | some j => some [.goto j A]
  | none => match c.lookup tgt with
    | some g => if tailOk c.env c.σ A g ref then some [] else none
    | none => none

/-- A call to `tgt` returning to `pc + 4`. The callee is entered with `ra = pc + 4`, so its
    interface is instantiated in `A` with that link. -/
def Ctx.call (c : Ctx) (pc : Word) (A : AState) (tgt : Word) (ref : Option (AVal × Word) := none) :
    Option (List Edge) :=
  match c.lookup tgt with
  | none => none
  | some g => match callOk c.env c.σ (A.set .x1 (.const (pc + 4))) g ref with
    | none => none
    | some co =>
      if g.returns then
        if (pc + 4) &&& ~~~1#64 = pc + 4 then
          match c.f.idx? (pc + 4) with
          | some j => some [.goto j (afterCall c.env c.σ (closure c.env c.σ ref) pc
              (A.set .x1 (.const (pc + 4))) co g)]
          | none => none
        else none
      else some []

/-- Every candidate target's edges. -/
def allEdges (f : Word → Option (List Edge)) (ts : List Word) : Option (List Edge) :=
  (ts.mapM f).map List.flatten

/-- The edges of an indirect jump or call through a value with candidates: for each
    candidate of the value's root, the target it determines, under that refinement. -/
def fanOut (env : Env) (σ : Iface) (v : AVal) (off : BitVec 12)
    (k : Option (AVal × Word) → Word → Option (List Edge)) : Option (List Edge) :=
  match root? σ v with
  | some (root, cs) =>
    (cs.mapM fun c => (refineVal env (root, c) v).bind fun t =>
      k (some (root, c)) ((t + signExtend12 off) &&& ~~~1#64)).map List.flatten
  | none => none

/-- Abstractly run an outlined fragment (straight-line prologue or epilogue code) to its
    `jalr zero, 0(t0)`. -/
def Ctx.runFrag (c : Ctx) (A : AState) (fbase : Word) : List (Option Instr) → Nat → Option AState
  | [], _ => none
  | some i :: rest, n =>
      if i = .JALR .x0 .x5 0 then some A else
      match plainStep c.env c.σ (closure c.env c.σ none) (fbase + BitVec.ofNat 64 (4 * n)) A i with
      | none => none
      | some B => c.runFrag B fbase rest (n + 1)
  | none :: _, _ => none

def Ctx.outlined (c : Ctx) (pc : Word) (A : AState) (off : BitVec 12) : Option (List Edge) :=
  match A.get .x5 with
  | .const t =>
      let tgt := (t + signExtend12 off) &&& ~~~1#64
      match c.f.frags.lookup tgt, c.f.idx? (pc + 4) with
      | some fp, some j =>
          match c.runFrag (A.set .x5 (.const (pc + 4))) tgt fp 0 with
          | some B =>
              if B.get .x5 = .const (pc + 4) ∧ (pc + 4) &&& ~~~1#64 = pc + 4 then
                some [.goto j B]
              else none
          | none => none
      | _, _ => none
  | _ => none

/-- One instruction at `pc` from abstract state `A`. `none`: the checker rejects it. An
    undecodable word traps (`stepSp1` has no step there), so it has no successors. -/
def Ctx.stepAt (c : Ctx) (pc : Word) (oi : Option Instr) (A : AState) : Option (List Edge) :=
  match oi with
  | none => some []
  | some ins =>
  let A := c.withFw pc (c.saturate (pc, pc) A)
  if !fwOk c.env c.σ A then none else
  match branchOff? ins with
  | some off => do
      let (ft, ff) := branchFacts A ins
      let e1 ← c.jump pc (A.addFacts ff) (pc + 4)
      let e2 ← c.jump pc (A.addFacts ft) (pc + signExtend13 off)
      pure (e1 ++ e2)
  | none =>
  match ins with
  | .JAL rd off =>
      if rd = .x0 then c.jump pc A (pc + signExtend21 off)
      else if rd = .x1 then c.call pc A (pc + signExtend21 off)
      else none
  | .JALR rd rs off =>
      if rd = .x0 then
        if rs = .x1 ∧ off = 0 then
          (if c.σ.returns && retOk c.env c.σ (closure c.env c.σ none) A then some [.ret A] else none)
        else match fanOut c.env c.σ (A.get rs) off (fun ref t => c.jump pc A t ref) with
          | some es => some es
          -- an unresolved target: the candidates of the control-flow premise, if listed
          | none => (c.env.cfi.lookup pc).bind (allEdges fun t => c.jump pc A t)
      else if rd = .x1 then
        match fanOut c.env c.σ (A.get rs) off (fun ref t => c.call pc A t ref) with
        | some es => some es
        | none => (c.env.cfi.lookup pc).bind (allEdges fun t => c.call pc A t)
      else if rd = .x5 ∧ rs = .x5 then c.outlined pc A off
      else none
  | .EBREAK => some []
  | .ECALL =>
      match sysStep c.σ A with
      | some .stop => some []
      | some (.next B its) =>
          if its.all (itemOk c.σ c.σ.depth) then
            c.jump pc { B with slots := B.slots.filter fun p => its.all (slotClear p.1) } (pc + 4)
          else none
      | none => none
  | ins => (plainStep c.env c.σ (closure c.env c.σ none) pc A ins (c.wtr.lookup pc)).bind
      fun B => c.jump pc B (pc + 4)

def Ctx.step (c : Ctx) (i : Nat) (A : AState) : Option (List Edge) :=
  match c.f.prog[i]? with
  | none => none
  | some oi => c.stepAt (c.f.pcOf i) oi A

/-! ## The check

An annotation gives each instruction the states it may be reached in: a list, so that a
loop whose variable takes a few constant values can be checked one value at a time. -/

def annoAt (anno : Array (List AState)) (i : Nat) : List AState := (anno[i]?).getD []

/-- The writers with fields the function has, with their kinds. -/
def entryWs (env : Env) (σ : Iface) : List ((AVal × AVal) × Kind) :=
  (closure env σ none).strs.filterMap fun e => match kindOf env e.2 with
    | some kd => if kd.pure then none else some (e, kd)
    | none => none

/-- Their fields' entry cells. -/
def entryWmem (env : Env) (σ : Iface) : List (AVal × AVal) :=
  (entryWs env σ).flatMap fun (e, kd) => kd.fields.filterMap fun off =>
    ((e.1.addK off).cellOf).map fun v => (e.1.addK off, v)

def entryBase (env : Env) (σ : Iface) : AState :=
  { regs := allRegs.map fun r => match σ.vals.lookup r with
      | some cs => .oneOf cs
      | none => .lin r 0
    slots := [], facts := σ.pre, wmem := entryWmem env σ }

/-- The writers' invariants over their entry cells. -/
def entryInvs (env : Env) (σ : Iface) : List (Fact AVal) :=
  (entryWs env σ).flatMap fun (e, kd) => match writerFields (entryBase env σ) e.1 kd with
    | some vals => instInv kd e.1 vals
    | none => []

/-- The abstract state at entry: every register its own entry value, except those `vals`
    restricts to a set of constants; the `pre` facts; the fields of the writers and their
    invariants. -/
def Iface.entryState (env : Env) (σ : Iface) : AState :=
  (entryBase env σ).addFacts (entryInvs env σ)

def Ctx.edgeOk (c : Ctx) (anno : Array (List AState)) : Edge → Bool
  | .goto j B => (annoAt anno j).any fun C => B == C || leAt (c.f.pcOf j).toNat B C
  | .ret B => okExit B

def Ctx.instrOk (c : Ctx) (anno : Array (List AState)) (i : Nat) : Bool :=
  (annoAt anno i).all fun A => match c.step i A with
    | none => false
    | some es => es.all (c.edgeOk anno)

/-- The interface mentions no symbols. -/
def Iface.symFree (σ : Iface) : Bool :=
  σ.foot.all (·.base.symFree) && σ.nz.all AVal.symFree &&
  σ.strs.all (fun e => e.1.symFree && e.2.symFree) && σ.pre.all Fact.symFree

/-- The interface is well-formed for the `Env`: constant footprint items lie above the
    stack and outside the protected regions are the caller's business; here only that
    lengths are sane. -/
def Ctx.valid (c : Ctx) (anno : Array (List AState)) : Bool :=
  c.σ.strs.all (fun e => e.1.isPtr && e.2.isPtr) && c.σ.symFree &&
  c.f.base == c.σ.entry &&
  (annoAt anno 0).any (leAt c.f.base.toNat (c.σ.entryState c.env) ·) &&
  (List.range c.f.prog.length).all (c.instrOk anno)

end AsmVerif.RiscV.Check

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

/-! ## Sparse certificates

A certificate need only give states where straight-line propagation from the previous
instruction would not: at join points and loop heads. `Ctx.fill` recomputes the rest by
running the checker's own step along fall-through edges. The checker then checks the
filled annotation like any other, so nothing about `fill` needs to be trusted. -/

def fallStates (j : Nat) : List Edge → List AState
  | [] => []
  | .goto j' B :: es => if j' = j then B :: fallStates j es else fallStates j es
  | .ret _ :: es => fallStates j es

def Ctx.fillGo (c : Ctx) : Nat → List (Option Instr) → List AState → List (Nat × List AState) →
    List (List AState)
  | _, [], _, _ => []
  | i, oi :: ps, cur, hints =>
    let (st, hints') := match hints with
      | (j, As) :: hs => if j = i then (As, hs) else (cur, hints)
      | [] => (cur, [])
    let next := st.flatMap fun A => match c.stepAt (c.f.pcOf i) oi A with
      | some es => fallStates (i + 1) es
      | none => []
    st :: c.fillGo (i + 1) ps next hints'

def Ctx.fill (c : Ctx) (hints : List (Nat × List AState)) : Array (List AState) :=
  (c.fillGo 0 c.f.prog [] hints).toArray

/-! ## The check in one pass

`Ctx.valid` indexes program and annotation by position: quadratic in the kernel.
`Ctx.validFast` walks both together; only jumps index. `validFast_sound` (`Check.Fast`)
shows it implies `Ctx.valid`. -/

def Ctx.edgeOkAt (c : Ctx) (anno : Array (List AState)) (i : Nat) (next : List AState) :
    Edge → Bool
  | .goto j B =>
      if j = i + 1 then next.any fun C => B == C || leAt (c.f.pcOf j).toNat B C
      else c.edgeOk anno (.goto j B)
  | .ret B => okExit B

def Ctx.walk (c : Ctx) (anno : Array (List AState)) :
    Nat → List (Option Instr) → List (List AState) → Bool
  | i, oi :: ps, a :: as =>
      a.all (fun A => match c.stepAt (c.f.pcOf i) oi A with
        | none => false
        | some es => es.all (c.edgeOkAt anno i (as.head?.getD []))) &&
      c.walk anno (i + 1) ps as
  | _, _, _ => true

def Ctx.validFast (c : Ctx) (anno : Array (List AState)) : Bool :=
  c.σ.strs.all (fun e => e.1.isPtr && e.2.isPtr) && c.σ.symFree &&
  c.f.base == c.σ.entry &&
  (annoAt anno 0).any (leAt c.f.base.toNat (c.σ.entryState c.env) ·) &&
  anno.size == c.f.prog.length && c.walk anno 0 c.f.prog anno.toList

end AsmVerif.RiscV.Check
