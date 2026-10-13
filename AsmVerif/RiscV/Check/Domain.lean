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

  Running from its entry in a state that satisfies the precondition, it does not accept,
  and if it returns it does so to `ra` with `sp`, `gp`, `tp`, `s0`-`s11` restored and
  memory outside window and footprint unchanged.

  ## The checker

  It reuses `Frame`'s abstract states (entry-register-relative values, frame slots). The
  differences from `Frame` are what a store and a call owe:

    * a store through `sp` must land in the window; any other store must be covered by a
      footprint item. Nothing else: the precondition says footprint items avoid the window,
      so no store can hit a frame slot; and they avoid the `Env`'s protected regions, so
      those keep their load-time contents;
    * a call instantiates the callee's interface with the caller's abstract registers. Its
      window must fit under the caller's, its footprint items must be covered by the
      caller's (or lie in the caller's frame, above the callee's stack pointer), and its
      `nz` values must be nonzero constants or the caller's own `nz`. Slots outside
      everything the callee may write survive the call.
-/

import AsmVerif.RiscV.Check.Model

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

/-- An abstract state given by how it differs from the entry state: the registers listed
    take the given values, the others their entry values. The compact form certificates are
    written in. -/
def _root_.AsmVerif.RiscV.Frame.AState.ofDiff (regs : List (Reg × AVal))
    (slots : List (Word × AVal)) : AState :=
  { regs := allRegs.map fun r => (regs.lookup r).getD (.lin r 0), slots }

/-- An abstract state given by its known registers; the others are unknown. -/
def _root_.AsmVerif.RiscV.Frame.AState.ofKnown (regs : List (Reg × AVal))
    (slots : List (Word × AVal)) : AState :=
  { regs := allRegs.map fun r => (regs.lookup r).getD .top, slots }

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
  deriving DecidableEq, Repr

/-- The abstract state at entry: every register its own entry value, except those `vals`
    restricts to a set of constants. -/
def Iface.entryState (σ : Iface) : AState :=
  { regs := allRegs.map fun r => match σ.vals.lookup r with
      | some cs => .oneOf cs
      | none => .lin r 0
    slots := [] }

/-- A value that can be a store's base or a footprint item's: entry-relative, loaded through
    an entry pointer, or constant. -/
def _root_.AsmVerif.RiscV.Frame.AVal.isPtr : AVal → Bool
  | .lin _ _ | .const _ | .cell _ _ _ => true
  | _ => false

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
          -- a load through a value with candidates, all protected: the symbolic load, whose
          -- candidates follow
          | none => match cands env σ kn b with
            | some cs => if cs.all env.protKey then b.cellOf.getD .top else .top
            | none => .top
  else .top

/-- A store: through the frame (slots updated), or covered by the footprint. `none` if
    neither. -/
def storeStep (σ : Iface) (A : AState) (rs1 rs2 : Reg) (off : BitVec 12) (w : Width) :
    Option AState :=
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
      else none

def plainStep (env : Env) (σ : Iface) (kn : Kn) (pc : Word) (A : AState) (i : Instr) :
    Option AState :=
  match aluResult pc A i with
  | some (rd, v) => some (A.set rd v)
  | none =>
  match loadOf i with
  | some (rd, rs, off, isD) =>
      some (A.set rd (loadVal env σ kn A ((A.get rs).addK (signExtend12 off)) isD))
  | none =>
  match storeOf i with
  | some (rs1, rs2, off, w) => storeStep σ A rs1 rs2 off w
  | none =>
  match i with
  | .NOP | .FENCE => some A
  | _ => none

/-! ## Calls -/

/-- The current contents of a doubleword the caller knows: a frame slot, one of its cells,
    or a stable doubleword of a writer it was lent. -/
def contentAt (σ : Iface) (kn : Kn) (A : AState) (a : AVal) : Option AVal :=
  match a.frameOff? with
  | some f => A.slots.lookup f
  | none => match cellAt σ a with
    | some v => some v
    | none => kn.cells.lookup a

/-- Follow a callee's path of loads from a caller value. -/
def instPath (σ : Iface) (kn : Kn) (A : AState) : AVal → List Word → Option AVal
  | v, [] => some v
  | v, k :: ks => (contentAt σ kn A (v.addK k)).bind (instPath σ kn A · ks)

/-- A callee's value, in the caller's terms. -/
def instVal (σ : Iface) (kn : Kn) (A : AState) : AVal → AVal
  | .lin r k => (A.get r).addK k
  | .cell r ks d => ((instPath σ kn A (A.get r) ks).map (·.addK d)).getD .top
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

/-- A callee's `nz` value, in the caller's terms, is nonzero. `σ` is the caller. -/
def nzOk (σ : Iface) (kn : Kn) (A : AState) (v : AVal) : Bool :=
  v.isPtr && nzVal σ (instVal σ kn A v)

/-- The callee-saved registers: `sp`, `gp`, `tp`, `s0`-`s11`. -/
def savedRegs : List Reg :=
  [.x2, .x3, .x4, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The state after a call returns: callee-saved registers kept, the slots it cannot
    write. -/
def afterCall (A : AState) (m : Nat) (its : List Item) : AState :=
  { regs := allRegs.map (fun r => if savedRegs.contains r then A.get r else .top),
    slots := A.slots.filter fun p => decide (negOff p.1 ≤ m) && its.all (slotClear p.1) }

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
it, or wrapped by one lent to it, its kind refined), or a structural writer the caller
builds in its frame around one it has (`passEntry`). After the call, every writer of the
caller must be *recovered*: given back by the callee, or wrapping one given back
(`recov`); or the callee has no writers, and gives back every writer it was not lent. -/

/-- The kind a value denotes, under the refinement. -/
def kindConst (env : Env) (ref : Option (AVal × Word)) (k : AVal) : Option Word :=
  match k with
  | .const c => some c
  | k => ref.bind fun rf => refineVal env rf k

/-- The stable doublewords along a path from a value: address, content. -/
def pathCells : AVal → List Word → List (AVal × AVal)
  | _, [] => []
  | v, k :: ks => match v.path [k] with
    | some u => (v.addK k, u) :: pathCells u ks
    | none => []

/-- The writer a structural writer wraps: the sub-writer, its pointer and its kind. -/
def subEntry (env : Env) (ref : Option (AVal × Word)) (e : AVal × AVal) :
    Option (Sub × AVal × AVal) :=
  match (kindConst env ref e.2).bind env.model.sub with
  | none => none
  | some s => match e.1.path s.dp, e.1.path s.kp with
    | some d', some k' => some (s, d', k')
    | _, _ => none

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

/-- A callee writer `(d, k)`, in the caller's terms: the caller's writers it stands on,
    and the frame slots it is built from. Directly one of them, or a structural writer
    built in the caller's frame around one of them. -/
def passEntry (env : Env) (σ : Iface) (kn : Kn) (ref : Option (AVal × Word)) (A : AState)
    (m : Option Nat) (its : List Item) (d k : AVal) : Option (List (AVal × AVal) × List Word) :=
  match kn.strs.find? (matchEntry env ref · (d, k)) with
  | some e => some ([e], [])
  | none => match k, m with
    | .const K, some m =>
      match env.model.sub K with
      | some s =>
        match framePath A m its d s.dp, framePath A m its d s.kp with
        | some (d2, fs1), some (k2, fs2) =>
          match kn.strs.find? (matchEntry env ref · (d2, k2)) with
          | some e => if inCands env σ kn k2 s.kinds then some ([e], fs1 ++ fs2) else none
          | none => none
        | _, _ => none
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
    passed, and the frame slots the callee's writers are built from. -/
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

/-- A call to `g` from a state `A`, under a refinement `ref` of the state: the callee's
    precondition, instantiated. Returns the items it may write, in the caller's terms. -/
def callOk (env : Env) (σ : Iface) (A : AState) (g : Iface) (ref : Option (AVal × Word)) :
    Option (Nat × List Item) :=
  let kn := closure env σ ref
  match spOff A with
  | none => none
  | some m =>
    if m + g.depth ≤ σ.depth then
      match g.foot.mapM (instItem σ kn A) with
      | none => none
      | some its =>
        match strsOk env σ kn ref A (some m) its g with
        | none => none
        | some (_, fs) =>
          if its.all (itemOk σ m) && g.nz.all (nzOk σ kn A) && g.vals.all (valOk env σ kn A) &&
              g.cells.all (cellOk env σ kn fs A (some m) its) then some (m, its)
          else none
    else none

def okExit (A : AState) : Bool :=
  A.get .x1 == .lin .x1 0 && savedRegs.all fun r => A.get r == .lin r 0

/-- A tail call: `f` leaves for `g` with every callee-saved register and `ra` restored, and
    `g`'s footprint covered by `f`'s. -/
def tailOk (env : Env) (σ : Iface) (A : AState) (g : Iface) (ref : Option (AVal × Word)) : Bool :=
  let kn := closure env σ ref
  okExit A && decide (g.depth ≤ σ.depth) && (σ.returns || !g.returns) &&
  match g.foot.mapM (instItem σ kn A) with
  | none => false
  | some its => its.all (fun it => it.base.frameOff?.isNone && it.base.isPtr &&
      σ.foot.any (·.within it)) && g.nz.all (nzOk σ kn A) && g.vals.all (valOk env σ kn A) &&
      g.cells.all (cellOk env σ kn [] A none its) && (strsOk env σ kn ref A none its g).isSome

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

/-- What the checker needs besides the function: its interface, its callees', and the
    program's `Env`. -/
structure Ctx where
  env : Env
  tbl : List Iface
  σ : Iface
  f : Fn

def Ctx.lookup (c : Ctx) (pc : Word) : Option Iface := c.tbl.find? (·.entry == pc)

/-- A jump to `pc`: inside the function, or a tail call (under a refinement, for an
    indirect one). -/
def Ctx.jump (c : Ctx) (A : AState) (pc : Word) (ref : Option (AVal × Word) := none) :
    Option (List Edge) :=
  match c.f.idx? pc with
  | some j => some [.goto j A]
  | none => match c.lookup pc with
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
    | some (m, its) =>
      if g.returns then
        if (pc + 4) &&& ~~~1#64 = pc + 4 then
          match c.f.idx? (pc + 4) with
          | some j => some [.goto j (afterCall A m its)]
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
  match branchOff? ins with
  | some off => do
      let e1 ← c.jump A (pc + 4)
      let e2 ← c.jump A (pc + signExtend13 off)
      pure (e1 ++ e2)
  | none =>
  match ins with
  | .JAL rd off =>
      if rd = .x0 then c.jump A (pc + signExtend21 off)
      else if rd = .x1 then c.call pc A (pc + signExtend21 off)
      else none
  | .JALR rd rs off =>
      if rd = .x0 then
        if rs = .x1 ∧ off = 0 then (if c.σ.returns then some [.ret A] else none)
        else match fanOut c.env c.σ (A.get rs) off (fun ref t => c.jump A t ref) with
          | some es => some es
          -- an unresolved target: the candidates of the control-flow premise, if listed
          | none => (c.env.cfi.lookup pc).bind (allEdges fun t => c.jump A t)
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
            c.jump { B with slots := B.slots.filter fun p => its.all (slotClear p.1) } (pc + 4)
          else none
      | none => none
  | ins => (plainStep c.env c.σ (closure c.env c.σ none) pc A ins).bind fun B => c.jump B (pc + 4)

def Ctx.step (c : Ctx) (i : Nat) (A : AState) : Option (List Edge) :=
  match c.f.prog[i]? with
  | none => none
  | some oi => c.stepAt (c.f.pcOf i) oi A

/-! ## The check -/

def edgeOk (anno : Array (Option AState)) : Edge → Bool
  | .goto j B => match Fn.annoAt anno j with
      | some C => B.le C
      | none => false
  | .ret B => okExit B

def Ctx.instrOk (c : Ctx) (anno : Array (Option AState)) (i : Nat) : Bool :=
  match Fn.annoAt anno i with
  | none => true
  | some A => match c.step i A with
    | none => false
    | some es => es.all (edgeOk anno)

/-- The interface is well-formed for the `Env`: constant footprint items lie above the
    stack and outside the protected regions are the caller's business; here only that
    lengths are sane. -/
def Ctx.valid (c : Ctx) (anno : Array (Option AState)) : Bool :=
  c.σ.strs.all (fun e => e.1.isPtr && e.2.isPtr) &&
  c.f.base == c.σ.entry &&
  (match Fn.annoAt anno 0 with
    | some A => c.σ.entryState.le A
    | none => false) &&
  (List.range c.f.prog.length).all (c.instrOk anno)

end AsmVerif.RiscV.Check

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

/-! ## Sparse certificates

A certificate need only give a state where straight-line propagation from the previous
instruction would not: at join points and loop heads. `Ctx.fill` recomputes the rest by
running the checker's own step along fall-through edges. The checker then checks the
filled annotation like any other, so nothing about `fill` needs to be trusted. -/

def fallState (A : AState) (j : Nat) : List Edge → Option AState
  | [] => none
  | .goto j' B :: es => if j' = j then some B else fallState A j es
  | .ret _ :: es => fallState A j es

def Ctx.fillGo (c : Ctx) : Nat → List (Option Instr) → Option AState → List (Nat × AState) →
    List (Option AState)
  | _, [], _, _ => []
  | i, oi :: ps, cur, hints =>
    let (st, hints') := match hints with
      | (j, A) :: hs => if j = i then (some A, hs) else (cur, hints)
      | [] => (cur, [])
    let next := match st with
      | none => none
      | some A => match c.stepAt (c.f.pcOf i) oi A with
        | some es => fallState A (i + 1) es
        | none => none
    st :: c.fillGo (i + 1) ps next hints'

def Ctx.fill (c : Ctx) (hints : List (Nat × AState)) : Array (Option AState) :=
  (c.fillGo 0 c.f.prog none hints).toArray

/-! ## The check in one pass

`Ctx.valid` indexes program and annotation by position: quadratic in the kernel.
`Ctx.validFast` walks both together; only jumps index. `validFast_sound` (`Check.Fast`)
shows it implies `Ctx.valid`. -/

def edgeOkAt (anno : Array (Option AState)) (i : Nat) (next : Option (Option AState)) :
    Edge → Bool
  | .goto j B =>
      if j = i + 1 then
        match next with
        | some (some C) => B == C || B.le C
        | _ => false
      else edgeOk anno (.goto j B)
  | .ret B => okExit B

def Ctx.walk (c : Ctx) (anno : Array (Option AState)) :
    Nat → List (Option Instr) → List (Option AState) → Bool
  | i, oi :: ps, a :: as =>
      (match a with
        | none => true
        | some A => match c.stepAt (c.f.pcOf i) oi A with
          | none => false
          | some es => es.all (edgeOkAt anno i as.head?)) &&
      c.walk anno (i + 1) ps as
  | _, _, _ => true

def Ctx.validFast (c : Ctx) (anno : Array (Option AState)) : Bool :=
  c.σ.strs.all (fun e => e.1.isPtr && e.2.isPtr) &&
  c.f.base == c.σ.entry &&
  (match Fn.annoAt anno 0 with
    | some A => c.σ.entryState.le A
    | none => false) &&
  anno.size == c.f.prog.length && c.walk anno 0 c.f.prog anno.toList

end AsmVerif.RiscV.Check
