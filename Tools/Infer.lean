/-
  Tools.Infer

  Infer an interface (`Check.Iface`) and a certificate (an annotation) for every function of
  an image, bottom-up over the call graph, and emit them as Lean for the kernel to check.

      lake exe infer-contracts ELF NM OUT.tsv STACKTOP PROTLO PROTHI
        [LEANDIR MODPREFIX IMGPREFIX LAYOUT [REGISTRY [CFI [STATICS]]]]

  REGISTRY lists hand-proved interfaces, CFI the control-flow premises, STATICS the statics
  the `Env` protects (address, length, name: their load values are constants).

  Untrusted. The abstract interpretation here mirrors `Check.Ctx.stepAt`, with the checks
  against the function's own interface replaced by *recording* what the interface must
  allow: the stack depth, footprint items, nonzero premises, whether it returns. The
  interface is then exactly what was recorded, the real checker (`Ctx.valid`) is run on
  the result as a sanity check, and the kernel re-runs it.

  A function gets no interface when its analysis meets something the checker does not
  model: an indirect call or jump through an unknown target, a store through an unknown
  pointer, an unmodelled `ecall`, a store above its entry stack pointer, a callee without an
  interface, or recursion.

  Indirect calls are resolved by value sets. A first, permissive pass over every function
  (unknown callees havoc and return) collects the values each call site passes in the
  argument registers; a register whose values, over every site, are rodata addresses or
  function entries becomes a `vals` premise of the callee. With the premises the bottom-up
  analysis runs again, and the passes repeat until the premises are stable. The kernel
  checks that every caller discharges them.
-/

import RiscvZkvm.Interpreter
import AsmVerif.RiscV.Check.Spec
import Tools.Elf

namespace Tools.Infer

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter AsmVerif.RiscV.Check Tools.Elf
open AsmVerif.RiscV.Frame (AVal AState Fn aluResult loadOf storeOf Width mayHit branchOff? joinAt
  regIdx allRegs)

/-! ## What a function's interface must allow -/

/-- A call site, for the top-down pass: the callee and the caller's state at the call. -/
structure Site where
  tgt : Word
  st : AState

structure Need where
  depth : Nat := 0
  items : List Item := []
  nz : List AVal := []
  returns : Bool := false
  frags : List Word := []
  /-- The cells whose premises the checks rely on. -/
  cells : List Cell := []
  /-- Cells an indirect jump, or a callee's candidate premise, wants as a constant set. -/
  wants : List Cell := []
  /-- Entry registers wanted as a constant set. -/
  wantRegs : List Reg := []
  /-- Writers a callee needs that the function has not got: it must be lent them. -/
  strs : List (AVal × AVal) := []
  /-- A callee changes the heap's structure. -/
  heap : Bool := false
  sites : List Site := []

def Need.addItem (n : Need) (it : Item) : Need :=
  if n.items.contains it then n else { n with items := it :: n.items }

def Need.addNz (n : Need) (v : AVal) : Need :=
  if n.nz.contains v then n else { n with nz := v :: n.nz }

def Need.addCell (n : Need) (c : Cell) : Need :=
  if n.cells.contains c then n else { n with cells := c :: n.cells }

def Need.addWant (n : Need) (c : Cell) : Need :=
  if n.wants.contains c then n else { n with wants := c :: n.wants }

def Need.addStr (n : Need) (e : AVal × AVal) : Need :=
  if n.strs.contains e then n else { n with strs := n.strs ++ [e] }

/-- Why the analysis gave up, with the cells it wanted constant on the way. `blocked` names
    a callee still being worked on. -/
inductive Why where
  | fail (pc : Word) (msg : String) (st : Need := {})
  | blocked (callee : Word)

abbrev M := StateT Need (Except Why)

def bad (pc : Word) (msg : String) : M α := do throw (.fail pc msg (← get))

/-- Paths of loads longer than this are not followed (a linked list would grow forever). -/
def maxPath : Nat := 3

structure Ctx' where
  env : Env
  tbl : Std.HashMap Word Iface
  pending : Std.HashSet Word
  f : Fn
  /-- The function's `vals` premises. -/
  vals : List (Reg × List Word) := []
  /-- Cells with candidate sets, from the top-down pass. -/
  cvals : List Cell := []
  /-- Discovering: any cell may be a premise, and a callee's writer the function has not
      got becomes one it is lent. Otherwise exactly `cells` and `strs`, as the checker. -/
  discover : Bool := true
  cells : List Cell := []
  /-- The writers the function is lent. -/
  strs : List (AVal × AVal) := []
  /-- The depth and heap flag found so far: what the checker's after-call states depend
      on (`slotOk`). -/
  depth : Nat := 0
  heap : Bool := false
  /-- Collecting call sites: unknown callees havoc and return, nothing is rejected for
      want of a callee's premises. -/
  permissive : Bool := false

/-- The premises so far, as the interface the checker's candidate and writer logic reads.
    Discovering, the cells are those with candidates: any other may still become one. -/
def Ctx'.σ (c : Ctx') : Iface :=
  { entry := c.f.base, depth := c.depth, vals := c.vals,
    cells := if c.discover then c.cvals else c.cells, strs := c.strs, heap := c.heap }

/-- What the function knows of its writers, under a refinement. -/
def Ctx'.kn (c : Ctx') (ref : Option (AVal × Word)) : Kn := closure c.env c.σ ref

def Ctx'.lookup (c : Ctx') (pc tgt : Word) : M Iface := do
  match c.tbl[tgt]? with
  | some g => pure g
  | none =>
    if c.permissive then pure { entry := tgt, depth := 0 }
    else if c.pending.contains tgt then throw (.blocked tgt)
    else bad pc s!"callee {tgt.toHex} has no interface"

/-- The argument registers whose call-site values are collected. -/
def argRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

def needDepth (d : Nat) : M Unit := modify fun n => { n with depth := max n.depth d }

/-! ### Cells -/

def sameCell (r : Reg) (ks : List Word) (k : Word) (cl : Cell) : Bool :=
  cl.r == r && cl.ks == ks && cl.k == k

def Ctx'.findCell (c : Ctx') (r : Reg) (ks : List Word) (k : Word) : Option Cell :=
  if c.discover then
    match c.cvals.find? (sameCell r ks k) with
    | some cl => some cl
    | none => if ks.length < maxPath then some { r, ks, k } else none
  else c.cells.find? (sameCell r ks k)

/-- `cellAt`: the value of the doubleword at an entry-memory address, if it is a cell: the
    symbolic load (`cellVal`). A cell with candidates is a premise as soon as it is read. -/
def Ctx'.cellAtI (c : Ctx') (a : AVal) : M (Option (Cell × AVal)) := do
  let some (r, ks, k) := (match a with
    | .lin r k => some (r, [], k)
    | .cell r ks d => some (r, ks, d)
    | _ => none) | return none
  match c.findCell r ks k with
  | none => pure none
  | some cl =>
    if cl.vals.isSome then modify (·.addCell cl)
    pure (some (cl, .cell r (ks ++ [k]) 0))

/-- The premises a value relies on: the cells along its path. -/
def demand (v : AVal) : M Unit :=
  match v with
  | .cell r ks _ => do
    for i in List.range ks.length do
      modify (·.addCell { r, ks := ks.take i, k := ks[i]! })
  | _ => pure ()

/-- What a value that should be a set of constants wants: the cell it was loaded from, and
    the cell or entry register its base came from (a vtable entry: the vtable pointer). -/
def wantsOf (v : AVal) : List Cell × List Reg :=
  match v with
  | .lin r _ => ([], [r])
  | .cell r ks _ =>
    if h : ks ≠ [] then
      let c : Cell := { r, ks := ks.dropLast, k := ks.getLast h }
      let ks' := ks.dropLast
      if h' : ks' ≠ [] then ([c, { r, ks := ks'.dropLast, k := ks'.getLast h' }], [])
      else ([c], [r])
    else ([], [])
  | _ => ([], [])

def want (v : AVal) : M Unit := do
  let (cs, rs) := wantsOf v
  for c in cs do modify (·.addWant c)
  for r in rs do modify fun n => if n.wantRegs.contains r then n else { n with wantRegs := r :: n.wantRegs }

/-- `loadVal`, discovering. Every way the checker knows a doubleword gives the same symbolic
    load; a load through a value with candidates, all protected, needs no cell, nor does a
    stable doubleword of a writer. -/
def Ctx'.loadI (c : Ctx') (kn : Kn) (A : AState) (b : AVal) (isD : Bool) : M AVal := do
  if !isD then return .top
  match b.frameOff? with
  | some k => pure ((A.slots.lookup k).getD .top)
  | none => match b with
    | .const _ | .oneOf _ => pure (loadVal c.env c.σ kn A b true)
    | b =>
      if let some cs := cands c.env c.σ kn b then
        if cs.all c.env.protKey then return b.cellOf.getD .top
      match kn.cells.lookup b with
      | some v => pure v
      | none => return ((← c.cellAtI b).map (·.2)).getD .top

/-- `contentAt`, recording the cells it relies on. -/
def Ctx'.contentAtI (c : Ctx') (kn : Kn) (A : AState) (a : AVal) : M (Option AVal) := do
  demand a
  match a.frameOff? with
  | some f => pure (A.slots.lookup f)
  | none => match kn.cells.lookup a with
    | some v => pure (some v)
    | none => match ← c.cellAtI a with
      | some (cl, v) => modify (·.addCell cl); pure (some v)
      | none => pure none

def Ctx'.instPathI (c : Ctx') (kn : Kn) (A : AState) : AVal → List Word → M (Option AVal)
  | v, [] => pure (some v)
  | v, k :: ks => do
    match ← c.contentAtI kn A (v.addK k) with
    | some u => c.instPathI kn A u ks
    | none => pure none

def Ctx'.instValI (c : Ctx') (kn : Kn) (A : AState) : AVal → M AVal
  | .lin r k => pure ((A.get r).addK k)
  | .cell r ks d => do return ((← c.instPathI kn A (A.get r) ks).map (·.addK d)).getD .top
  | v => pure v

def Ctx'.instItems (c : Ctx') (kn : Kn) (pc : Word) (A : AState) (g : Iface) : M (List Item) :=
  g.foot.mapM fun it => do
    match instLen A it.len with
    | some l =>
      let b ← c.instValI kn A it.base
      demand b
      pure { base := b, len := l }
    | none => bad pc s!"callee item {(repr it).pretty 80} cannot be instantiated"

/-! ### Straight-line instructions -/

/-- `storeStep`, recording. -/
def storeI (pc : Word) (A : AState) (rs1 rs2 : Reg) (off : BitVec 12) (w : Width) : M AState := do
  let b := (A.get rs1).addK (signExtend12 off)
  match b.frameOff? with
  | some k =>
      if wbytes w ≤ negOff k && negOff k < 2 ^ 31 then
        needDepth (negOff k)
        let kept := A.slots.filter (fun p => !mayHit w k p.1)
        let new := match w, A.get rs2 with
          | .d, .top => kept
          | .d, v => if negOff k % 8 = 0 then (k, v) :: kept else kept
          | .sub, _ => kept
        pure { A with slots := new }
      else bad pc "store at or above the entry stack pointer"
  | none =>
      if !b.isPtr then bad pc "store through an unknown pointer"
      else if !b.symFree then bad pc "store through a symbolic pointer"
      else
        demand b
        modify (·.addItem { base := b, len := .n (wbytes w) })
        pure A

/-- `plainStep`, recording: the ALU step is the checker's own; a load's value is found here
    (recording the cells), then handled as `loadStep` does. -/
def Ctx'.plainI (c : Ctx') (kn : Kn) (pc : Word) (A : AState) (i : Instr) : M AState := do
  match aluStep pc A i with
  | some B => pure B
  | none =>
  match loadOf i with
  | some (rd, rs, off, isD) =>
    let v ← c.loadI kn A ((A.get rs).addK (signExtend12 off)) isD
    if v != .top then pure (A.set rd v) else
    let A := A.kill pc.toNat 0
    let s := AVal.sym pc.toNat 0 0
    pure ((A.set rd s).addFacts (loadBound i s))
  | none =>
  match storeOf i with
  | some (rs1, rs2, off, w) => storeI pc A rs1 rs2 off w
  | none =>
  match i with
  | .NOP | .FENCE => pure A
  | _ => bad pc s!"unmodeled {(repr i).pretty 80}"

/-- Record that a value (in this function's terms) must be nonzero. -/
def nzV (pc : Word) : AVal → M Unit
  | .const c => if c != 0 then pure () else bad pc "a value that must be nonzero is 0"
  | .lin r k => modify (·.addNz (.lin r k))
  | .cell r ks k => do demand (.cell r ks k); modify (·.addNz (.cell r ks k))
  | .top => bad pc "a value that must be nonzero is unknown"
  | .sym .. => bad pc "a value that must be nonzero is symbolic"
  | .oneOf cs => if cs.all (· != 0) then pure () else bad pc "a value that must be nonzero may be 0"

def Ctx'.nzI (c : Ctx') (kn : Kn) (pc : Word) (A : AState) (v : AVal) : M Unit := do
  if !v.isPtr then bad pc "a callee's nonzero premise is not a value"
  nzV pc (← c.instValI kn A v)

/-- An item a syscall writes, checked as `itemOk σ σ.depth` will check it. -/
def sysItemI (pc : Word) (it : Item) : M Unit := do
  match it.base.frameOff?, it.len with
  | some k, .n l =>
    if !(l ≤ negOff k) then bad pc "syscall writes a frame item above the entry stack pointer"
    needDepth (negOff k)
  | some _, _ => bad pc "syscall writes a frame item of register length"
  | none, _ =>
    if !it.base.isPtr then bad pc "syscall writes through an unknown pointer"
    demand it.base
    modify (·.addItem it)

/-- `ecall`, as `sysStep` classifies it. -/
def ecallI (pc : Word) (A : AState) : M (Option (AState × List Item)) := do
  match A.get .x5 with
  | .const t =>
    if Sp1.isAccelId t then
      match accelLen t with
      | some L => pure (some (A, [⟨A.get .x10, .n (8 * L)⟩]))
      | none => bad pc s!"precompile {t.toHex} not modeled"
    else if t = Sp1.HINT_LEN then pure (some (A.set .x5 .top, []))
    else if t = Sp1.HINT_READ then
      match lenPlus (A.get .x11) 8 with
      | some l => pure (some (A, [⟨A.get .x10, l⟩]))
      | none => bad pc "hint read of unknown length"
    else if t = Sp1.COMMIT ∨ t = Sp1.COMMIT_DEFERRED_PROOFS then pure (some (A, []))
    else if t = 0 then do nzV pc (A.get .x10); pure none
    else if t = 2 then pure (some (A, []))
    else if t = 0xF2 then pure (some (A, [⟨A.get .x10, .n 8⟩, ⟨A.get .x11, .n 8⟩]))
    else pure none
  | _ => bad pc "ecall with an unknown syscall number"

/-! ### Calls -/

/-- A callee's `vals` premise, discharged by the caller's value's candidates. -/
def Ctx'.valI (c : Ctx') (kn : Kn) (pc : Word) (A : AState) (p : Reg × List Word) : M Unit := do
  let v := A.get p.1
  if inCands c.env c.σ kn v p.2 then pure ()
  else
    want v
    bad pc s!"callee needs x{regIdx p.1} among {p.2.length} candidates"

/-- A callee's cell premise, discharged as `cellOk` will. -/
def Ctx'.cellI (c : Ctx') (kn : Kn) (pc : Word) (A : AState) (fs : List Word) (mo : Option Nat)
    (its : List Item) (cl : Cell) : M Unit := do
  let some v ← c.instPathI kn A (A.get cl.r) cl.ks
    | bad pc "a callee's cell is not reachable from what the caller knows"
  let a := v.addK cl.k
  demand a
  let w ← match a.frameOff? with
    | some f =>
      if fs.contains f then bad pc "a callee's cell is a frame slot its writers are built from"
      match mo with
      | some m => pure (if negOff f ≤ m && its.all (slotClear f) then A.slots.lookup f else none)
      | none => pure none
    | none => do
      match ← c.cellAtI a with
      | some (cl', v') => modify (·.addCell cl'); pure (some v')
      | none => pure none
  let some w := w | bad pc "a callee's cell may change under it"
  match cl.vals with
  | none => pure ()
  | some cs =>
    if inCands c.env c.σ kn w cs then pure ()
    else
      want w
      bad pc "a callee's cell must hold one of its candidates"

/-- Collecting, a premise check that fails only says what it wants. -/
def Ctx'.softD (c : Ctx') (d : α) (x : M α) : M α :=
  if c.permissive then
    tryCatch x fun e => match e with
      | .fail _ _ st => do set st; pure d
      | .blocked _ => pure d
  else x

def Ctx'.soft (c : Ctx') (x : M Unit) : M Unit := c.softD () x

/-! ### Writers -/

/-- A value in the function's own terms: a writer's pointer or kind at its entry. -/
def entryVal (v : AVal) : Bool := v.isPtr && v.frameOff?.isNone && v.symFree

/-- A callee's writer, as `passEntry` will match it. Discovering, one the function has not
    got (directly, or the one a structural writer built in its frame wraps) becomes a writer
    it is lent. -/
def Ctx'.passI (c : Ctx') (kn : Kn) (ref : Option (AVal × Word)) (pc : Word) (A : AState)
    (m : Option Nat) (its : List Item) (d k : AVal) : M (List (AVal × AVal) × List Word) := do
  match passEntry c.env c.σ kn ref A m its d k with
  | some r => pure r
  | none =>
    let (d', k') ← match k, m with
      | .const K, some m =>
        match c.env.model.sub K with
        | some s =>
          match framePath A m its d s.dp, framePath A m its d s.kp with
          | some (d2, _), some (k2, _) => do
            if !inCands c.env c.σ kn k2 s.kinds then want k2
            pure (d2, k2)
          | _, _ => pure (d, k)
        | none => pure (d, k)
      | _, _ => pure (d, k)
    if c.discover && entryVal d' && entryVal k' then
      demand d'
      demand k'
      modify (·.addStr (d', k'))
      pure ([(d', k')], [])
    else bad pc "a callee's writer is not one the caller has"

/-- `strsOk`: the callee's writers are the caller's, and the caller's are recovered. The
    writers lent, and the frame slots the callee's writers are built from. -/
def Ctx'.strsI (c : Ctx') (kn : Kn) (ref : Option (AVal × Word)) (pc : Word) (A : AState)
    (m : Option Nat) (its : List Item) (g : Iface) : M (List (AVal × AVal) × List Word) := do
  let mut passed : List (AVal × AVal) := []
  let mut fs : List Word := []
  for e in g.strs do
    let (ps, f) ← c.passI kn ref pc A m its (← c.instValI kn A e.1) (← c.instValI kn A e.2)
    passed := passed ++ ps
    fs := fs ++ f
  if !g.strs.isEmpty then
    for e in c.σ.strs do
      if !recov c.env ref kn passed 2 e then
        bad pc "a writer of the caller is not recovered after the call"
  pure (passed, fs)

/-- A callee's `pre` facts, as `preOk` will check them; its heap flag, recorded. -/
def Ctx'.factsI (c : Ctx') (kn : Kn) (pc : Word) (A : AState) (g : Iface) : M Unit := do
  if g.heap then modify fun n => { n with heap := true }
  for f in g.pre do
    if !preOk c.σ kn A f then bad pc "a callee's precondition fact is not among the facts"

/-! ### Control flow -/

def tailI (pc : Word) (A : AState) (g : Iface) : M Unit := do
  if !okExit A then bad pc "tail call without the callee-saved registers restored"
  needDepth g.depth
  if g.returns then modify fun n => { n with returns := true }

def Ctx'.tailChecks (c : Ctx') (pc : Word) (A : AState) (g : Iface)
    (ref : Option (AVal × Word)) : M Unit := do
  let kn := c.kn ref
  tailI pc A g
  let its ← c.instItems kn pc A g
  for it in its do
    if it.base.frameOff?.isSome || !it.base.isPtr then
      bad pc "tail call passes a frame or unknown pointer the callee writes through"
    modify (·.addItem it)
  for v in g.nz do c.nzI kn pc A v
  for p in g.vals do c.soft (c.valI kn pc A p)
  for cl in g.cells do c.soft (c.cellI kn pc A [] none its cl)
  c.soft (discard <| c.strsI kn ref pc A none its g)
  c.soft (c.factsI kn pc A g)
  for e in c.σ.strs do
    if !writerOkNow c.env c.σ kn ref A 4 e then
      bad pc "a writer of the function is not well-typed at the tail call"
  if !c.σ.strs.isEmpty && g.heap && g.strs.isEmpty then
    bad pc "tail call to a heap-changing callee that takes none of the function's writers"

def Ctx'.jump (c : Ctx') (pc : Word) (A : AState) (tgt : Word)
    (ref : Option (AVal × Word) := none) : M (List Edge) := do
  let A := A.gcIf
  if A.facts.contains falseFact then return []
  match c.f.idx? tgt with
  | some j => pure [.goto j A]
  | none =>
    let g ← c.lookup pc tgt
    modify fun n => { n with sites := ⟨tgt, A⟩ :: n.sites }
    c.soft (c.tailChecks pc A g ref)
    pure []

def Ctx'.call (c : Ctx') (pc : Word) (A : AState) (tgt : Word)
    (ref : Option (AVal × Word) := none) : M (List Edge) := do
  let g ← c.lookup pc tgt
  let kn := c.kn ref
  let A1 := A.set .x1 (.const (pc + 4))
  modify fun n => { n with sites := ⟨tgt, A1⟩ :: n.sites }
  let some m := spOff A1 | bad pc "call with the stack pointer not a known 8-aligned frame offset"
  needDepth (m + g.depth)
  let its ← c.instItems kn pc A1 g
  for it in its do
    match it.base.frameOff?, it.len with
    | some k, .n l =>
      if !(l ≤ negOff k && negOff k ≤ m) then
        bad pc s!"callee writes a frame item outside the caller's frame above its stack pointer"
    | some _, _ => bad pc "callee writes a frame item of register length"
    | none, _ =>
      if !it.base.isPtr then bad pc "callee writes through a pointer the caller does not know"
      modify (·.addItem it)
  let (lent, fs) ← c.softD ([], []) (c.strsI kn ref pc A1 (some m) its g)
  for v in g.nz do c.nzI kn pc A1 v
  for p in g.vals do c.soft (c.valI kn pc A1 p)
  for cl in g.cells do c.soft (c.cellI kn pc A1 fs (some m) its cl)
  c.soft (c.factsI kn pc A1 g)
  if g.returns then
    if (pc + 4) &&& ~~~1#64 != pc + 4 then bad pc "misaligned return address"
    match c.f.idx? (pc + 4) with
    | some j => pure [.goto j (afterCall c.env c.σ kn pc A1 ⟨m, its, lent⟩ g).gcIf]
    | none => bad pc "returning call at the end of the function"
  else pure []

/-- `fanOut`: the edges of an indirect jump or call through a value with candidates, each
    under the refinement that fixes the target. -/
def Ctx'.fanOut (c : Ctx') (v : AVal) (off : BitVec 12)
    (k : Option (AVal × Word) → Word → M (List Edge)) : M (Option (List Edge)) := do
  match root? c.σ v with
  | some (root, cs) =>
    let mut es : List Edge := []
    for cand in cs do
      match refineVal c.env (root, cand) v with
      | some t => es := es ++ (← k (some (root, cand)) ((t + signExtend12 off) &&& ~~~1#64))
      | none => return none
    pure (some es)
  | none => pure none

def Ctx'.runFrag (c : Ctx') (pc0 : Word) (A : AState) (fbase : Word) :
    List (Option Instr) → Nat → M AState
  | [], _ => bad pc0 "fragment without its return"
  | some i :: rest, n =>
      if i = .JALR .x0 .x5 0 then pure A else do
      let B ← c.plainI (c.kn none) (fbase + BitVec.ofNat 64 (4 * n)) A i
      c.runFrag pc0 B fbase rest (n + 1)
  | none :: _, _ => bad pc0 "undecodable word in a fragment"

def Ctx'.outlined (c : Ctx') (pc : Word) (A : AState) (off : BitVec 12) : M (List Edge) := do
  match A.get .x5 with
  | .const t =>
      let tgt := (t + signExtend12 off) &&& ~~~1#64
      match c.f.frags.lookup tgt, c.f.idx? (pc + 4) with
      | some fp, some j =>
          modify fun n => if n.frags.contains tgt then n else { n with frags := tgt :: n.frags }
          let B ← c.runFrag pc (A.set .x5 (.const (pc + 4))) tgt fp 0
          if B.get .x5 = .const (pc + 4) ∧ (pc + 4) &&& ~~~1#64 = pc + 4 then pure [.goto j B.gcIf]
          else bad pc "fragment does not return through t0"
      | none, _ => bad pc s!"outlined call to unknown fragment {tgt.toHex}"
      | _, none => bad pc "outlined call at the end of the function"
  | _ => bad pc "outlined call through an unknown t0"

def Ctx'.stepAt (c : Ctx') (pc : Word) (oi : Option Instr) (A : AState) : M (List Edge) := do
  match oi with
  | none => pure []
  | some ins =>
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
      else bad pc "jal with an unusual link register"
  | .JALR rd rs off =>
      if rd = .x0 then
        if rs = .x1 ∧ off = 0 then
          if okExit A then
            modify fun n => { n with returns := true }
            pure [.ret A]
          else bad pc "ret without ra and the callee-saved registers restored"
        else match ← c.fanOut (A.get rs) off (fun ref t => c.jump pc A t ref) with
          | some es => pure es
          | none => match c.env.cfi.lookup pc with
            | some ts => return (← ts.mapM fun t => c.jump pc A t).flatten
            | none => do want (A.get rs); bad pc "indirect jump"
      else if rd = .x1 then
        match ← c.fanOut (A.get rs) off (fun ref t => c.call pc A t ref) with
        | some es => pure es
        | none => match c.env.cfi.lookup pc with
          | some ts => return (← ts.mapM fun t => c.call pc A t).flatten
          | none => do want (A.get rs); bad pc "indirect call"
      else if rd = .x5 ∧ rs = .x5 then c.outlined pc A off
      else bad pc "jalr with an unusual link register"
  | .EBREAK => pure []
  | .ECALL => do
      match ← ecallI pc A with
      | none => pure []
      | some (B, its) =>
        for it in its do sysItemI pc it
        c.jump pc { B with slots := B.slots.filter fun p => its.all (slotClear p.1) } (pc + 4)
  | ins => do
      let B ← c.plainI (c.kn none) pc A ins
      c.jump pc B (pc + 4)

/-- Kildall over instruction indices, then one pass to record what every reachable
    instruction needs. An instruction the analysis rejects is recorded and treated as having
    no successor, so that one run reports every problem; the function then gets no interface. -/
def Ctx'.analyze (c : Ctx') : Except Why (Array (Option AState) × Need) := do
  let n := c.f.prog.length
  let entry := c.σ.entryState c.env
  let mut anno : Array (Option AState) := (List.replicate n none).toArray.set! 0 (some entry)
  let mut work : List Nat := [0]
  let mut fuel := 256 * n + 64
  let mut fails : List String := []
  let mut wants : List Cell := []
  let mut wantRegs : List Reg := []
  while !work.isEmpty do
    if fuel = 0 then throw (.fail c.f.base "no fixpoint")
    fuel := fuel - 1
    let i := work.head!
    work := work.tail
    let some (some A) := anno[i]? | continue
    let some oi := c.f.prog[i]? | throw (.fail c.f.base "index out of range")
    let es ← match (c.stepAt (c.f.pcOf i) oi A).run {} with
      | .ok (es, _) => pure es
      | .error (.fail pc msg st) =>
        let m := s!"{pc.toHex}: {msg}"
        if !fails.contains m then fails := fails ++ [m]
        wants := wants ++ st.wants.filter (!wants.contains ·)
        wantRegs := wantRegs ++ st.wantRegs.filter (!wantRegs.contains ·)
        pure []
      | .error (.blocked g) => throw (.blocked g)
    for e in es do
      match e with
      | .goto j B =>
        let (a, ch) := joinAt anno j B
        anno := a
        if ch then work := j :: work
      | .ret _ => pure ()
  if !fails.isEmpty && !c.permissive then throw (.fail c.f.base ("; ".intercalate fails))
  let mut need : Need := { wants, wantRegs }
  for i in List.range n do
    let some (some A) := anno[i]? | continue
    let some oi := c.f.prog[i]? | continue
    match (c.stepAt (c.f.pcOf i) oi A).run need with
    | .ok (_, nd) => need := nd
    | .error (.fail pc msg st) =>
      if c.permissive then need := st
      else throw (.fail pc msg st)
    | .error e => throw e
  return (anno, need)

/-! ## Merging footprint items -/

/-- One item per entry register for small constant-length items at small offsets; the rest
    as they are. `Item.within` accepts every merged-away item. -/
def mergeItems (its : List Item) : List Item := Id.run do
  let mut byReg : Std.HashMap Nat (Reg × Nat × Nat) := {}
  let mut rest : List Item := []
  for it in its do
    match it.base, it.len with
    | .lin r k, .n l =>
      if k.toNat < 2 ^ 31 && l < 2 ^ 31 then
        let lo := k.toNat
        let hi := k.toNat + l
        match byReg[regIdx r]? with
        | some (_, lo', hi') => byReg := byReg.insert (regIdx r) (r, min lo lo', max hi hi')
        | none => byReg := byReg.insert (regIdx r) (r, lo, hi)
      else if !rest.contains it then rest := it :: rest
    | _, _ => if !rest.contains it then rest := it :: rest
  let merged := byReg.toList.map fun (_, (r, lo, hi)) =>
    ({ base := .lin r (BitVec.ofNat 64 lo), len := .n (hi - lo) } : Item)
  return (merged.mergeSort fun a b => match a.base, b.base with
    | .lin r _, .lin r' _ => regIdx r ≤ regIdx r'
    | _, _ => true) ++ rest.reverse

/-- One cell per address, the one with candidates if any; in a fixed order. -/
def mergeCells (cs : List Cell) : List Cell := Id.run do
  let mut out : List Cell := []
  for c in cs do
    match out.find? (sameCell c.r c.ks c.k) with
    | some d => if d.vals.isNone && c.vals.isSome then out := c :: out.erase d
    | none => out := c :: out
  return out.mergeSort fun a b =>
    regIdx a.r < regIdx b.r || (regIdx a.r == regIdx b.r && (a.ks.length < b.ks.length ||
      (a.ks.length == b.ks.length && (repr a.ks).pretty ≤ (repr b.ks).pretty && a.k.toNat ≤ b.k.toNat)))

def mkIface (entry : Word) (n : Need) (vals : List (Reg × List Word)) (cells : List Cell)
    (strs : List (AVal × AVal)) : Iface :=
  { entry, depth := n.depth, foot := mergeItems n.items, nz := n.nz.reverse, returns := n.returns,
    vals, cells, strs, heap := n.heap }

/-! ## Lean output -/

def regName (r : Reg) : String := s!".x{regIdx r}"
def word (w : Word) : String := s!"0x{w.toHex}#64"
def fmtWords (cs : List Word) : String := "[" ++ ", ".intercalate (cs.map word) ++ "]"
def fmtList (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"
def fmtAVal : AVal → String
  | .lin r k => s!"(.lin {regName r} {word k})"
  | .const c => s!"(.const {word c})"
  | .top => ".top"
  | .oneOf cs => s!"(.oneOf {fmtWords cs})"
  | .cell r ks k => s!"(.cell {regName r} {fmtWords ks} {word k})"
  | .sym i j k => s!"(.sym {i} {j} {word k})"
def fmtLin (t : LinTerm AVal) : String :=
  "⟨" ++ fmtList (t.coeffs.map fun (v, n) => s!"({fmtAVal v}, {n})") ++ s!", {t.const}⟩"
def fmtOp : Op → String
  | .add => ".add" | .sub => ".sub" | .and => ".and" | .or => ".or" | .xor => ".xor"
  | .sltu => ".sltu" | .slt => ".slt" | .mul => ".mul" | .mulhu => ".mulhu" | .divu => ".divu"
  | .remu => ".remu" | .shl c => s!"(.shl {c})" | .shr c => s!"(.shr {c})" | .sra c => s!"(.sra {c})"
  | .addw => ".addw" | .subw => ".subw" | .shlw c => s!"(.shlw {c})" | .shrw c => s!"(.shrw {c})"
def fmtFact : Fact AVal → String
  | .le l r => s!"(.le {fmtLin l} {fmtLin r})"
  | .op o x args => s!"(.op {fmtOp o} {fmtAVal x} {fmtList (args.map fmtAVal)})"
  | .atom i args => s!"(.atom {i} {fmtList (args.map fmtAVal)})"
def fmtPVal : PVal → String
  | .ent v => s!"(.ent {fmtAVal v})"
  | .ret r => s!"(.ret {regName r})"
  | .out a => s!"(.out {fmtAVal a})"
def fmtPLin (t : LinTerm PVal) : String :=
  "⟨" ++ fmtList (t.coeffs.map fun (v, n) => s!"({fmtPVal v}, {n})") ++ s!", {t.const}⟩"
def fmtPFact : Fact PVal → String
  | .le l r => s!"(.le {fmtPLin l} {fmtPLin r})"
  | .op o x args => s!"(.op {fmtOp o} {fmtPVal x} {fmtList (args.map fmtPVal)})"
  | .atom i args => s!"(.atom {i} {fmtList (args.map fmtPVal)})"
def fmtLen : Len → String
  | .n l => s!"(.n {l})"
  | .reg r => s!"(.reg {regName r})"
  | .regPlus r c => s!"(.regPlus {regName r} {c})"
def fmtItem (it : Item) : String := s!"\{ base := {fmtAVal it.base}, len := {fmtLen it.len} }"
def fmtState (A : AState) : String :=
  let regs := allRegs.map fun r => (r, A.regs.getD (regIdx r) .top)
  let diff := regs.filterMap fun (r, v) => if v == .lin r 0 then none else some s!"({regName r}, {fmtAVal v})"
  let known := regs.filterMap fun (r, v) => if v == .top then none else some s!"({regName r}, {fmtAVal v})"
  let slots := fmtList (A.slots.map fun (k, v) => s!"({word k}, {fmtAVal v})")
  let pairs (ps : List (AVal × AVal)) := fmtList (ps.map fun (a, b) => s!"({fmtAVal a}, {fmtAVal b})")
  let extra := if A.facts.isEmpty && A.wmem.isEmpty && A.fw.isEmpty then "" else
    s!" {fmtList (A.facts.map fmtFact)} {pairs A.wmem} {pairs A.fw}"
  if diff.length ≤ known.length then s!"(.ofDiff {fmtList diff} {slots}{extra})"
  else s!"(.ofKnown {fmtList known} {slots}{extra})"
def fmtCell (c : Cell) : String :=
  let vs := match c.vals with
    | some cs => s!"some {fmtWords cs}"
    | none => "none"
  s!"\{ r := {regName c.r}, ks := {fmtWords c.ks}, k := {word c.k}, vals := {vs} }"
def fmtIface (σ : Iface) : String :=
  s!"\{ entry := {word σ.entry}, depth := {σ.depth}, foot := {fmtList (σ.foot.map fmtItem)}, " ++
  s!"nz := {fmtList (σ.nz.map fmtAVal)}, returns := {σ.returns}, " ++
  s!"vals := {fmtList (σ.vals.map fun (r, cs) => s!"({regName r}, {fmtWords cs})")}, " ++
  s!"cells := {fmtList (σ.cells.map fmtCell)}, " ++
  s!"strs := {fmtList (σ.strs.map fun (d, k) => s!"({fmtAVal d}, {fmtAVal k})")}, " ++
  s!"pre := {fmtList (σ.pre.map fmtFact)}, post := {fmtList (σ.post.map fmtPFact)}, heap := {σ.heap} }"

end Tools.Infer

namespace Tools.Infer

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter AsmVerif.RiscV.Check Tools.Elf
open AsmVerif.RiscV.Frame (AVal AState Fn aluResult loadOf storeOf Width mayHit branchOff? joinAt
  regIdx allRegs)

/-- The doubleword at `a`, little-endian, from the segment holding it (zero elsewhere). -/
def memAt (img : Elf64Image) (a : Nat) : Word :=
  match img.segments.find? (fun s => s.vaddr ≤ a && a + 8 ≤ s.vaddr + s.memsz) with
  | none => 0
  | some seg =>
    let b (i : Nat) : Nat := if a - seg.vaddr + i < seg.data.size then (seg.data.get! (a - seg.vaddr + i)).toNat else 0
    BitVec.ofNat 64 ((List.range 8).foldr (fun i acc => acc * 256 + b i) 0)

/-! ## Interfaces proved by hand

A registry (TSV) of functions whose interface is a theorem proved outside the checker
(`AsmVerif.RiscV.Exec`). Their callers are analysed against them, and the emitted table and
composition use the hand proofs. Columns: address, Lean module, the interface's name, a
term proving `∀ n, (∀ g ∈ tbl, ∀ m < n, g.HoldsN env C m) → iface.HoldsN env C n`, and the
interface itself in a compact form:

    depth=N foot=ITEM,ITEM nz=VAL,VAL ret=0|1 strs=BASE:BASE,...

with `ITEM := BASE:LEN`, `BASE := xN+HEX | #HEX`, `LEN := N | xN | xN+N`. The kernel checks
that the Lean interface is the one callers were checked against: the table it builds is the
Lean definition. -/

structure Given where
  addr : Nat
  module : String
  iface : String
  proof : String
  σ : Iface

def parseReg? (s : String) : Option Reg := do
  guard (s.startsWith "x")
  let n ← (s.drop 1).toString.toNat?
  allRegs[n]?

def parseBase? (s : String) : Option AVal :=
  if s.startsWith "#" then (parseHex? (s.drop 1).toString).map fun c => .const (BitVec.ofNat 64 c)
  else match s.splitOn "+" with
    | [r, k] => do pure (.lin (← parseReg? r) (BitVec.ofNat 64 (← parseHex? k)))
    | _ => none

def parseLen? (s : String) : Option Len :=
  match s.toNat? with
  | some n => some (.n n)
  | none => match s.splitOn "+" with
    | [r] => (parseReg? r).map .reg
    | [r, c] => do pure (.regPlus (← parseReg? r) (← c.toNat?))
    | _ => none

def parseIface? (entry : Nat) (spec : String) : Option Iface := do
  let mut σ : Iface := { entry := BitVec.ofNat 64 entry, depth := 0 }
  for f in spec.splitOn " " do
    match f.splitOn "=" with
    | ["depth", d] => σ := { σ with depth := ← d.toNat? }
    | ["foot", is] =>
      let its ← (is.splitOn ",").filter (· != "") |>.mapM fun it => do
        let [b, l] := it.splitOn ":" | none
        pure ({ base := ← parseBase? b, len := ← parseLen? l } : Item)
      σ := { σ with foot := its }
    | ["nz", vs] => σ := { σ with nz := ← ((vs.splitOn ",").filter (· != "")).mapM parseBase? }
    | ["strs", es] =>
      let strs ← ((es.splitOn ",").filter (· != "")).mapM fun e => do
        let [d, k] := e.splitOn ":" | none
        pure ((← parseBase? d), (← parseBase? k))
      σ := { σ with strs }
    | ["ret", r] => σ := { σ with returns := r == "1" }
    | ["heap", h] => σ := { σ with heap := h == "1" }
    | [""] => pure ()
    | _ => none
  return σ

def parseGiven (src : String) : Except String (List Given) := do
  let mut out := []
  for l in src.splitOn "\n" do
    if l.trimAscii.isEmpty || l.startsWith "#" || l.startsWith "addr" then continue
    let [a, m, i, p, spec] := l.splitOn "\t" | throw s!"bad registry line: {l}"
    let some addr := parseHex? a | throw s!"bad address: {a}"
    let some σ := parseIface? addr spec | throw s!"bad interface: {spec}"
    out := out ++ [{ addr, module := m, iface := i, proof := p, σ }]
  return out

/-- A constant footprint item shares a doubleword key with a protected region: a precondition
    that says it does not would be false. -/
def hitsProt (env : Env) (it : Item) : Bool :=
  match it.base, it.len with
  | .const c, .n l =>
    l > 0 && env.prot.any fun (b, pl) =>
      let lo := max (c.toNat / 8 * 8) (b.toNat / 8 * 8)
      pl > 0 && decide (lo < min (c.toNat + l) (b.toNat + pl))
  | _, _ => false

/-- What the call sites give a function: the joined value of each argument register and
    wanted cell. -/
abbrev Raw := List (Reg × AVal) × List (Cell × AVal)

/-- A function's premises from the top-down pass. -/
structure Prem where
  vals : List (Reg × List Word) := []
  cvals : List Cell := []
  deriving BEq

structure Result where
  sym : Sym
  func : Fn
  status : Except String (Iface × Array (Option AState) × List Word)
  given : Option Given := none

def run (img : Elf64Image) (syms : List Sym) (env : Env) (given : List Given) :
    IO (Array Result × List Iface × Std.HashMap Word Prem × Array (Sym × Fn)) := do
  let progOf (s : Sym) : Except String (List (Option Instr)) :=
    (wordsAt img s.addr (s.size / 4)).map (·.map decode)
  let mut frags : List (Word × List (Option Instr)) := []
  for s in syms do
    if s.name.startsWith "OUTLINED_FUNCTION" then
      if let .ok p := progOf s then frags := (BitVec.ofNat 64 s.addr, p) :: frags
  let mut fns : Array (Sym × Fn) := #[]
  for s in syms do
    if s.size % 4 != 0 || s.name.startsWith "OUTLINED_FUNCTION" then continue
    if let .ok prog := progOf s then
      fns := fns.push (s, { base := BitVec.ofNat 64 s.addr, prog, frags })
  let isEntry : Std.HashSet Word := fns.foldl (fun acc (_, f) => acc.insert f.base) {}
  let useful (c : Word) : Bool := env.protKey c || isEntry.contains c
  let givenAt : Std.HashSet Word := given.foldl (fun acc g => acc.insert g.σ.entry) {}
  let fnAt : Std.HashMap Word Fn := fns.foldl (fun acc (_, f) => acc.insert f.base f) {}
  -- Bottom-up, under the given premises. A function's discovering run finds the cells its
  -- checks rely on; the exact run, with those cells declared, is what the checker will see.
  let bottomUp (prem : Std.HashMap Word Prem) :
      Std.HashMap Word (Iface × Array (Option AState) × List Word) × Std.HashMap Word String ×
        Std.HashSet Word := Id.run do
    let mut done : Std.HashMap Word (Iface × Array (Option AState) × List Word) := {}
    for g in given do done := done.insert g.σ.entry (g.σ, #[], [])
    let mut failed : Std.HashMap Word String := {}
    let mut pending : Std.HashSet Word := fns.foldl (fun acc (_, f) => acc.insert f.base) {}
    for g in given do pending := pending.erase g.σ.entry
    let mut changed := true
    while changed do
      changed := false
      for (_, f) in fns do
        if !pending.contains f.base then continue
        let tbl : Std.HashMap Word Iface := done.fold (fun acc k v => acc.insert k v.1) {}
        let p := prem.getD f.base {}
        let c0 : Ctx' := { env, tbl, pending := pending.erase f.base, f, vals := p.vals,
                           cvals := p.cvals }
        -- The writers a function is lent are found by its calls, and what it knows through
        -- them feeds its own analysis: discover until they stop growing.
        let mut c := c0
        let mut disc := c.analyze
        for _ in [0:3] do
          match disc with
          | .ok (_, need) =>
            let strs := c.strs ++ need.strs.filter (!c.strs.contains ·)
            if strs.length == c.strs.length then break
            c := { c with strs }
            disc := c.analyze
          | .error _ => break
        match disc with
        | .ok (_, need) =>
          let mut cells := mergeCells need.cells
          let mut depth := need.depth
          let mut heap := need.heap
          let mut res : Except String (Array (Option AState) × Need × List Cell) :=
            .error "no exact run"
          for _ in [0:4] do
            match ({ c with discover := false, cells, depth, heap } : Ctx').analyze with
            | .ok (anno, need') =>
              res := .ok (anno, need', cells)
              let used := mergeCells need'.cells
              if used.length == cells.length && need'.depth == depth && need'.heap == heap then
                break
              cells := used
              depth := need'.depth
              heap := need'.heap
            | .error (.fail pc msg _) =>
              if let .ok _ := res then break
              res := .error s!"{pc.toHex}: exact run: {msg}"
              break
            | .error (.blocked _) => break
          match res with
          | .ok (anno, need', cells') =>
            let σ := mkIface f.base need' p.vals cells' c.strs
            match σ.foot.find? (hitsProt env) with
            | some it =>
              failed := failed.insert f.base
                s!"footprint {fmtItem it} writes a protected region (its precondition would be unsatisfiable)"
            | none => done := done.insert f.base (σ, anno, need'.frags)
          | .error e => failed := failed.insert f.base e
          pending := pending.erase f.base
          changed := true
        | .error (.fail pc msg _) =>
          failed := failed.insert f.base s!"{pc.toHex}: {msg}"
          pending := pending.erase f.base
          changed := true
        | .error (.blocked _) => pure ()
    return (done, failed, pending)
  -- Call sites, permissively, under the given premises and the interfaces found so far: the
  -- values passed in argument registers, and the contents of the cells callees want.
  let collect (prem : Std.HashMap Word Prem) (tbl : Std.HashMap Word Iface)
      (extra : Std.HashMap Word (List Cell × List Reg)) :
      Std.HashMap Word Raw × Std.HashMap Word (List Cell × List Reg) := Id.run do
    let ctxOf (f : Fn) : Ctx' :=
      let p := prem.getD f.base {}
      { env, tbl, pending := {}, f, vals := p.vals, cvals := p.cvals, permissive := true,
        strs := ((tbl[f.base]?).map (·.strs)).getD [],
        depth := ((tbl[f.base]?).map (·.depth)).getD 0, heap := ((tbl[f.base]?).map (·.heap)).getD false }
    let mut wants : Std.HashMap Word (List Cell × List Reg) := {}
    let mut sites : Array (Word × Site) := #[]
    for (_, f) in fns do
      if let .ok (_, need) := (ctxOf f).analyze then
        let (ec, er) := extra.getD f.base ([], [])
        wants := wants.insert f.base (need.wants ++ ec.filter (!need.wants.contains ·),
          need.wantRegs ++ er.filter (!need.wantRegs.contains ·))
        sites := sites ++ (need.sites.map (f.base, ·)).toArray
    let mut extra' := extra
    let addExtra (m : Std.HashMap Word (List Cell × List Reg)) (cb : Word) (v : AVal) :
        Std.HashMap Word (List Cell × List Reg) :=
      let (cs, rs) := wantsOf v
      let (oc, or) := m.getD cb ([], [])
      m.insert cb (oc ++ cs.filter (!oc.contains ·), or ++ rs.filter (!or.contains ·))
    let mut seenRegs : Std.HashMap Word (List AVal) := {}
    let mut seenWant : Std.HashMap Word (List (Reg × AVal)) := {}
    let mut seenCells : Std.HashMap Word (List (Cell × AVal)) := {}
    for (cb, site) in sites do
      let some f := fnAt[cb]? | continue
      let c := ctxOf f
      let kn0 := c.kn none
      -- A value with candidates is the set of them.
      let cv (v : AVal) : AVal := match v with
        | .lin .. | .cell .. => match cands env c.σ kn0 v with
          | some cs => .oneOf cs
          | none => v
        | v => v
      let vs := argRegs.map fun r => cv (site.st.get r)
      seenRegs := seenRegs.insert site.tgt (match seenRegs[site.tgt]? with
        | some ws => (ws.zip vs).map fun (a, b) => a.join b
        | none => vs)
      let (wcs, wrs) := wants.getD site.tgt ([], [])
      -- Optimistic: a wanted value the caller has only symbolically (its own entry value or
      -- cell) adds nothing here, and becomes the caller's want.
      for r in wrs do
        let v := cv (site.st.get r)
        match v with
        | .cell .. | .lin .. => extra' := addExtra extra' cb v
        | _ =>
          let old := seenWant.getD site.tgt []
          seenWant := seenWant.insert site.tgt (match old.find? (·.1 == r) with
            | some (_, u) => (r, u.join v) :: old.filter (·.1 != r)
            | none => (r, v) :: old)
      for w in wcs do
        let ev : M (Option AVal) := do
          match ← c.instPathI kn0 site.st (site.st.get w.r) w.ks with
          | some v => c.contentAtI kn0 site.st (v.addK w.k)
          | none => pure none
        let v := match ev.run' {} with
          | .ok (some v) => cv v
          | _ => .top
        match v with
        | .cell .. | .lin .. => extra' := addExtra extra' cb v
        | _ =>
          let old := seenCells.getD site.tgt []
          seenCells := seenCells.insert site.tgt (match old.find? (·.1 == w) with
            | some (_, u) => (w, u.join v) :: old.filter (·.1 != w)
            | none => (w, v) :: old)
    let mut out : Std.HashMap Word Raw := {}
    for (_, f) in fns do
      let tgt := f.base
      if givenAt.contains tgt then continue
      let wanted := seenWant.getD tgt []
      let regs := match seenRegs[tgt]? with
        | some vs => (argRegs.zip vs).map fun (r, v) =>
          match wanted.find? (·.1 == r) with
          | some (_, u) => (r, u)
          | none => (r, v)
        | none => wanted
      let cells := seenCells.getD tgt []
      if !regs.isEmpty || !cells.isEmpty then out := out.insert tgt (regs, cells)
    return (out, extra')
  let usefulSet : AVal → Option (List Word)
    | .const c => if useful c then some [c] else none
    | .oneOf cs => if cs.all useful then some cs else none
    | _ => none
  -- The premises the accumulated values give: the useful sets.
  let premOf (acc : Std.HashMap Word Raw) : Std.HashMap Word Prem := acc.fold (init := {})
    fun out tgt (regs, cells) =>
      let vals := regs.filterMap fun (r, v) => (usefulSet v).map (r, ·)
      let cvals := cells.filterMap fun (w, v) => (usefulSet v).map fun cs => { w with vals := some cs }
      if vals.isEmpty && cvals.isEmpty then out
      else out.insert tgt { vals := vals.mergeSort (fun a b => regIdx a.1 ≤ regIdx b.1),
                            cvals := mergeCells cvals }
  -- Values only rise (absent, a set, then ⊤): the iteration is monotone and stops.
  let joinRaw (a b : Raw) : Raw :=
    let regs := b.1.foldl (fun acc (r, v) => match acc.find? (·.1 == r) with
      | some (_, u) => (r, u.join v) :: acc.filter (·.1 != r)
      | none => (r, v) :: acc) a.1
    let cells := b.2.foldl (fun acc (w, v) => match acc.find? (·.1 == w) with
      | some (_, u) => (w, u.join v) :: acc.filter (·.1 != w)
      | none => (w, v) :: acc) a.2
    (regs, cells)
  let sorted (m : Std.HashMap Word Prem) := m.toList.mergeSort (fun a b => a.1.toNat ≤ b.1.toNat)
  let mut acc : Std.HashMap Word Raw := {}
  let mut prem : Std.HashMap Word Prem := {}
  let mut extra : Std.HashMap Word (List Cell × List Reg) := {}
  let mut (done, failed, pending) := bottomUp prem
  let mut rounds := 0
  for _ in [0:40] do
    rounds := rounds + 1
    let tbl0 : Std.HashMap Word Iface := done.fold (fun acc k v => acc.insert k v.1) {}
    let (raw, extra') := collect prem tbl0 extra
    acc := raw.fold (fun acc tgt r => acc.insert tgt (joinRaw (acc.getD tgt ([], [])) r)) acc
    let prem' := premOf acc
    let grew := extra'.fold (fun n _ v => n + v.1.length + v.2.length) 0 !=
      extra.fold (fun n _ v => n + v.1.length + v.2.length) 0
    extra := extra'
    if sorted prem' == sorted prem && !grew then break
    if sorted prem' != sorted prem then
      if (← IO.getEnv "INFER_ROUNDS").isSome then
        let changed := (prem'.toList.filter fun (a, p) => prem[a]? != some p).map (hex ·.1.toNat 8)
        let gone := (prem.toList.filter fun (a, _) => !prem'.contains a).map (hex ·.1.toNat 8)
        IO.eprintln s!"round {rounds}: changed {changed} gone {gone}"
      prem := prem'
      (done, failed, pending) := bottomUp prem
  IO.eprintln s!"infer-contracts: premises after {rounds} rounds"
  for b in pending do failed := failed.insert b "recursion (a cycle of calls)"
  let tbl : List Iface := (fns.toList.filterMap fun (_, f) => (done[f.base]?).map (·.1))
  let mut out : Array Result := #[]
  for (s, f) in fns do
    if let some g := given.find? (·.addr == s.addr) then
      out := out.push ⟨s, f, .ok (g.σ, #[], []), some g⟩
      continue
    match done[f.base]? with
    | some (σ, anno, used) =>
      let f' := { f with frags := f.frags.filter fun (b, _) => used.contains b }
      let ok := ({ env, tbl, σ, f := f' } : Ctx).valid (anno.map Option.toList)
      let st : Except String (Iface × Array (Option AState) × List Word) :=
        if ok then .ok (σ, anno, used) else .error "inferred, but the checker rejects it"
      out := out.push { sym := s, func := f', status := st }
    | none => out := out.push { sym := s, func := f, status := .error (failed.getD f.base "?") }
  return (out, tbl, prem, fns)

/-! ## Emitting Lean -/

/-- Chunk indices of `MODPREFIX.F_<addr>` modules in the layout's code list. -/
def layoutIndex (layout : String) : Std.HashMap Nat Nat := Id.run do
  let lines := layout.splitOn "\n"
  let mut inCode := false
  let mut idx := 0
  let mut out : Std.HashMap Nat Nat := {}
  for l in lines do
    let t := l.trimAscii.toString
    if t.startsWith "code := [" then inCode := true; continue
    if inCode then
      if t.startsWith "]" then inCode := false; continue
      if t.startsWith "⟨" then
        match (t.splitOn ".F_").drop 1 |>.head? with
        | some rest =>
          match parseHex? (String.ofList (rest.toList.takeWhile (· != '.'))) with
          | some a => out := out.insert a idx
          | none => pure ()
        | none => pure ()
        idx := idx + 1
  return out

/-- The states a sparse certificate must give: the analysis's states at the targets of
    jumps (where its join happens), where fall-through propagation does not already produce
    them. Elsewhere the checker's own fall-through state stands: at least as precise as the
    analysis's (which is a join over every visit: a constant and a symbol join to `⊤`, where
    the checker, stepping the final state, keeps the symbol). -/
def hintsFor (c : Ctx) (anno : Array (Option AState)) : List (Nat × List AState) := Id.run do
  let step (i : Nat) (A : AState) : List Edge := match c.f.prog[i]? with
    | some oi => (c.stepAt (c.f.pcOf i) oi A).getD []
    | none => []
  let mut targets : Std.HashSet Nat := {}
  for i in List.range anno.size do
    if let some A := anno[i]! then
      for e in step i A do
        if let .goto j _ := e then
          if j != i + 1 then targets := targets.insert j
  let mut out : Array (Nat × List AState) := #[]
  let mut prev : List AState := []
  for i in List.range anno.size do
    let a := (anno[i]!).toList
    let cur := if a != prev && (prev.isEmpty || targets.contains i) then a else prev
    if cur != prev then out := out.push (i, cur)
    prev := cur.flatMap fun A => fallStates (i + 1) (step i A)
  return out.toList

def emit (dir modPrefix imgPrefix : String) (env : Env) (tbl : List Iface) (res : Array Result)
    (index : Std.HashMap Nat Nat) : IO Nat := do
  IO.FS.createDirAll dir
  let ok := res.filterMap fun r => match r.status, r.given with
    | .ok (σ, anno, used), none => some (r, σ, anno, used)
    | _, _ => none
  let gv := res.filterMap (·.given)
  let tblNames := res.toList.filterMap fun r => match r.status, r.given with
    | .ok _, some g => some g.iface
    | .ok _, none => some s!"A_{hex r.sym.addr 8}.iface"
    | _, _ => none
  let hdr (what : String) := s!"/-\n  DO NOT EDIT -- generated by `lake exe infer-contracts`.\n\n  {what}\n-/\n\n"
  let opens := "open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check\n\n"
  for (r, σ, anno, used) in ok do
    let a := hex r.sym.addr 8
    let fragImports := used.map fun b => s!"import {imgPrefix}.F_{hex b.toNat 8}\n"
    let frags := fmtList (used.map fun b => s!"({imgPrefix}.F_{hex b.toNat 8}.base, {imgPrefix}.F_{hex b.toNat 8}.prog)")
    let c : Ctx := { env, tbl, σ, f := r.func }
    let hints := hintsFor c anno
    -- `INFER_HINTS=addr`: why each hint is needed.
    if (← IO.getEnv "INFER_HINTS") == some a then
      let mut prev : List AState := []
      for i in List.range anno.size do
        let st := (anno[i]!).toList
        if st != prev then
          match st, prev with
          | [A], [B] =>
            let rs := allRegs.filter fun r => A.get r != B.get r
            IO.println <| s!"hint {i}: regs {rs.map fun r => s!"{regName r}: {fmtAVal (B.get r)} -> {fmtAVal (A.get r)}"}" ++
              (if A.slots != B.slots then s!" slots {B.slots.length} -> {A.slots.length}" else "") ++
              (if A.facts != B.facts then s!" facts {B.facts.map fmtFact} -> {A.facts.map fmtFact}" else "") ++
              (if A.wmem != B.wmem then " wmem" else "") ++ (if A.fw != B.fw then " fw" else "")
          | _, _ => IO.println s!"hint {i}: {st.length} states, fall-through {prev.length}"
        prev := st.flatMap fun A => match c.f.prog[i]? with
          | some oi => match c.stepAt (c.f.pcOf i) oi A with
            | some es => fallStates (i + 1) es
            | none => []
          | none => []
    let annoL := c.fill hints
    if !c.validFast annoL then throw <| IO.userError s!"{a}: validFast rejects the filled certificate"
    let body := ",\n  ".intercalate (hints.map fun (i, As) =>
      s!"({i}, {fmtList (As.map fmtState)})")
    IO.FS.writeFile s!"{dir}/A_{a}.lean" <|
      hdr s!"`{r.sym.name}`: its interface and certificate." ++
      s!"import AsmVerif.RiscV.Check.Domain\nimport {imgPrefix}.F_{a}\n" ++ String.join fragImports ++
      s!"\nset_option maxRecDepth 200000\n\nnamespace {modPrefix}.A_{a}\n\n" ++ opens ++
      s!"def iface : Iface := {fmtIface σ}\n\n" ++
      s!"def fn : Fn := \{ base := {imgPrefix}.F_{a}.base, prog := {imgPrefix}.F_{a}.prog, frags := {frags} }\n\n" ++
      s!"noncomputable def hints : List (Nat × List AState) := [\n  {body}]\n\nend {modPrefix}.A_{a}\n"
  -- The table.
  let protS := fmtList (env.prot.map fun (b, l) => s!"({word b}, {l})")
  let cfiS := fmtList (env.cfi.map fun (p, ts) => s!"({word p}, {fmtWords ts})")
  IO.FS.writeFile s!"{dir}/Table.lean" <|
    hdr "The program's `Env` and the table of inferred interfaces." ++
    s!"import AsmVerif.RiscV.Check.Spec\nimport {imgPrefix}.Layout\n" ++
    String.join (ok.toList.map fun (r, _) => s!"import {modPrefix}.A_{hex r.sym.addr 8}\n") ++
    String.join (gv.toList.map fun g => s!"import {g.module}\n") ++
    s!"\nnamespace {modPrefix}\n\n" ++ opens ++
    s!"noncomputable def env : Env :=\n  \{ stackTop := {env.stackTop}, prot := {protS}, init := {imgPrefix}.Layout.image.memAt,\n    cfi := {cfiS} }\n\n" ++
    "theorem env_wf : env.wf = true := by decide +kernel\n\n" ++
    "/-- The trivial model: no heap. -/\n" ++
    "theorem env_ok : env.Ok := ⟨fun _ h => h.elim, fun _ _ _ _ h => h.elim⟩\n\n" ++
    s!"def tbl : List Iface := [\n  " ++ ",\n  ".intercalate tblNames ++
    s!"]\n\nend {modPrefix}\n"
  -- One proof module per function.
  for (r, _, _, used) in ok do
    let a := hex r.sym.addr 8
    let some k := index[r.sym.addr]? | throw <| IO.userError s!"no layout chunk for {a}"
    let fragFacts ← used.mapM fun b => do
      let some kf := index[b.toNat]? | throw <| IO.userError s!"no layout chunk for fragment {b.toHex}"
      pure (hex b.toNat 8, kf)
    let fragDecodes := String.join (fragFacts.map fun (fa, _) =>
      s!"theorem decode_{fa} : decodeWords {imgPrefix}.F_{fa}.words = {imgPrefix}.F_{fa}.prog := by decide +kernel\n\n")
    let fragProof := if used.isEmpty then "(fun _ _ h => by simp [A_" ++ a ++ ".fn] at h)" else
      "(frags_of_image (by\n    intro p hp\n    simp only [A_" ++ a ++ ".fn, List.mem_cons, List.not_mem_nil, or_false] at hp\n    " ++
      "rcases hp with " ++ " | ".intercalate (fragFacts.map fun _ => "rfl") ++ "\n" ++
      String.join (fragFacts.map fun (fa, kf) => s!"    · exact ⟨{kf}, _, rfl, decode_{fa}⟩\n") ++ "))"
    IO.FS.writeFile s!"{dir}/V_{a}.lean" <|
      hdr s!"`{r.sym.name}` meets its interface, given the table below the budget." ++
      s!"import AsmVerif.RiscV.Check.Image\nimport AsmVerif.RiscV.Check.Fast\nimport Cases.Zip2005.Loaded\nimport {modPrefix}.Table\n\n" ++
      "set_option maxRecDepth 200000\n\n" ++
      s!"namespace {modPrefix}.V_{a}\n\n" ++ opens ++ s!"open {modPrefix}\n\n" ++
      s!"noncomputable abbrev ctx : Ctx := \{ env, tbl, σ := A_{a}.iface, f := A_{a}.fn }\n\n" ++
      s!"noncomputable def anno : Array (List AState) := ctx.fill A_{a}.hints\n\n" ++
      s!"theorem valid : ctx.valid anno = true := Ctx.validFast_sound (by decide +kernel)\n\n" ++
      s!"theorem decode : decodeWords {imgPrefix}.F_{a}.words = {imgPrefix}.F_{a}.prog := by decide +kernel\n\n" ++
      fragDecodes ++
      s!"theorem code : CodeAt A_{a}.fn {imgPrefix}.Layout.image.codeAt :=\n  codeAt_of_image (k := {k}) Cases.Zip2005.Loaded.codeWF rfl decode\n  {fragProof}\n\n" ++
      s!"theorem holds (n : Nat) (h : ∀ g ∈ tbl, ∀ m < n, g.HoldsN env {imgPrefix}.Layout.image.codeAt m) :\n" ++
      s!"    A_{a}.iface.HoldsN env {imgPrefix}.Layout.image.codeAt n :=\n" ++
      s!"  Ctx.sound (c := ctx) valid code (by decide +kernel) env_wf env_ok h\n\n" ++
      s!"end {modPrefix}.V_{a}\n"
  -- Assembly.
  IO.FS.writeFile s!"{dir}/All.lean" <|
    hdr "Every interface of the table holds." ++
    String.join (ok.toList.map fun (r, _) => s!"import {modPrefix}.V_{hex r.sym.addr 8}\n") ++
    String.join (gv.toList.map fun g => s!"import {g.module}\n") ++
    s!"\nnamespace {modPrefix}\n\n" ++ opens ++
    s!"theorem all : ∀ g ∈ tbl, g.Holds env {imgPrefix}.Layout.image.codeAt := by\n" ++
    s!"  apply table_sound\n" ++
    s!"  have : tbl.foldr (fun g acc => (∀ n, (∀ g' ∈ tbl, ∀ m < n, g'.HoldsN env {imgPrefix}.Layout.image.codeAt m) →\n" ++
    s!"      g.HoldsN env {imgPrefix}.Layout.image.codeAt n) ∧ acc) True :=\n    ⟨" ++
    ", ".intercalate (res.toList.filterMap fun r => match r.status, r.given with
      | .ok _, some g => some s!"({g.proof})"
      | .ok _, none => some s!"V_{hex r.sym.addr 8}.holds"
      | _, _ => none) ++ ", trivial⟩\n" ++
    s!"  exact forall_mem_of_foldr this\n\nend {modPrefix}\n"
  return ok.size

def main (args : List String) : IO UInt32 := do
  let [elfPath, nmPath, outPath, stackTop, protLo, protHi] := args.take 6
    | IO.eprintln "usage: infer-contracts ELF NM OUT.tsv STACKTOP PROTLO PROTHI"; return 2
  let some stackTop := parseHex? stackTop | return 2
  let some protLo := parseHex? protLo | return 2
  let some protHi := parseHex? protHi | return 2
  let img ← match parseElf64 (← IO.FS.readBinFile elfPath) with
    | .ok img => pure img
    | .error e => IO.eprintln s!"infer-contracts: {e}"; return 1
  let syms := parseNm (← IO.FS.readFile nmPath)
  let cfi ← match (args.drop 11).take 1 with
    | [cfiPath] => do
      let mut out : List (Word × List Word) := []
      for l in (← IO.FS.readFile cfiPath).splitOn "\n" do
        if l.trimAscii.isEmpty || l.startsWith "#" || l.startsWith "site" then continue
        let site :: cs :: _ := l.splitOn "\t" | throw <| IO.userError s!"bad CFI line: {l}"
        let some a := parseHex? site | throw <| IO.userError s!"bad CFI site: {site}"
        let ts ← (cs.splitOn ",").mapM fun c => match parseHex? c with
          | some t => pure (BitVec.ofNat 64 t)
          | none => throw <| IO.userError s!"bad CFI candidate: {c}"
        out := out ++ [(BitVec.ofNat 64 a, ts)]
      pure out
    | _ => pure []
  let statics ← match args.drop 12 with
    | [path] => do
      let mut out : List (Word × Nat) := []
      for l in (← IO.FS.readFile path).splitOn "\n" do
        if l.trimAscii.isEmpty || l.startsWith "#" || l.startsWith "addr" then continue
        let a :: n :: _ := l.splitOn "\t" | throw <| IO.userError s!"bad STATICS line: {l}"
        let (some a, some n) := (parseHex? a, parseHex? n)
          | throw <| IO.userError s!"bad STATICS line: {l}"
        out := out ++ [(BitVec.ofNat 64 a, n)]
      pure out
    | _ => pure []
  let env : Env := { stackTop, prot := (BitVec.ofNat 64 protLo, protHi - protLo) :: statics,
                     init := fun a => memAt img a.toNat, cfi }
  if !env.wf then IO.eprintln "infer-contracts: Env not well-formed"; return 1
  let given ← match (args.drop 10).take 1 with
    | [regPath] => match parseGiven (← IO.FS.readFile regPath) with
      | .ok g => pure g
      | .error e => IO.eprintln s!"infer-contracts: {e}"; return 1
    | _ => pure []
  let (res, tbl, prem, fns) ← run img syms env given
  -- `INFER_TRACE=addr,...`: what a function wants, and what its call sites give it.
  if let some tr := (← IO.getEnv "INFER_TRACE") then
    let tblM : Std.HashMap Word Iface := tbl.foldl (fun acc g => acc.insert g.entry g) {}
    let ctxOf (f : Fn) : Ctx' :=
      let p := prem.getD f.base {}
      { env, tbl := tblM, pending := {}, f, vals := p.vals, cvals := p.cvals, permissive := true,
        strs := ((tblM[f.base]?).map (·.strs)).getD [] }
    let mut allSites : Array (Word × Site) := #[]
    for (_, f) in fns do
      if let .ok (_, need) := (ctxOf f).analyze then
        allSites := allSites ++ (need.sites.map (f.base, ·)).toArray
    -- `INFER_REACH=addr`: the functions reachable from `addr`, with their own problems.
    if let some ra := (← IO.getEnv "INFER_REACH") >>= parseHex? then
      let mut seen : Std.HashSet Word := {}
      let mut work : List Word := [BitVec.ofNat 64 ra]
      while !work.isEmpty do
        let w := work.head!
        work := work.tail
        if seen.contains w then continue
        seen := seen.insert w
        for (cb, site) in allSites do
          if cb == w then work := site.tgt :: work
      for w in seen.toList.mergeSort (fun a b => a.toNat ≤ b.toNat) do
        let st := (res.find? (·.sym.addr == w.toNat)).map fun r => match r.status with
          | .ok _ => "ok"
          | .error e => "; ".intercalate (((e.splitOn "; ").filter fun m =>
              (m.splitOn "has no interface").length ≤ 1).map fun m => (m.drop 18).toString)
        let nm := (res.find? (·.sym.addr == w.toNat)).map (·.sym.name)
        IO.println s!"reach {hex w.toNat 8} {st.getD "?"} {nm.getD ""}"
    for a in tr.splitOn "," do
      let some a := parseHex? a | continue
      let some (_, f) := fns.find? (·.2.base.toNat == a) | continue
      IO.println s!"trace {hex a 8}: status {(res.find? (·.sym.addr == a)).map fun r => match r.status with | .ok _ => "ok" | .error e => e}"
      let p := prem.getD f.base {}
      IO.println s!"  vals {p.vals.map fun (r, cs) => (regIdx r, cs.length)} cvals {p.cvals.map fmtCell}"
      match (ctxOf f).analyze with
      | .ok (_, need) =>
        IO.println s!"  wants {need.wants.map fmtCell} wantRegs {need.wantRegs.map regIdx} sites-out {need.sites.map (hex ·.tgt.toNat 8)}"
      | .error (.fail pc m _) => IO.println s!"  permissive analysis failed: {pc.toHex}: {m}"
      | .error (.blocked g) => IO.println s!"  permissive analysis blocked on {g.toHex}"
      for (cb, site) in allSites do
        if site.tgt != f.base then continue
        IO.println s!"  site from {hex cb.toNat 8}: {(argRegs.map site.st.get).map fmtAVal}"
  let mut rows : Array String := #["addr\twords\tstatus\tdetail\tdepth\tfoot\tnz\treturns\tname"]
  let mut nOk := 0
  let mut words := 0
  let mut reasons : Std.HashMap String Nat := {}
  for r in res do
    match r.status with
    | .ok (σ, _, _) =>
      nOk := nOk + 1; words := words + r.func.prog.length
      let how := if r.given.isSome then "proved" else "ok"
      rows := rows.push s!"{hex r.sym.addr 8}\t{r.func.prog.length}\t{how}\t\t{σ.depth}\t{σ.foot.length}\t{σ.nz.length}\t{σ.returns}\t{r.sym.name}"
    | .error e =>
      let key := String.ofList (((e.splitOn ": ").drop 1 |> ": ".intercalate).toList.take 40)
      reasons := reasons.insert key (reasons.getD key 0 + 1)
      rows := rows.push s!"{hex r.sym.addr 8}\t{r.func.prog.length}\tfail\t{e}\t\t\t\t\t{r.sym.name}"
  IO.FS.writeFile outPath ("\n".intercalate rows.toList ++ "\n")
  if let [dir, modPrefix, imgPrefix, layoutPath] := (args.drop 6).take 4 then
    let index := layoutIndex (← IO.FS.readFile layoutPath)
    let n ← emit dir modPrefix imgPrefix env tbl res index
    IO.println s!"infer-contracts: emitted {n} functions to {dir}"
  IO.println s!"infer-contracts: {nOk} of {res.size} functions get an interface ({words} words)"
  IO.println s!"infer-contracts: {prem.size} functions have candidate-set premises"
  for (a, p) in prem.toList do
    IO.println s!"    {hex a.toNat 8}: {p.vals.map fun (r, cs) => (regIdx r, cs.length)} {p.cvals.map fun c => (regIdx c.r, c.ks.map (·.toNat), c.k.toNat, (c.vals.getD []).length)}"
  let rs := reasons.toList.mergeSort (fun a b => a.2 ≥ b.2)
  for (k, v) in rs do IO.println s!"  {v}\t{k}"
  return 0

end Tools.Infer

def main (args : List String) : IO UInt32 := Tools.Infer.main args
