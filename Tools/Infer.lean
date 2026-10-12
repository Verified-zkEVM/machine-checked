/-
  Tools.Infer

  Infer an interface (`Check.Iface`) and a certificate (an annotation) for every function of
  an image, bottom-up over the call graph, and emit them as Lean for the kernel to check.

      lake exe infer-contracts ELF NM OUT.tsv STACKTOP PROTLO PROTHI
        [LEANDIR MODPREFIX IMGPREFIX LAYOUT [REGISTRY]]

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

structure Need where
  depth : Nat := 0
  items : List Item := []
  nz : List AVal := []
  returns : Bool := false
  frags : List Word := []
  /-- Call sites: the callee and the values passed in `a0`-`a7`. -/
  sites : List (Word × List AVal) := []

def Need.addItem (n : Need) (it : Item) : Need :=
  if n.items.contains it then n else { n with items := it :: n.items }

def Need.addNz (n : Need) (v : AVal) : Need :=
  if n.nz.contains v then n else { n with nz := v :: n.nz }

/-- Why the analysis gave up. `blocked` names a callee still being worked on. -/
inductive Why where
  | fail (pc : Word) (msg : String)
  | blocked (callee : Word)

abbrev M := StateT Need (Except Why)

def bad (pc : Word) (msg : String) : M α := throw (.fail pc msg)

structure Ctx' where
  env : Env
  tbl : Std.HashMap Word Iface
  pending : Std.HashSet Word
  f : Fn
  /-- The function's `vals` premises. -/
  vals : List (Reg × List Word) := []
  /-- Collecting call sites: unknown callees havoc and return, nothing is rejected for
      want of a callee's premises. -/
  permissive : Bool := false

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
      else
        modify (·.addItem { base := b, len := .n (wbytes w) })
        pure A

def plainI (env : Env) (pc : Word) (A : AState) (i : Instr) : M AState := do
  match aluResult pc A i with
  | some (rd, v) => pure (A.set rd v)
  | none =>
  match loadOf i with
  | some (rd, rs, off, isD) => pure (A.set rd (loadVal env A ((A.get rs).addK (signExtend12 off)) isD))
  | none =>
  match storeOf i with
  | some (rs1, rs2, off, w) => storeI pc A rs1 rs2 off w
  | none =>
  match i with
  | .NOP | .FENCE => pure A
  | _ => bad pc s!"unmodeled {(repr i).pretty 80}"

def instItems (pc : Word) (A : AState) (g : Iface) : M (List Item) :=
  g.foot.mapM fun it => match instItem A it with
    | some it' => pure it'
    | none => bad pc s!"callee item {(repr it).pretty 80} cannot be instantiated"

/-- Record that a value (in this function's terms) must be nonzero. -/
def nzV (pc : Word) : AVal → M Unit
  | .const c => if c != 0 then pure () else bad pc "a value that must be nonzero is 0"
  | .lin r k => modify (·.addNz (.lin r k))
  | .top => bad pc "a value that must be nonzero is unknown"
  | .oneOf cs => if cs.all (· != 0) then pure () else bad pc "a value that must be nonzero may be 0"

def nzI (pc : Word) (A : AState) (v : AVal) : M Unit := nzV pc (instVal A v)

/-- An item a syscall writes, checked as `itemOk σ σ.depth` will check it. -/
def sysItemI (pc : Word) (it : Item) : M Unit := do
  match it.base.frameOff?, it.len with
  | some k, .n l =>
    if !(l ≤ negOff k) then bad pc "syscall writes a frame item above the entry stack pointer"
    needDepth (negOff k)
  | some _, _ => bad pc "syscall writes a frame item of register length"
  | none, _ =>
    if !it.base.isPtr then bad pc "syscall writes through an unknown pointer"
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

/-- A callee's `vals` premise, discharged by the caller's value. -/
def valI (pc : Word) (A : AState) (p : Reg × List Word) : M Unit :=
  if valOk A p then pure ()
  else bad pc s!"callee needs x{regIdx p.1} among {p.2.length} candidates"

def tailI (pc : Word) (A : AState) (g : Iface) : M Unit := do
  if !okExit A then bad pc "tail call without the callee-saved registers restored"
  needDepth g.depth
  if g.returns then modify fun n => { n with returns := true }
  let its ← instItems pc A g
  for it in its do
    if it.base.frameOff?.isSome || !it.base.isPtr then
      bad pc "tail call passes a frame or unknown pointer the callee writes through"
    modify (·.addItem it)
  for v in g.nz do nzI pc A v
  for p in g.vals do valI pc A p

def Ctx'.jump (c : Ctx') (pc : Word) (A : AState) (tgt : Word) : M (List Edge) := do
  match c.f.idx? tgt with
  | some j => pure [.goto j A]
  | none =>
    let g ← c.lookup pc tgt
    modify fun n => { n with sites := (tgt, argRegs.map A.get) :: n.sites }
    if !c.permissive then tailI pc A g
    pure []

def Ctx'.call (c : Ctx') (pc : Word) (A : AState) (tgt : Word) : M (List Edge) := do
  let g ← c.lookup pc tgt
  let A1 := A.set .x1 (.const (pc + 4))
  modify fun n => { n with sites := (tgt, argRegs.map A1.get) :: n.sites }
  let some m := spOff A1 | bad pc "call with the stack pointer not a known 8-aligned frame offset"
  needDepth (m + g.depth)
  let its ← instItems pc A1 g
  for it in its do
    match it.base.frameOff?, it.len with
    | some k, .n l =>
      if !(l ≤ negOff k && negOff k ≤ m) then
        bad pc s!"callee writes a frame item outside the caller's frame above its stack pointer"
    | some _, _ => bad pc "callee writes a frame item of register length"
    | none, _ =>
      if !it.base.isPtr then bad pc "callee writes through a pointer the caller does not know"
      modify (·.addItem it)
  for v in g.nz do nzI pc A1 v
  if !c.permissive then for p in g.vals do valI pc A1 p
  if g.returns then
    if (pc + 4) &&& ~~~1#64 != pc + 4 then bad pc "misaligned return address"
    match c.f.idx? (pc + 4) with
    | some j => pure [.goto j (afterCall A m its)]
    | none => bad pc "returning call at the end of the function"
  else pure []

def Ctx'.runFrag (c : Ctx') (pc0 : Word) (A : AState) (fbase : Word) :
    List (Option Instr) → Nat → M AState
  | [], _ => bad pc0 "fragment without its return"
  | some i :: rest, n =>
      if i = .JALR .x0 .x5 0 then pure A else do
      let B ← plainI c.env (fbase + BitVec.ofNat 64 (4 * n)) A i
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
          if B.get .x5 = .const (pc + 4) ∧ (pc + 4) &&& ~~~1#64 = pc + 4 then pure [.goto j B]
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
      let e1 ← c.jump pc A (pc + 4)
      let e2 ← c.jump pc A (pc + signExtend13 off)
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
        else match A.get rs with
          | .const t => c.jump pc A ((t + signExtend12 off) &&& ~~~1#64)
          | .oneOf ts => return (← ts.mapM fun t => c.jump pc A ((t + signExtend12 off) &&& ~~~1#64)).flatten
          | _ => bad pc "indirect jump"
      else if rd = .x1 then
        match A.get rs with
        | .const t => c.call pc A ((t + signExtend12 off) &&& ~~~1#64)
        | .oneOf ts => return (← ts.mapM fun t => c.call pc A ((t + signExtend12 off) &&& ~~~1#64)).flatten
        | _ => bad pc "indirect call"
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
      let B ← plainI c.env pc A ins
      c.jump pc B (pc + 4)

/-- Kildall over instruction indices, then one pass to record what every reachable
    instruction needs. An instruction the analysis rejects is recorded and treated as having
    no successor, so that one run reports every problem; the function then gets no interface. -/
def Ctx'.analyze (c : Ctx') : Except Why (Array (Option AState) × Need) := do
  let n := c.f.prog.length
  let entry := ({ entry := c.f.base, depth := 0, vals := c.vals } : Iface).entryState
  let mut anno : Array (Option AState) := (List.replicate n none).toArray.set! 0 (some entry)
  let mut work : List Nat := [0]
  let mut fuel := 256 * n + 64
  let mut fails : List String := []
  while !work.isEmpty do
    if fuel = 0 then throw (.fail c.f.base "no fixpoint")
    fuel := fuel - 1
    let i := work.head!
    work := work.tail
    let some (some A) := anno[i]? | continue
    let some oi := c.f.prog[i]? | throw (.fail c.f.base "index out of range")
    let es ← match (c.stepAt (c.f.pcOf i) oi A).run {} with
      | .ok (es, _) => pure es
      | .error (.fail pc msg) =>
        let m := s!"{pc.toHex}: {msg}"
        if !fails.contains m then fails := fails ++ [m]
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
  let mut need : Need := {}
  for i in List.range n do
    let some (some A) := anno[i]? | continue
    let some oi := c.f.prog[i]? | continue
    match (c.stepAt (c.f.pcOf i) oi A).run need with
    | .ok (_, nd) => need := nd
    | .error e => if c.permissive then continue else throw e
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

def mkIface (entry : Word) (n : Need) (vals : List (Reg × List Word)) : Iface :=
  { entry, depth := n.depth, foot := mergeItems n.items, nz := n.nz.reverse, returns := n.returns,
    vals }

/-! ## Lean output -/

def regName (r : Reg) : String := s!".x{regIdx r}"
def word (w : Word) : String := s!"0x{w.toHex}#64"
def fmtWords (cs : List Word) : String := "[" ++ ", ".intercalate (cs.map word) ++ "]"
def fmtAVal : AVal → String
  | .lin r k => s!"(.lin {regName r} {word k})"
  | .const c => s!"(.const {word c})"
  | .top => ".top"
  | .oneOf cs => s!"(.oneOf {fmtWords cs})"
def fmtLen : Len → String
  | .n l => s!"(.n {l})"
  | .reg r => s!"(.reg {regName r})"
  | .regPlus r c => s!"(.regPlus {regName r} {c})"
def fmtItem (it : Item) : String := s!"\{ base := {fmtAVal it.base}, len := {fmtLen it.len} }"
def fmtList (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"
def fmtState (A : AState) : String :=
  let regs := allRegs.map fun r => (r, A.regs.getD (regIdx r) .top)
  let diff := regs.filterMap fun (r, v) => if v == .lin r 0 then none else some s!"({regName r}, {fmtAVal v})"
  let known := regs.filterMap fun (r, v) => if v == .top then none else some s!"({regName r}, {fmtAVal v})"
  let slots := fmtList (A.slots.map fun (k, v) => s!"({word k}, {fmtAVal v})")
  if diff.length ≤ known.length then s!"some (.ofDiff {fmtList diff} {slots})"
  else s!"some (.ofKnown {fmtList known} {slots})"
def fmtIface (σ : Iface) : String :=
  s!"\{ entry := {word σ.entry}, depth := {σ.depth}, foot := {fmtList (σ.foot.map fmtItem)}, " ++
  s!"nz := {fmtList (σ.nz.map fmtAVal)}, returns := {σ.returns}, " ++
  s!"vals := {fmtList (σ.vals.map fun (r, cs) => s!"({regName r}, {fmtWords cs})")} }"

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

    depth=N foot=ITEM,ITEM nz=VAL,VAL ret=0|1

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
    | ["ret", r] => σ := { σ with returns := r == "1" }
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

structure Result where
  sym : Sym
  func : Fn
  status : Except String (Iface × Array (Option AState) × List Word)
  given : Option Given := none

def run (img : Elf64Image) (syms : List Sym) (env : Env) (given : List Given) :
    IO (Array Result × List Iface × Std.HashMap Word (List (Reg × List Word))) := do
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
  -- Bottom-up, under the given `vals` premises.
  let bottomUp (vals : Std.HashMap Word (List (Reg × List Word))) :
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
        let vs := vals.getD f.base []
        match ({ env, tbl, pending := pending.erase f.base, f, vals := vs } : Ctx').analyze with
        | .ok (anno, need) =>
          done := done.insert f.base (mkIface f.base need vs, anno, need.frags)
          pending := pending.erase f.base
          changed := true
        | .error (.fail pc msg) =>
          failed := failed.insert f.base s!"{pc.toHex}: {msg}"
          pending := pending.erase f.base
          changed := true
        | .error (.blocked _) => pure ()
    return (done, failed, pending)
  -- Call sites, permissively, under the given premises and the interfaces found so far.
  let collect (vals : Std.HashMap Word (List (Reg × List Word))) (tbl : Std.HashMap Word Iface) :
      Std.HashMap Word (List (Reg × List Word)) := Id.run do
    let mut seen : Std.HashMap Word (List AVal) := {}
    for (_, f) in fns do
      let c : Ctx' := { env, tbl, pending := {}, f, vals := vals.getD f.base [], permissive := true }
      if let .ok (_, need) := c.analyze then
        for (tgt, vs) in need.sites do
          seen := seen.insert tgt (match seen[tgt]? with
            | some ws => (ws.zip vs).map fun (a, b) => a.join b
            | none => vs)
    let mut out : Std.HashMap Word (List (Reg × List Word)) := {}
    for (tgt, vs) in seen.toList do
      if givenAt.contains tgt then continue
      let ps := (argRegs.zip vs).filterMap fun (r, v) => match v with
        | .const c => if useful c then some (r, [c]) else none
        | .oneOf cs => if cs.all useful then some (r, cs) else none
        | _ => none
      if !ps.isEmpty then out := out.insert tgt ps
    return out
  let mut vals : Std.HashMap Word (List (Reg × List Word)) := {}
  let mut (done, failed, pending) := bottomUp vals
  for _ in [0:6] do
    let tbl0 : Std.HashMap Word Iface := done.fold (fun acc k v => acc.insert k v.1) {}
    let vals' := collect vals tbl0
    if vals'.toList.mergeSort (fun a b => a.1.toNat ≤ b.1.toNat) ==
        vals.toList.mergeSort (fun a b => a.1.toNat ≤ b.1.toNat) then break
    vals := vals'
    (done, failed, pending) := bottomUp vals
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
      let ok := ({ env, tbl, σ, f := f' } : Ctx).valid anno
      let st : Except String (Iface × Array (Option AState) × List Word) :=
        if ok then .ok (σ, anno, used) else .error "inferred, but the checker rejects it"
      out := out.push { sym := s, func := f', status := st }
    | none => out := out.push { sym := s, func := f, status := .error (failed.getD f.base "?") }
  return (out, tbl, vals)

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

/-- The states a sparse certificate must give: where fall-through propagation does not
    already produce the annotation's state. -/
def hintsFor (c : Ctx) (anno : Array (Option AState)) : List (Nat × AState) := Id.run do
  let mut out : Array (Nat × AState) := #[]
  let mut prev : Option AState := none
  for i in List.range anno.size do
    let a := anno[i]!
    if a != prev then
      if let some A := a then out := out.push (i, A)
    prev := match a, c.f.prog[i]? with
      | some A, some oi => match c.stepAt (c.f.pcOf i) oi A with
        | some es => fallState A (i + 1) es
        | none => none
      | _, _ => none
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
    if (c.fill hints).toList != anno.toList then
      throw <| IO.userError s!"{a}: the sparse certificate does not fill back to the annotation"
    if !c.validFast anno then throw <| IO.userError s!"{a}: validFast rejects the annotation"
    let body := ",\n  ".intercalate (hints.map fun (i, A) =>
      s!"({i}, {(fmtState A).drop 5 |>.toString})")
    IO.FS.writeFile s!"{dir}/A_{a}.lean" <|
      hdr s!"`{r.sym.name}`: its interface and certificate." ++
      s!"import AsmVerif.RiscV.Check.Domain\nimport {imgPrefix}.F_{a}\n" ++ String.join fragImports ++
      s!"\nset_option maxRecDepth 200000\n\nnamespace {modPrefix}.A_{a}\n\n" ++ opens ++
      s!"def iface : Iface := {fmtIface σ}\n\n" ++
      s!"def fn : Fn := \{ base := {imgPrefix}.F_{a}.base, prog := {imgPrefix}.F_{a}.prog, frags := {frags} }\n\n" ++
      s!"noncomputable def hints : List (Nat × AState) := [\n  {body}]\n\nend {modPrefix}.A_{a}\n"
  -- The table.
  let protS := fmtList (env.prot.map fun (b, l) => s!"({word b}, {l})")
  IO.FS.writeFile s!"{dir}/Table.lean" <|
    hdr "The program's `Env` and the table of inferred interfaces." ++
    s!"import AsmVerif.RiscV.Check.Spec\nimport {imgPrefix}.Layout\n" ++
    String.join (ok.toList.map fun (r, _) => s!"import {modPrefix}.A_{hex r.sym.addr 8}\n") ++
    String.join (gv.toList.map fun g => s!"import {g.module}\n") ++
    s!"\nnamespace {modPrefix}\n\n" ++ opens ++
    s!"noncomputable def env : Env :=\n  \{ stackTop := {env.stackTop}, prot := {protS}, init := {imgPrefix}.Layout.image.memAt }\n\n" ++
    "theorem env_wf : env.wf = true := by decide +kernel\n\n" ++
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
      s!"noncomputable abbrev ctx : Ctx := ⟨env, tbl, A_{a}.iface, A_{a}.fn⟩\n\n" ++
      s!"noncomputable def anno : Array (Option AState) := ctx.fill A_{a}.hints\n\n" ++
      s!"theorem valid : ctx.valid anno = true := Ctx.validFast_sound (by decide +kernel)\n\n" ++
      s!"theorem decode : decodeWords {imgPrefix}.F_{a}.words = {imgPrefix}.F_{a}.prog := by decide +kernel\n\n" ++
      fragDecodes ++
      s!"theorem code : CodeAt A_{a}.fn {imgPrefix}.Layout.image.codeAt :=\n  codeAt_of_image (k := {k}) Cases.Zip2005.Loaded.codeWF rfl decode\n  {fragProof}\n\n" ++
      s!"theorem holds (n : Nat) (h : ∀ g ∈ tbl, ∀ m < n, g.HoldsN env {imgPrefix}.Layout.image.codeAt m) :\n" ++
      s!"    A_{a}.iface.HoldsN env {imgPrefix}.Layout.image.codeAt n :=\n" ++
      s!"  Ctx.sound (c := ctx) valid code (by decide +kernel) env_wf h\n\n" ++
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
  let env : Env := { stackTop, prot := [(BitVec.ofNat 64 protLo, protHi - protLo)],
                     init := fun a => memAt img a.toNat }
  if !env.wf then IO.eprintln "infer-contracts: Env not well-formed"; return 1
  let given ← match args.drop 10 with
    | [regPath] => match parseGiven (← IO.FS.readFile regPath) with
      | .ok g => pure g
      | .error e => IO.eprintln s!"infer-contracts: {e}"; return 1
    | _ => pure []
  let (res, tbl, vals) ← run img syms env given
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
  IO.println s!"infer-contracts: {vals.size} functions have candidate-set premises"
  for (a, ps) in vals.toList do
    IO.println s!"    {hex a.toNat 8}: {ps.map fun (r, cs) => (regIdx r, cs.map fun (c : Word) => hex c.toNat 8)}"
  let rs := reasons.toList.mergeSort (fun a b => a.2 ≥ b.2)
  for (k, v) in rs do IO.println s!"  {v}\t{k}"
  return 0

end Tools.Infer

def main (args : List String) : IO UInt32 := Tools.Infer.main args
