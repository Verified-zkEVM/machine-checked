/-
  Tools.Infer

  Infer an interface (`Check.Iface`) and a certificate (an annotation) for every function of
  an image, bottom-up over the call graph, and emit them as Lean for the kernel to check.

      lake exe infer-contracts ELF NM OUT.tsv [LEANDIR MODPREFIX IMGPREFIX]

  Untrusted. The abstract interpretation here mirrors `Check.Ctx.stepAt`, with the checks
  against the function's own interface replaced by *recording* what the interface must
  allow: the stack depth, footprint items, nonzero premises, whether it returns. The
  interface is then exactly what was recorded, the real checker (`Ctx.valid`) is run on
  the result as a sanity check, and the kernel re-runs it.

  A function gets no interface when its analysis meets something the checker does not
  model: an indirect call or jump, a store through an unknown pointer, an `ecall`, a store
  above its entry stack pointer, a callee without an interface, or recursion.
-/

import RiscvZkvm.Interpreter
import AsmVerif.RiscV.Check.Spec
import Tools.Elf

namespace Tools.Infer

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter AsmVerif.RiscV.Check Tools.Elf
open AsmVerif.RiscV.Frame (AVal AState Fn aluResult loadOf storeOf Width mayHit branchOff? joinAt
  regIdx)

/-! ## What a function's interface must allow -/

structure Need where
  depth : Nat := 0
  items : List Item := []
  nz : List AVal := []
  returns : Bool := false
  frags : List Word := []

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

def Ctx'.lookup (c : Ctx') (pc tgt : Word) : M Iface := do
  match c.tbl[tgt]? with
  | some g => pure g
  | none => if c.pending.contains tgt then throw (.blocked tgt) else bad pc s!"callee {tgt.toHex} has no interface"

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
      if b = .top then bad pc "store through an unknown pointer"
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

def nzI (pc : Word) (A : AState) (v : AVal) : M Unit := nzV pc (instVal A v)

/-- An item a syscall writes, checked as `itemOk σ σ.depth` will check it. -/
def sysItemI (pc : Word) (it : Item) : M Unit := do
  match it.base.frameOff?, it.len with
  | some k, .n l =>
    if !(l ≤ negOff k) then bad pc "syscall writes a frame item above the entry stack pointer"
    needDepth (negOff k)
  | some _, _ => bad pc "syscall writes a frame item of register length"
  | none, _ =>
    if it.base == .top then bad pc "syscall writes through an unknown pointer"
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

def tailI (pc : Word) (A : AState) (g : Iface) : M Unit := do
  if !okExit A then bad pc "tail call without the callee-saved registers restored"
  needDepth g.depth
  if g.returns then modify fun n => { n with returns := true }
  let its ← instItems pc A g
  for it in its do
    if it.base.frameOff?.isSome || it.base == .top then
      bad pc "tail call passes a frame or unknown pointer the callee writes through"
    modify (·.addItem it)
  for v in g.nz do nzI pc A v

def Ctx'.jump (c : Ctx') (pc : Word) (A : AState) (tgt : Word) : M (List Edge) := do
  match c.f.idx? tgt with
  | some j => pure [.goto j A]
  | none =>
    let g ← c.lookup pc tgt
    tailI pc A g
    pure []

def Ctx'.call (c : Ctx') (pc : Word) (A : AState) (tgt : Word) : M (List Edge) := do
  let g ← c.lookup pc tgt
  let A1 := A.set .x1 (.const (pc + 4))
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
      if it.base == .top then bad pc "callee writes through a pointer the caller does not know"
      modify (·.addItem it)
  for v in g.nz do nzI pc A1 v
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
          | _ => bad pc "indirect jump"
      else if rd = .x1 then
        match A.get rs with
        | .const t => c.call pc A ((t + signExtend12 off) &&& ~~~1#64)
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
  let mut anno : Array (Option AState) := (List.replicate n none).toArray.set! 0 (some AState.entry)
  let mut work : List Nat := [0]
  let mut fuel := 64 * n + 64
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
  if !fails.isEmpty then throw (.fail c.f.base ("; ".intercalate fails))
  let mut need : Need := {}
  for i in List.range n do
    let some (some A) := anno[i]? | continue
    let some oi := c.f.prog[i]? | continue
    let (_, nd) ← (c.stepAt (c.f.pcOf i) oi A).run need
    need := nd
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

def mkIface (entry : Word) (n : Need) : Iface :=
  { entry, depth := n.depth, foot := mergeItems n.items, nz := n.nz.reverse, returns := n.returns }

/-! ## Lean output -/

def regName (r : Reg) : String := s!".x{regIdx r}"
def word (w : Word) : String := s!"0x{w.toHex}#64"
def fmtAVal : AVal → String
  | .lin r k => s!"(.lin {regName r} {word k})"
  | .const c => s!"(.const {word c})"
  | .top => ".top"
def fmtLen : Len → String
  | .n l => s!"(.n {l})"
  | .reg r => s!"(.reg {regName r})"
  | .regPlus r c => s!"(.regPlus {regName r} {c})"
def fmtItem (it : Item) : String := s!"\{ base := {fmtAVal it.base}, len := {fmtLen it.len} }"
def fmtList (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"
def fmtState (A : AState) : String :=
  s!"some \{ regs := {fmtList (A.regs.map fmtAVal)}, slots := {fmtList (A.slots.map fun (k, v) => s!"({word k}, {fmtAVal v})")} }"
def fmtIface (σ : Iface) : String :=
  s!"\{ entry := {word σ.entry}, depth := {σ.depth}, foot := {fmtList (σ.foot.map fmtItem)}, " ++
  s!"nz := {fmtList (σ.nz.map fmtAVal)}, returns := {σ.returns} }"

end Tools.Infer

namespace Tools.Infer

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter AsmVerif.RiscV.Check Tools.Elf
open AsmVerif.RiscV.Frame (AVal AState Fn aluResult loadOf storeOf Width mayHit branchOff? joinAt
  regIdx)

/-- The doubleword at `a`, little-endian, from the segment holding it (zero elsewhere). -/
def memAt (img : Elf64Image) (a : Nat) : Word :=
  match img.segments.find? (fun s => s.vaddr ≤ a && a + 8 ≤ s.vaddr + s.memsz) with
  | none => 0
  | some seg =>
    let b (i : Nat) : Nat := if a - seg.vaddr + i < seg.data.size then (seg.data.get! (a - seg.vaddr + i)).toNat else 0
    BitVec.ofNat 64 ((List.range 8).foldr (fun i acc => acc * 256 + b i) 0)

structure Result where
  sym : Sym
  func : Fn
  status : Except String (Iface × Array (Option AState) × List Word)

def run (img : Elf64Image) (syms : List Sym) (env : Env) : IO (Array Result × List Iface) := do
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
  let mut done : Std.HashMap Word (Iface × Array (Option AState) × List Word) := {}
  let mut failed : Std.HashMap Word String := {}
  let mut pending : Std.HashSet Word := fns.foldl (fun acc (_, f) => acc.insert f.base) {}
  let mut changed := true
  while changed do
    changed := false
    for (_, f) in fns do
      if !pending.contains f.base then continue
      let tbl : Std.HashMap Word Iface := done.fold (fun acc k v => acc.insert k v.1) {}
      match ({ env, tbl, pending := pending.erase f.base, f } : Ctx').analyze with
      | .ok (anno, need) =>
        done := done.insert f.base (mkIface f.base need, anno, need.frags)
        pending := pending.erase f.base
        changed := true
      | .error (.fail pc msg) =>
        failed := failed.insert f.base s!"{pc.toHex}: {msg}"
        pending := pending.erase f.base
        changed := true
      | .error (.blocked _) => pure ()
  for b in pending do failed := failed.insert b "recursion (a cycle of calls)"
  let tbl : List Iface := (fns.toList.filterMap fun (_, f) => (done[f.base]?).map (·.1))
  let mut out : Array Result := #[]
  for (s, f) in fns do
    match done[f.base]? with
    | some (σ, anno, used) =>
      let f' := { f with frags := f.frags.filter fun (b, _) => used.contains b }
      let ok := ({ env, tbl, σ, f := f' } : Ctx).valid anno
      let st : Except String (Iface × Array (Option AState) × List Word) :=
        if ok then .ok (σ, anno, used) else .error "inferred, but the checker rejects it"
      out := out.push ⟨s, f', st⟩
    | none => out := out.push ⟨s, f, .error (failed.getD f.base "?")⟩
  return (out, tbl)

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
  let (res, _) ← run img syms env
  let mut rows : Array String := #["addr\twords\tstatus\tdetail\tdepth\tfoot\tnz\treturns\tname"]
  let mut nOk := 0
  let mut words := 0
  let mut reasons : Std.HashMap String Nat := {}
  for r in res do
    match r.status with
    | .ok (σ, _, _) =>
      nOk := nOk + 1; words := words + r.func.prog.length
      rows := rows.push s!"{hex r.sym.addr 8}\t{r.func.prog.length}\tok\t\t{σ.depth}\t{σ.foot.length}\t{σ.nz.length}\t{σ.returns}\t{r.sym.name}"
    | .error e =>
      let key := String.ofList (((e.splitOn ": ").drop 1 |> ": ".intercalate).toList.take 40)
      reasons := reasons.insert key (reasons.getD key 0 + 1)
      rows := rows.push s!"{hex r.sym.addr 8}\t{r.func.prog.length}\tfail\t{e}\t\t\t\t\t{r.sym.name}"
  IO.FS.writeFile outPath ("\n".intercalate rows.toList ++ "\n")
  IO.println s!"infer-contracts: {nOk} of {res.size} functions get an interface ({words} words)"
  let rs := reasons.toList.mergeSort (fun a b => a.2 ≥ b.2)
  for (k, v) in rs do IO.println s!"  {v}\t{k}"
  return 0

end Tools.Infer

def main (args : List String) : IO UInt32 := Tools.Infer.main args
