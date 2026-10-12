/-
  AsmVerif.RiscV.Frame.Domain

  A frame analysis for one function activation, computable so that the kernel can run it.

  The question it answers is return-address integrity: at every way the activation leaves
  its function (a `ret`, or any non-call transfer out of the function's address range), `ra`
  and `sp` hold their entry values.

  ## The domain

  Every register is abstracted as one of
    * `lin r k` -- the value register `r` had at entry, plus the constant `k`;
    * `const c` -- a known constant (from `lui`/`auipc`/`li`);
    * `top`     -- unknown.
  `ra` at entry is `lin x1 0`, `sp` is `lin x2 0`, a pointer argument in `a0` is `lin x10 0`,
  a frame address is `lin x2 k`. One shape covers all of them.

  `slots` records stack words known to hold an abstract value: `(k, v)` means the
  doubleword at `entry sp + k` holds `v`. Saving `ra` makes `(k, lin x1 0)` a slot and
  `ld ra` from it restores `lin x1 0`. That is how `ra` used as a scratch register between
  a save and a restore is handled.

  ## What a store owes

  A store through a frame address (`lin x2 k`) updates `slots` exactly. Any other store
  could hit a live slot. Slots holding anything but a return address are forgotten (sound,
  free); for a return-address slot the analysis records what has to be true for the store
  not to hit it:
    * base `lin r k` or `const c`: a premise over the ENTRY registers only (`Req`),
      e.g. "`a0 + 0x18` is not the doubleword at `sp - 8`";
    * base `top`: a premise over the run at that pc (`residual`).
  With no live slot, a store owes nothing.

  ## Calls

  A call (`jal`/`jalr` writing `ra`) is a macro-step governed by a contract: the callee
  returns to the next instruction, preserves `sp` and `s0`-`s11`, and leaves every live
  slot's doubleword unchanged. The analysis keeps callee-saved registers and slots across
  the call and forgets the rest. A call whose return address lies outside the function is
  recorded as assumed not to return (`noreturn`).

  A machine-outliner call (`jalr t0, ...` to a known address) is NOT a contract: the
  fragment's instructions are abstractly executed in place, since it writes our frame.

  This file is the computation. Soundness against `stepSp1` is `Frame.Sound`.
-/

import RiscvZkvm.Rv64

namespace AsmVerif.RiscV.Frame

open RiscvZkvm.Rv64

/-! ## Abstract values -/

inductive AVal where
  | lin (r : Reg) (k : Word)
  | const (c : Word)
  | top
  deriving DecidableEq, Repr, Inhabited

namespace AVal

def addK : AVal → Word → AVal
  | .lin r k, d => .lin r (k + d)
  | .const c, d => .const (c + d)
  | .top, _ => .top

/-- The frame offset of a frame address (`lin x2 k`). Matching on a specific register
    inside a pattern expands into Lean's 32-way case tree for `Reg`; testing it with `if`
    keeps proofs that `split` on this result small. -/
def frameOff? : AVal → Option Word
  | .lin r k => if r = .x2 then some k else none
  | _ => none

/-- `v` is a concretization of the abstract value, given the entry register file `E`. -/
def Holds (E : Reg → Word) : AVal → Word → Prop
  | .lin r k, v => v = E r + k
  | .const c, v => v = c
  | .top, _ => True

end AVal

/-! ## Abstract states -/

def allRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
   .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
   .x30, .x31]

/-- The registers a callee preserves under the RISC-V calling convention. -/
def calleeSaved : List Reg :=
  [.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- A register's index in the register file. -/
def regIdx : Reg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3 | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11 | .x12 => 12 | .x13 => 13 | .x14 => 14
  | .x15 => 15 | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19 | .x20 => 20 | .x21 => 21
  | .x22 => 22 | .x23 => 23 | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27 | .x28 => 28
  | .x29 => 29 | .x30 => 30 | .x31 => 31

/-- An abstract register file is concrete data (32 entries, by `regIdx`), not a function:
    a function built by repeated `set`/`join` is a closure tree whose evaluation grows
    exponentially with the number of joins. -/
structure AState where
  regs : List AVal
  slots : List (Word × AVal)
  deriving DecidableEq, Repr

/-- Slots worth protecting from a store that might hit them: the saved return address.
    Every other slot is simply forgotten (sound, and owes nothing). -/
def protects : Word × AVal → Bool
  | (_, .lin .x1 _) => true
  | _ => false

namespace AState

def get (A : AState) (r : Reg) : AVal :=
  if r = .x0 then .const 0 else A.regs.getD (regIdx r) .top

def set (A : AState) (r : Reg) (v : AVal) : AState :=
  { A with regs := A.regs.set (regIdx r) v }

/-- The entry state: every register is its own entry value, no slots. -/
def entry : AState := { regs := allRegs.map (fun r => .lin r 0), slots := [] }

/-- `A ≤ B`: every fact of `B` is a fact of `A`. -/
def le (A B : AState) : Bool :=
  allRegs.all (fun r => B.get r == .top || B.get r == A.get r) &&
  B.slots.all (fun p => A.slots.contains p)

def join (A B : AState) : AState :=
  { regs := allRegs.map (fun r => if A.get r = B.get r then A.get r else .top)
    slots := A.slots.filter (fun p => B.slots.contains p) }

def beq (A B : AState) : Bool := le A B && le B A

/-- The state a call contract leaves: callee-saved registers kept, and the return-address
    slots, which are what the contract protects. -/
def afterCall (A : AState) : AState :=
  { regs := allRegs.map (fun r => if calleeSaved.contains r then A.get r else .top),
    slots := A.slots.filter protects }

end AState

/-! ## What stores owe -/

/-- The width of a store, as far as slots care: a doubleword store writes `mem addr`; a
    narrower one rewrites `mem (alignToDword addr)`. -/
inductive Width where
  | d
  | sub
  deriving DecidableEq, Repr

def Width.target : Width → Word → Word
  | .d, a => a
  | .sub, a => alignToDword a

/-- A premise over the entry registers: the store with base `b` (not a frame address) does
    not rewrite the doubleword of slot `sk`. -/
structure Req where
  pc : Word
  w : Width
  base : AVal
  sk : Word
  deriving DecidableEq, Repr

def Req.Holds (E : Reg → Word) (q : Req) : Prop :=
  match q.base with
  | .lin r k => q.w.target (E r + k) ≠ E .x2 + q.sk
  | .const c => q.w.target c ≠ E .x2 + q.sk
  | .top => True   -- never generated; a `top` base is a residual

/-! ## The transfer function on straight-line instructions -/

/-- The result of one straight-line instruction: the next state and what it owes. -/
structure Out where
  st : AState
  reqs : List Req := []
  residual : List Word := []

/-- The register a non-memory, non-control instruction writes, with its abstract value. -/
def aluResult (pc : Word) (A : AState) : Instr → Option (Reg × AVal)
  | .ADDI rd rs imm => some (rd, (A.get rs).addK (signExtend12 imm))
  | .ADD rd rs1 rs2 =>
      some (rd, match A.get rs1, A.get rs2 with
        | v, .const c => v.addK c
        | .const c, v => v.addK c
        | _, _ => .top)
  | .MV rd rs => some (rd, A.get rs)
  | .LI rd imm => some (rd, .const imm)
  | .LUI rd imm => some (rd, .const ((imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64))
  | .AUIPC rd imm => some (rd, .const (pc + (imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64))
  | .SUB rd _ _ | .SLL rd _ _ | .SRL rd _ _ | .SRA rd _ _ | .AND rd _ _ | .OR rd _ _
  | .XOR rd _ _ | .SLT rd _ _ | .SLTU rd _ _ => some (rd, .top)
  | .ANDI rd _ _ | .ORI rd _ _ | .XORI rd _ _ | .SLTI rd _ _ | .SLTIU rd _ _ => some (rd, .top)
  | .SLLI rd _ _ | .SRLI rd _ _ | .SRAI rd _ _ => some (rd, .top)
  | .ADDIW rd _ _ | .SUBW rd _ _ | .SRLW rd _ _ | .SLLIW rd _ _ | .SRLIW rd _ _ => some (rd, .top)
  | .MUL rd _ _ | .MULH rd _ _ | .MULHSU rd _ _ | .MULHU rd _ _ => some (rd, .top)
  | .DIV rd _ _ | .DIVU rd _ _ | .REM rd _ _ | .REMU rd _ _ => some (rd, .top)
  | _ => none

/-- A load: destination, base, offset, and whether it is a doubleword load. -/
def loadOf : Instr → Option (Reg × Reg × BitVec 12 × Bool)
  | .LD rd rs off => some (rd, rs, off, true)
  | .LW rd rs off | .LWU rd rs off | .LB rd rs off | .LH rd rs off
  | .LBU rd rs off | .LHU rd rs off => some (rd, rs, off, false)
  | _ => none

/-- A store: base, source, offset, width. -/
def storeOf : Instr → Option (Reg × Reg × BitVec 12 × Width)
  | .SD rs1 rs2 off => some (rs1, rs2, off, .d)
  | .SW rs1 rs2 off | .SH rs1 rs2 off | .SB rs1 rs2 off => some (rs1, rs2, off, .sub)
  | _ => none

/-- Whether a frame store at offset `k` of width `w` may rewrite slot `sk`. -/
def mayHit (w : Width) (k sk : Word) : Bool :=
  match w with
  | .d => k == sk
  | .sub => (k - sk).toNat < 8

def transferStore (pc : Word) (A : AState) (rs1 rs2 : Reg) (off : BitVec 12) (w : Width) : Out :=
  let b := (A.get rs1).addK (signExtend12 off)
  match b.frameOff? with
  | some k =>
      let kept := A.slots.filter (fun p => !mayHit w k p.1)
      let new := match w, A.get rs2 with
        | .d, .top => kept
        | .d, v => (k, v) :: kept
        | .sub, _ => kept
      { st := { A with slots := new } }
  | none =>
      let kept := A.slots.filter protects
      if b = .top then
        { st := { A with slots := kept }, residual := if kept.isEmpty then [] else [pc] }
      else
        { st := { A with slots := kept },
          reqs := kept.map (fun p => { pc, w, base := b, sk := p.1 }) }

/-- One straight-line instruction, or `none` if it is not one this analysis models. -/
def transfer (pc : Word) (A : AState) (i : Instr) : Option Out :=
  match aluResult pc A i with
  | some (rd, v) => some { st := A.set rd v }
  | none =>
  match loadOf i with
  | some (rd, rs, off, isD) =>
      let v := match ((A.get rs).addK (signExtend12 off)).frameOff?, isD with
        | some k, true => (A.slots.lookup k).getD .top
        | _, _ => .top
      some { st := A.set rd v }
  | none =>
  match storeOf i with
  | some (rs1, rs2, off, w) => some (transferStore pc A rs1 rs2 off w)
  | none =>
  match i with
  | .NOP | .FENCE => some { st := A }
  | _ => none

/-! ## Control flow -/

/-- A function: its base, its decoded words, and the outlined fragments it may call. -/
structure Fn where
  base : Word
  prog : List (Option Instr)
  frags : List (Word × List (Option Instr)) := []
  /-- Where an indirect jump (`jalr zero` through an unknown register) may land inside the
      function. `none`: anywhere, and no premise. `some ts`: only at `ts` -- the frame
      theorem then takes the control-flow premise that it does (`CfiOk`). Jump tables give
      `ts` from relocations; a vtable tail call gives `some []` ("it leaves"). -/
  jumps : Option (List Word) := none

def Fn.pcOf (f : Fn) (i : Nat) : Word := f.base + BitVec.ofNat 64 (4 * i)

/-- The index of `pc` in the function, if it is one of its instruction addresses. -/
def Fn.idx? (f : Fn) (pc : Word) : Option Nat :=
  let d := (pc - f.base).toNat
  if d % 4 = 0 ∧ d / 4 < f.prog.length then some (d / 4) else none

def Fn.instrAt? (f : Fn) (i : Nat) : Option Instr := (f.prog[i]?).join

/-- What one instruction does to control, from the analysis's point of view. -/
inductive Edge where
  /-- Continue at instruction index `j` with this state. -/
  | goto (j : Nat) (A : AState)
  /-- Leave the function here: integrity is required of this state. -/
  | exit (A : AState)
  /-- An unknown target: possibly any instruction of the function, possibly an exit. -/
  | anywhere (A : AState)

/-- The result of analysing one instruction. -/
structure Step where
  edges : List Edge
  reqs : List Req := []
  residual : List Word := []
  noreturn : List Word := []

def Fn.target (f : Fn) (A : AState) (pc : Word) : List Edge :=
  match f.idx? pc with
  | some j => [.goto j A]
  | none => [.exit A]

/-- Abstractly run an outlined fragment from instruction `n` to its `jalr zero, 0(t0)`.
    Fragments here are prologue/epilogue code: straight-line, and owing nothing (a store
    that would need a premise makes the fragment unsupported). -/
def runFrag (A : AState) (fbase : Word) : List (Option Instr) → Nat → Option AState
  | [], _ => none
  | some i :: rest, n =>
      if i = .JALR .x0 .x5 0 then some A else
      match transfer (fbase + BitVec.ofNat 64 (4 * n)) A i with
      | none => none
      | some o => if o.reqs.isEmpty && o.residual.isEmpty then runFrag o.st fbase rest (n + 1) else none
  | none :: _, _ => none

/-- Conditional branches: the offset. -/
def branchOff? : Instr → Option (BitVec 13)
  | .BEQ _ _ off | .BNE _ _ off | .BLT _ _ off | .BGE _ _ off | .BLTU _ _ off | .BGEU _ _ off =>
      some off
  | _ => none

/-- A call under the contract: continue after it with the contract's state, or, if the
    return address is outside the function, record it as assumed not to return. -/
def Fn.callStep (f : Fn) (pc : Word) (A : AState) : Step :=
  match f.idx? (pc + 4) with
  | some j => { edges := [.goto j A.afterCall] }
  | none => { edges := [], noreturn := [pc] }

/-- An outliner call `jalr t0, off(t0)` to a fragment we hold. -/
def Fn.outlinedStep (f : Fn) (pc : Word) (A : AState) (off : BitVec 12) : Option Step :=
  match A.get .x5 with
  | .const c =>
      let tgt := (c + signExtend12 off) &&& ~~~1#64
      match f.frags.lookup tgt, f.idx? (pc + 4) with
      | some fp, some j =>
          match runFrag (A.set .x5 (.const (pc + 4))) tgt fp 0 with
          | some B =>
              -- The fragment returns through `t0`, so `t0` must still be the return address,
              -- and `jalr` clearing bit 0 must not move it.
              if B.get .x5 = .const (pc + 4) ∧ (pc + 4) &&& ~~~1#64 = pc + 4 then
                some { edges := [.goto j B] }
              else none
          | none => none
      | _, _ => none
  | _ => none

/-- One instruction at `pc`. A word that does not decode (`none`) has no successor: the
    image gives it no code, so `stepSp1` traps there. -/
def Fn.stepAt (f : Fn) (pc : Word) (oi : Option Instr) (A : AState) : Option Step :=
  match oi with
  | none => some { edges := [] }
  | some ins =>
  match branchOff? ins with
  | some off => some { edges := f.target A (pc + 4) ++ f.target A (pc + signExtend13 off) }
  | none =>
  match ins with
  | .JAL rd off =>
      if rd = .x0 then some { edges := f.target A (pc + signExtend21 off) }
      else if rd = .x1 then some (f.callStep pc A)
      else none
  | .JALR rd rs off =>
      if rd = .x0 then
        if rs = .x1 ∧ off = 0 then some { edges := [.exit A] }
        else match A.get rs with
          | .const c => some { edges := f.target A ((c + signExtend12 off) &&& ~~~1#64) }
          | _ => some { edges := [.anywhere A] }
      else if rd = .x1 then some (f.callStep pc A)
      else if rd = .x5 ∧ rs = .x5 then f.outlinedStep pc A off
      else none
  | ins =>
      match transfer pc A ins with
      | none => none
      | some o => some { edges := f.target o.st (pc + 4), reqs := o.reqs, residual := o.residual }

/-- Instruction `i` of the function. -/
def Fn.step (f : Fn) (i : Nat) (A : AState) : Option Step :=
  match f.prog[i]? with
  | none => none
  | some oi => f.stepAt (f.pcOf i) oi A

/-! ## The fixpoint -/

def okExit (A : AState) : Bool := A.get .x1 == .lin .x1 0 && A.get .x2 == .lin .x2 0

def joinAt (anno : Array (Option AState)) (j : Nat) (A : AState) : Array (Option AState) × Bool :=
  match anno[j]? with
  | some none => (anno.set! j (some A), true)
  | some (some B) =>
      let C := B.join A
      if C.beq B then (anno, false) else (anno.set! j (some C), true)
  | none => (anno, false)

/-- The instructions an indirect jump may land on, as `Fn.jumps` says. -/
def Fn.jumpTargets (f : Fn) : List Nat :=
  match f.jumps with
  | none => List.range f.prog.length
  | some ts => ts.filterMap f.idx?

/-- Kildall's worklist over instruction indices. Unreachable instructions stay `none`. -/
def Fn.analyze (f : Fn) (fuel : Nat := 64 * f.prog.length + 64) : Option (Array (Option AState)) :=
  go fuel (((List.replicate f.prog.length none).toArray).set! 0 (some AState.entry)) [0]
where
  go : Nat → Array (Option AState) → List Nat → Option (Array (Option AState))
    | 0, _, _ => none
    | _, anno, [] => some anno
    | fuel + 1, anno, i :: work =>
      match anno[i]? with
      | some (some A) =>
        match f.step i A with
        | none => none
        | some st =>
          let (anno, work) := st.edges.foldl (fun (acc : Array (Option AState) × List Nat) e =>
            match e with
            | .goto j B =>
                let (a, ch) := joinAt acc.1 j B
                (a, if ch then j :: acc.2 else acc.2)
            | .exit _ => acc
            | .anywhere B =>
                f.jumpTargets.foldl (fun acc j =>
                  let (a, ch) := joinAt acc.1 j B
                  (a, if ch then j :: acc.2 else acc.2)) acc) (anno, work)
          go fuel anno work
      | _ => go fuel anno work

/-! ## The check

`Fn.valid` is the Boolean the soundness theorem consumes. It is pure (`List.all` over
instruction indices) so that facts about it are proved by unfolding, not by reasoning
about a loop. `Fn.check` wraps it with a report for humans. -/

def Fn.annoAt (anno : Array (Option AState)) (i : Nat) : Option AState := (anno[i]?).join

def Fn.edgeOk (f : Fn) (anno : Array (Option AState)) : Edge → Bool
  | .goto j B => match Fn.annoAt anno j with
      | some C => B.le C
      | none => false
  | .exit B => okExit B
  | .anywhere B => okExit B &&
      match f.jumps with
      | none => (List.range f.prog.length).all fun j => match Fn.annoAt anno j with
          | some C => B.le C
          | none => false
      | some ts => ts.all fun t => match f.idx? t with
          | some j => (match Fn.annoAt anno j with
              | some C => B.le C
              | none => false)
          | none => true

def Fn.instrOk (f : Fn) (anno : Array (Option AState)) (i : Nat) : Bool :=
  match Fn.annoAt anno i with
  | none => true
  | some A => match f.step i A with
    | none => false
    | some st => st.edges.all (f.edgeOk anno)

def Fn.valid (f : Fn) (anno : Array (Option AState)) : Bool :=
  (match Fn.annoAt anno 0 with
    | some A => AState.entry.le A
    | none => false) &&
  (List.range f.prog.length).all (f.instrOk anno)

/-! ### The same check, in one pass

`Fn.valid` indexes the program and the annotation by position, which the kernel does in
time linear in the index: quadratic overall, and most of the cost of checking a function.
`Fn.validFast` walks both lists together; only jump edges index. `validFast_sound`
(`Frame.Sound`) shows it implies `Fn.valid`. -/

/-- `Fn.edgeOk` at instruction `i`, given the annotation of `i + 1` (`next`), so that the
    common fall-through edge needs no lookup; "anywhere" is one pass over the list. -/
def Fn.edgeOkAt (f : Fn) (anno : Array (Option AState)) (i : Nat)
    (next : Option (Option AState)) : Edge → Bool
  | .goto j B =>
      if j = i + 1 then
        match next with
        | some (some C) => B.le C
        | _ => false
      else f.edgeOk anno (.goto j B)
  | .exit B => okExit B
  | .anywhere B => okExit B &&
      match f.jumps with
      | none => anno.toList.all fun
          | some C => B.le C
          | none => false
      | some _ => f.edgeOk anno (.anywhere B)

def Fn.walk (f : Fn) (anno : Array (Option AState)) :
    Nat → List (Option Instr) → List (Option AState) → Bool
  | i, oi :: ps, a :: as =>
      (match a with
        | none => true
        | some A => match f.stepAt (f.pcOf i) oi A with
          | none => false
          | some st => st.edges.all (f.edgeOkAt anno i as.head?)) &&
      f.walk anno (i + 1) ps as
  | _, _, _ => true

def Fn.validFast (f : Fn) (anno : Array (Option AState)) : Bool :=
  (match Fn.annoAt anno 0 with
    | some A => AState.entry.le A
    | none => false) &&
  anno.size == f.prog.length && f.walk anno 0 f.prog anno.toList

/-- Everything the reachable instructions owe, collected in one walk. -/
def Fn.collectFrom (f : Fn) (g : Step → List α) :
    Nat → List (Option Instr) → List (Option AState) → List α
  | i, oi :: ps, a :: as =>
      (match a with
        | none => []
        | some A => match f.stepAt (f.pcOf i) oi A with
          | none => []
          | some st => g st) ++ f.collectFrom g (i + 1) ps as
  | _, _, _ => []

def Fn.collect (f : Fn) (anno : Array (Option AState)) (g : Step → List α) : List α :=
  f.collectFrom g 0 f.prog anno.toList

structure Report where
  ok : Bool
  reqs : List Req
  residual : List Word
  noreturn : List Word
  deriving Repr

def Fn.report (f : Fn) (anno : Array (Option AState)) : Report :=
  { ok := f.valid anno, reqs := f.collect anno (·.reqs), residual := f.collect anno (·.residual),
    noreturn := f.collect anno (·.noreturn) }

def Fn.check (f : Fn) : Report :=
  match f.analyze with
  | some anno => f.report anno
  | none => { ok := false, reqs := [], residual := [], noreturn := [] }

end AsmVerif.RiscV.Frame
