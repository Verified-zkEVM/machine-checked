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

import AsmVerif.RiscV.Frame.Domain

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
  | _, _, _, _ => false

/-- What every function of a program shares: the top of the stack (everything the image
    places lies above it), the protected regions (byte ranges no function may write, whose
    contents are fixed), and those contents. -/
structure Env where
  stackTop : Nat
  prot : List (Word × Nat)
  init : Word → Word

/-- An aligned doubleword key inside a protected region. -/
def Env.protKey (env : Env) (a : Word) : Bool :=
  decide (a.toNat % 8 = 0) &&
  env.prot.any fun (b, l) => decide (b.toNat ≤ a.toNat) && decide (a.toNat + 8 ≤ b.toNat + l)

structure Iface where
  entry : Word
  depth : Nat
  foot : List Item := []
  nz : List AVal := []
  returns : Bool := true
  /-- Registers whose entry value is one of the listed constants: a function pointer or a
      vtable among candidates (the control-flow premise of an indirect call). -/
  vals : List (Reg × List Word) := []
  deriving DecidableEq, Repr

/-- The abstract state at entry: every register its own entry value, except those `vals`
    restricts to a set of constants. -/
def Iface.entryState (σ : Iface) : AState :=
  { regs := allRegs.map fun r => match σ.vals.lookup r with
      | some cs => .oneOf cs
      | none => .lin r 0
    slots := [] }

/-- A value that can be a store's base or a footprint item's: entry-relative or constant. -/
def _root_.AsmVerif.RiscV.Frame.AVal.isPtr : AVal → Bool
  | .lin _ _ | .const _ => true
  | _ => false

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
def loadVal (env : Env) (A : AState) (b : AVal) (isD : Bool) : AVal :=
  if isD then
    match b.frameOff? with
    | some k => (A.slots.lookup k).getD .top
    | none => match b with
      | .const c => if env.protKey c then .const (env.init c) else .top
      | .oneOf cs => if cs.all env.protKey then .oneOf (cs.map env.init) else .top
      | _ => .top
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

def plainStep (env : Env) (σ : Iface) (pc : Word) (A : AState) (i : Instr) : Option AState :=
  match aluResult pc A i with
  | some (rd, v) => some (A.set rd v)
  | none =>
  match loadOf i with
  | some (rd, rs, off, isD) => some (A.set rd (loadVal env A ((A.get rs).addK (signExtend12 off)) isD))
  | none =>
  match storeOf i with
  | some (rs1, rs2, off, w) => storeStep σ A rs1 rs2 off w
  | none =>
  match i with
  | .NOP | .FENCE => some A
  | _ => none

/-! ## Calls -/

def instVal (A : AState) : AVal → AVal
  | .lin r k => (A.get r).addK k
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

def instItem (A : AState) (it : Item) : Option Item :=
  (instLen A it.len).map fun l => { base := instVal A it.base, len := l }

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

def nzOk (σ : Iface) (A : AState) (v : AVal) : Bool := v.isPtr && nzVal σ (instVal A v)

/-- The callee-saved registers: `sp`, `gp`, `tp`, `s0`-`s11`. -/
def savedRegs : List Reg :=
  [.x2, .x3, .x4, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The state after a call returns: callee-saved registers kept, the slots it cannot
    write. -/
def afterCall (A : AState) (m : Nat) (its : List Item) : AState :=
  { regs := allRegs.map (fun r => if savedRegs.contains r then A.get r else .top),
    slots := A.slots.filter fun p => decide (negOff p.1 ≤ m) && its.all (slotClear p.1) }

/-- A callee's `vals` premise, discharged by the caller's value: a constant or a set inside
    the candidates. -/
def valOk (A : AState) (p : Reg × List Word) : Bool :=
  match A.get p.1 with
  | .const c => p.2.contains c
  | .oneOf cs => cs.all p.2.contains
  | _ => false

/-- The stack pointer is `m` bytes below its entry value, `m` a multiple of 8. -/
def spOff (A : AState) : Option Nat :=
  match (A.get .x2).frameOff? with
  | some k => if negOff k % 8 = 0 then some (negOff k) else none
  | none => none

/-- A call to `g` from a state `A`: the callee's precondition, instantiated. Returns the
    items it may write, in the caller's terms. -/
def callOk (σ : Iface) (A : AState) (g : Iface) : Option (Nat × List Item) :=
  match spOff A with
  | none => none
  | some m =>
    if m + g.depth ≤ σ.depth then
      match g.foot.mapM (instItem A) with
      | none => none
      | some its =>
        if its.all (itemOk σ m) && g.nz.all (nzOk σ A) && g.vals.all (valOk A) then some (m, its)
        else none
    else none

def okExit (A : AState) : Bool :=
  A.get .x1 == .lin .x1 0 && savedRegs.all fun r => A.get r == .lin r 0

/-- A tail call: `f` leaves for `g` with every callee-saved register and `ra` restored, and
    `g`'s footprint covered by `f`'s. -/
def tailOk (σ : Iface) (A : AState) (g : Iface) : Bool :=
  okExit A && decide (g.depth ≤ σ.depth) && (σ.returns || !g.returns) &&
  match g.foot.mapM (instItem A) with
  | none => false
  | some its => its.all (fun it => it.base.frameOff?.isNone && it.base.isPtr &&
      σ.foot.any (·.within it)) && g.nz.all (nzOk σ A) && g.vals.all (valOk A)

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

/-- A jump to `pc`: inside the function, or a tail call. -/
def Ctx.jump (c : Ctx) (A : AState) (pc : Word) : Option (List Edge) :=
  match c.f.idx? pc with
  | some j => some [.goto j A]
  | none => match c.lookup pc with
    | some g => if tailOk c.σ A g then some [] else none
    | none => none

/-- A call to `tgt` returning to `pc + 4`. The callee is entered with `ra = pc + 4`, so its
    interface is instantiated in `A` with that link. -/
def Ctx.call (c : Ctx) (pc : Word) (A : AState) (tgt : Word) : Option (List Edge) :=
  match c.lookup tgt with
  | none => none
  | some g => match callOk c.σ (A.set .x1 (.const (pc + 4))) g with
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

/-- Abstractly run an outlined fragment (straight-line prologue or epilogue code) to its
    `jalr zero, 0(t0)`. -/
def Ctx.runFrag (c : Ctx) (A : AState) (fbase : Word) : List (Option Instr) → Nat → Option AState
  | [], _ => none
  | some i :: rest, n =>
      if i = .JALR .x0 .x5 0 then some A else
      match plainStep c.env c.σ (fbase + BitVec.ofNat 64 (4 * n)) A i with
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
        else match A.get rs with
          | .const t => c.jump A ((t + signExtend12 off) &&& ~~~1#64)
          | .oneOf ts => allEdges (fun t => c.jump A ((t + signExtend12 off) &&& ~~~1#64)) ts
          | _ => none
      else if rd = .x1 then
        match A.get rs with
        | .const t => c.call pc A ((t + signExtend12 off) &&& ~~~1#64)
        | .oneOf ts => allEdges (fun t => c.call pc A ((t + signExtend12 off) &&& ~~~1#64)) ts
        | _ => none
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
  | ins => (plainStep c.env c.σ pc A ins).bind fun B => c.jump B (pc + 4)

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
  c.f.base == c.σ.entry &&
  (match Fn.annoAt anno 0 with
    | some A => c.σ.entryState.le A
    | none => false) &&
  anno.size == c.f.prog.length && c.walk anno 0 c.f.prog anno.toList

end AsmVerif.RiscV.Check
