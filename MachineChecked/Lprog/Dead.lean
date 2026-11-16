/-
  MachineChecked.Lprog.Dead

  Dropping the writes nothing reads, for the registers an instruction set says to look at.

  An instruction set with condition flags lifts each instruction that sets them to a write
  of each flag, and most of those writes are never read: the next such instruction writes
  the flags again. `dropDead regs` removes, from a function's body, each `set` of a register
  of `regs` whose value no later instruction of the function can read.

  It is the usual backward analysis over the instructions of one function, and it assumes
  nothing of what is outside it:

  * a call, a tail call, a return and an external call read every register;
  * only a `set` is dropped: it reads registers and writes one, and does nothing else. A
    load into a register nothing reads stays, since the load may fail;
  * a register outside `regs` is not looked at.

  A `set` that is dropped reads nothing either, so a write that only feeds a dropped write
  is dropped with it.

  Nothing is proved of it yet.

  ## Main definitions

  * `dropDead`
-/

import MachineChecked.Lprog.Op
import Std.Data.HashMap

namespace MachineChecked.Lprog

variable {Reg : Type} [DecidableEq Reg]

namespace Dead

/-- The registers of `regs` an expression reads, as a set of their positions. -/
def Expr.reads (regs : List Reg) : Expr Reg → Nat
  | .reg r => match regs.idxOf? r with
    | some k => 1 <<< k
    | none => 0
  | .imm _ => 0
  | .un _ e => reads regs e
  | .bin _ a b => reads regs a ||| reads regs b

/-- Likewise for an operand. -/
def operandReads (regs : List Reg) : LOperand Reg → Nat
  | .reg r => Expr.reads regs (.reg r)
  | .imm _ => 0
  | .cmp _ a b => operandReads regs a ||| operandReads regs b

/-- A set without position `k`. -/
def without (s k : Nat) : Nat := if s &&& (1 <<< k) = 0 then s else s ^^^ (1 <<< k)

/-- What is read before an instruction, given what is read after it. -/
def before (regs : List Reg) (after : Nat) : LinstrR (Op Reg) Reg → Nat
  | .Lopn (.set d e) => match regs.idxOf? d with
    | some k => if after &&& (1 <<< k) = 0 then after else without after k ||| Expr.reads regs e
    | none => after ||| Expr.reads regs e
  | .Lopn (.load d _ _ a) => (match regs.idxOf? d with
    | some k => without after k
    | none => after) ||| Expr.reads regs a
  | .Lopn (.store _ a e) => after ||| Expr.reads regs a ||| Expr.reads regs e
  | .Lopn .skip | .Llabel .. | .Lgoto _ => after
  | .Lcond c _ => after ||| operandReads regs c
  | .Ligoto e _ => after ||| Expr.reads regs e
  | .Lcall .. | .Ltail _ | .Lret | .Lext _ => 2 ^ regs.length - 1
  | .Labort => 0

end Dead

open Dead in
/-- **A body without the writes of `regs` that nothing reads.** -/
def dropDead (regs : List Reg) (body : Lcmd (Op Reg) Reg) : Lcmd (Op Reg) Reg := Id.run do
  let code := body.toArray
  let n := code.size
  let mut at_ : Std.HashMap LLabel Nat := {}
  for h : i in [0 : n] do
    if let .Llabel _ l := code[i] then at_ := at_.insert l i
  -- what is read from each instruction on; `live[n]` is the end of the body
  let mut live : Array Nat := Array.replicate (n + 1) 0
  let to (live : Array Nat) (l : LLabel) : Nat := (at_[l]?.map (live[·]!)).getD 0
  -- what is read after instruction `i`: at each place it may go on to
  let after (live : Array Nat) (i : Nat) : Nat := match code[i]? with
    | some (.Lgoto l) => to live l
    | some (.Lcond _ l) => live[i + 1]! ||| to live l
    | some (.Ligoto _ cands) => cands.foldl (fun s (_, l) => s ||| to live l) 0
    | some (.Ltail _) | some .Lret | some .Labort => 0
    | _ => live[i + 1]!
  let mut changed := true
  -- each round only adds to the sets, of which there are finitely many
  for _ in [0 : (n + 1) * (regs.length + 1)] do
    if !changed then break
    changed := false
    for k in [0 : n] do
      let i := n - 1 - k
      let some c := code[i]? | continue
      let s := before regs (after live i) c
      if s != live[i]! then
        live := live.set! i s
        changed := true
  let mut out : Array (LinstrR (Op Reg) Reg) := #[]
  for h : i in [0 : n] do
    let dead := match code[i] with
      | .Lopn (.set d _) => (regs.idxOf? d).any fun k => after live i &&& (1 <<< k) = 0
      | _ => false
    if !dead then out := out.push code[i]
  return out.toList

end MachineChecked.Lprog
