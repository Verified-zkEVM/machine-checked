/-
  Tools.Test.Run

  Runs the lift of one instruction on concrete registers and memory, for the tests of
  `Tools/Test/`. The instruction is lifted where its own address has label `here`, the next
  instruction's `next`, and every other address `taken`; the run follows the lift's own
  `Lgoto`, `Lcond` and `Ligoto` and stops where it leaves the instruction: at `next`, at
  `taken`, at the lift's `abort` label, or at an instruction that is not local (a call, a tail
  call, a return, an external call, `Labort`).

  The memory is a map from addresses to bytes, little-endian, with every address readable and
  writable (a byte never written reads as 0). Nothing here is trusted: it is a test harness.

  ## Main definitions

  * `cx`, `body`, `run`, `End`
-/

import Lprog.Linked
import Lprog.Op
import Lprog.Sem
import Std.Data.HashMap

namespace Tools.Test

open Lprog

/-- Memory: bytes by address. -/
abbrev Mem := Std.HashMap (BitVec 64) (BitVec 8)

def Mem.byte (m : Mem) (a : BitVec 64) : BitVec 8 := m.getD a 0

/-- `w` bytes at `a`, little-endian, zero-extended. -/
def Mem.read (m : Mem) (w : Width) (a : BitVec 64) : BitVec 64 :=
  (List.range w.bytes).foldr (fun k acc => (acc <<< 8) ||| (m.byte (a + BitVec.ofNat 64 k)).zeroExtend 64) 0

/-- The low `w` bytes of `v` at `a`, little-endian. -/
def Mem.write (m : Mem) (w : Width) (a v : BitVec 64) : Mem :=
  (List.range w.bytes).foldl (fun m k => m.insert (a + BitVec.ofNat 64 k) ((v >>> (8 * k)).truncate 8)) m

def mem : Lprog.Mem Mem where
  load w a m := some (m.read w a)
  store w a v m := some (m.write w a v)

/-- The labels of the run: the instruction, the next one, any other address, and giving up. -/
def here : LLabel := 0
def next : LLabel := 1
def taken : LLabel := 2
def abort : LLabel := 3

/-- What a lift may ask of the program, for an instruction at `addr` of `size` bytes: its own
    address is `here`, the next `next`, any other `taken`. `entries` are addresses that are
    functions (function `k` is the `k`th); a computed jump may go to any of `cands`. -/
def cx (addr : BitVec 64) (size : Nat) (entries : List (BitVec 64) := [])
    (cands : List (BitVec 64) := []) : Linked.Cx where
  label a := some (if a == addr then here else if a == addr + BitVec.ofNat 64 size then next else taken)
  entry a := entries.idxOf? a
  cands := cands.map fun a => (a, if a == addr + BitVec.ofNat 64 size then next else taken)
  all := List.range entries.length
  abort := abort

/-- The lift of one instruction with the labels it may go to after it. -/
def body {Reg : Type} (code : Lcmd (Op Reg) Reg) : Lcmd (Op Reg) Reg :=
  [.Llabel .internal here] ++ code ++
    [.Llabel .internal next, .Labort, .Llabel .internal taken, .Labort, .Llabel .internal abort, .Labort]

/-- How a run of one instruction ends. -/
inductive End (Reg : Type) where
  /-- At the next instruction, or at another (a branch taken). -/
  | next (regs : Reg → BitVec 64) (m : Mem)
  | taken (regs : Reg → BitVec 64) (m : Mem)
  /-- The lift gives up, as the instruction runs (`abort`) or outright (`Labort`). -/
  | abort
  /-- The Lprog program goes `wrong` (a jump nowhere, a condition it cannot state). -/
  | wrong (why : String)
  /-- An instruction that leaves the function: a call, tail call, return or external call. -/
  | leaves (i : LinstrR (Op Reg) Reg) (regs : Reg → BitVec 64) (m : Mem)
  /-- The fuel ran out. -/
  | stuck

/-- Run `code` from instruction `pc`. -/
def go {Reg : Type} [DecidableEq Reg] (code : Lcmd (Op Reg) Reg) :
    Nat → Nat → (Reg → BitVec 64) → Mem → End Reg
  | 0, _, _, _ => .stuck
  | fuel + 1, pc, regs, m =>
    let jump (l : LLabel) : End Reg :=
      if l == next then .next regs m
      else if l == taken then .taken regs m
      else if l == abort then .abort
      else match labelIdx code l with
        | some j => go code fuel j regs m
        | none => .wrong s!"no label {l}"
    match code[pc]? with
    | none => .wrong "ran off the end"
    | some i => match i with
      | .Lopn op => match op.eval mem regs m with
        | some (r', m') => go code fuel (pc + 1) r' m'
        | none => .wrong "a fault"
      | .Llabel _ l =>
        if l == next then .next regs m
        else if l == taken then .taken regs m
        else if l == abort then .abort
        else go code fuel (pc + 1) regs m
      | .Lgoto l => jump l
      | .Lcond c l => match condEval c regs with
        | some true => jump l
        | some false => go code fuel (pc + 1) regs m
        | none => .wrong "a condition with no meaning"
      | .Ligoto e cs => match cs.find? (·.1 == e.eval regs) with
        | some (_, l) => jump l
        | none => .wrong "a computed jump to none of its candidates"
      | .Labort => .abort
      | i => .leaves i regs m

/-- Registers: `init` where it says, 0 elsewhere. -/
def regsOf {Reg : Type} [DecidableEq Reg] (init : List (Reg × BitVec 64)) : Reg → BitVec 64 :=
  fun r => ((init.find? (·.1 == r)).map (·.2)).getD 0

/-- **Run the lift `code` of one instruction** from the registers `init` and memory `m`. -/
def run {Reg : Type} [DecidableEq Reg] (code : Lcmd (Op Reg) Reg) (init : List (Reg × BitVec 64))
    (m : Mem := {}) (fuel : Nat := 100000) : End Reg :=
  go (body code) fuel 1 (regsOf init) m

/-- Do the registers after a run at the next instruction have the values `want`? -/
def End.has {Reg : Type} (e : End Reg) (want : List (Reg × BitVec 64)) : Bool :=
  match e with
  | .next regs _ => want.all fun (r, v) => regs r == v
  | _ => false

/-- The same, for a run that ends at another instruction (a branch taken). -/
def End.hasTaken {Reg : Type} (e : End Reg) (want : List (Reg × BitVec 64)) : Bool :=
  match e with
  | .taken regs _ => want.all fun (r, v) => regs r == v
  | _ => false

/-- The memory after a run at the next instruction, if it got there. -/
def End.mem? {Reg : Type} : End Reg → Option Mem
  | .next _ m | .taken _ m | .leaves _ _ m => some m
  | _ => none

def End.isAbort {Reg : Type} : End Reg → Bool | .abort => true | _ => false
def End.isNext {Reg : Type} : End Reg → Bool | .next .. => true | _ => false
def End.isTaken {Reg : Type} : End Reg → Bool | .taken .. => true | _ => false

/-- Memory with `bytes` from `a`. -/
def memAt (a : BitVec 64) (bytes : List Nat) : Mem :=
  bytes.zipIdx.foldl (fun m (b, k) => m.insert (a + BitVec.ofNat 64 k) (BitVec.ofNat 8 b)) {}

end Tools.Test
