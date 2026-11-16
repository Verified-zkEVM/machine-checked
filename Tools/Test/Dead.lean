/-
  Tools.Test.Dead

  Tests of `dropDead` (`MachineChecked/Lprog/Dead.lean`), run when the module is built: small
  function bodies written by hand, over five registers of which two are flags, and what the
  pass makes of them. A flag write is dropped only when no later instruction of the function
  can read it; calls, tail calls, returns and external calls read everything; only `set`s of
  flags go. Then bodies are run before and after the pass (`Tools.Test.Run.go`) and agree on
  everything but the flags that were dropped.
-/

import MachineChecked.Lprog.Dead
import Tools.Test.Run

namespace Tools.Test.Dead

open MachineChecked.Lprog

/-- The registers of the tests: three that are not flags, two that are. -/
inductive R where
  | a
  | b
  | c
  | zf
  | cf
  deriving DecidableEq, Repr

open R

/-- The flags: what the pass looks at. -/
def flags : List R := [zf, cf]

abbrev I := LinstrR (Op R) R

def set (d : R) (e : Expr R) : I := .Lopn (.set d e)
def setI (d : R) (v : BitVec 64) : I := set d (.imm v)
def setR (d s : R) : I := set d (.reg s)
/-- Jump to `l` when `r` is not zero. -/
def br (r : R) (l : LLabel) : I := .Lcond (.cmp "ne" (.reg r) (.imm 0)) l
/-- Jump to `l` when `a = b`, which reads no flag. -/
def brAB (l : LLabel) : I := .Lcond (.cmp "eq" (.reg a) (.reg b)) l
def lbl (l : LLabel) : I := .Llabel .internal l

/-- What the pass does to a body. -/
def dd (body : List I) : List I := dropDead flags body

/-! ## A flag written and overwritten -/

-- written twice and never read: both go
#guard dd [setI zf 1, setI zf 2, .Labort] == [.Labort]
-- written twice, the second read by a branch: the first goes
#guard dd [setR zf a, setR zf b, br zf 10, lbl 10, .Labort] == [setR zf b, br zf 10, lbl 10, .Labort]
-- overwritten by a load: the set goes, the load stays
#guard dd [setR zf a, .Lopn (.load zf .b8 false (.reg b)), br zf 10, lbl 10, .Labort] ==
  [.Lopn (.load zf .b8 false (.reg b)), br zf 10, lbl 10, .Labort]
-- written and overwritten after a read: both stay
#guard dd [setR zf a, br zf 10, setR zf b, br zf 10, lbl 10, .Labort] ==
  [setR zf a, br zf 10, setR zf b, br zf 10, lbl 10, .Labort]
-- one flag read, the other not: only the unread one goes
#guard dd [setR zf a, setR cf b, br cf 10, lbl 10, .Labort] == [setR cf b, br cf 10, lbl 10, .Labort]

/-! ## Read by an instruction that is not a branch -/

-- a flag read by a write of a register that is not a flag stays
#guard dd [setR zf a, setR b zf, .Labort] == [setR zf a, setR b zf, .Labort]
-- read by a store's value
#guard dd [setR zf a, .Lopn (.store .b8 (.reg b) (.reg zf)), .Labort] ==
  [setR zf a, .Lopn (.store .b8 (.reg b) (.reg zf)), .Labort]
-- read by a load's address
#guard dd [setR zf a, .Lopn (.load c .b8 false (.reg zf)), .Labort] ==
  [setR zf a, .Lopn (.load c .b8 false (.reg zf)), .Labort]
-- read by a computed jump's target
#guard dd [setR zf a, .Ligoto (.reg zf) [], .Labort] == [setR zf a, .Ligoto (.reg zf) [], .Labort]
-- read inside an expression
#guard dd [setR zf a, set c (.un .not (.bin .add (.reg b) (.reg zf))), .Labort] ==
  [setR zf a, set c (.un .not (.bin .add (.reg b) (.reg zf))), .Labort]
-- a flag that only feeds a dropped flag goes with it
#guard dd [setR cf a, setR zf cf, .Labort] == [.Labort]
-- a flag that feeds a flag that is read stays
#guard dd [setR cf a, setR zf cf, br zf 10, lbl 10, .Labort] ==
  [setR cf a, setR zf cf, br zf 10, lbl 10, .Labort]

/-! ## Live across control flow -/

-- read after a `Lgoto`
#guard dd [setR zf a, .Lgoto 10, .Labort, lbl 10, br zf 11, lbl 11, .Labort] ==
  [setR zf a, .Lgoto 10, .Labort, lbl 10, br zf 11, lbl 11, .Labort]
-- read only on the code a `Lgoto` jumps over: goes
#guard dd [setR zf a, .Lgoto 10, br zf 11, lbl 10, .Labort, lbl 11, .Labort] ==
  [.Lgoto 10, br zf 11, lbl 10, .Labort, lbl 11, .Labort]
-- overwritten where a `Lgoto` goes: goes
#guard dd [setR zf a, .Lgoto 10, .Labort, lbl 10, setR zf b, br zf 11, lbl 11, .Labort] ==
  [.Lgoto 10, .Labort, lbl 10, setR zf b, br zf 11, lbl 11, .Labort]
-- read only where a branch goes: stays
#guard dd [setR cf a, brAB 10, .Labort, lbl 10, br cf 11, lbl 11, .Labort] ==
  [setR cf a, brAB 10, .Labort, lbl 10, br cf 11, lbl 11, .Labort]
-- read only where a branch falls through: stays
#guard dd [setR cf a, brAB 10, br cf 11, .Labort, lbl 10, .Labort, lbl 11, .Labort] ==
  [setR cf a, brAB 10, br cf 11, .Labort, lbl 10, .Labort, lbl 11, .Labort]
-- read on neither edge: goes
#guard dd [setR cf a, brAB 10, .Labort, lbl 10, .Labort] == [brAB 10, .Labort, lbl 10, .Labort]
-- a branch to a label not in the body: nothing is read there
#guard dd [setR zf a, brAB 99, .Labort] == [brAB 99, .Labort]
-- read where a computed jump may go: stays
#guard dd [setR zf a, .Ligoto (.reg a) [(5, 10)], .Labort, lbl 10, br zf 11, lbl 11, .Labort] ==
  [setR zf a, .Ligoto (.reg a) [(5, 10)], .Labort, lbl 10, br zf 11, lbl 11, .Labort]
-- read only after a computed jump, where it never goes on: goes
#guard dd [setR zf a, .Ligoto (.reg a) [(5, 10)], br zf 11, lbl 10, .Labort, lbl 11, .Labort] ==
  [.Ligoto (.reg a) [(5, 10)], br zf 11, lbl 10, .Labort, lbl 11, .Labort]

/-! ## Loops -/

/-- A loop whose head reads `cf`, written at the end of the loop, before the back edge. -/
def loop : List I :=
  [lbl 10, br cf 11, set a (.bin .add (.reg a) (.imm 1)), set cf (.bin .ult (.reg b) (.reg a)),
    .Lgoto 10, lbl 11, .Labort]

-- a flag read on the next round, by the back edge: stays
#guard dd loop == loop
-- written in a loop and never read: goes
#guard dd [lbl 10, setI cf 1, brAB 10, .Labort] == [lbl 10, brAB 10, .Labort]
-- read through a back edge reached by a forward jump: needs more than one backward round
#guard dd [.Lgoto 20, lbl 10, br zf 30, .Labort, lbl 20, setR zf a, .Lgoto 10, lbl 30, .Labort] ==
  [.Lgoto 20, lbl 10, br zf 30, .Labort, lbl 20, setR zf a, .Lgoto 10, lbl 30, .Labort]
-- the same, with the flag overwritten before the read: goes
#guard dd [.Lgoto 20, lbl 10, setI zf 0, br zf 30, .Labort, lbl 20, setR zf a, .Lgoto 10, lbl 30,
    .Labort] ==
  [.Lgoto 20, lbl 10, setI zf 0, br zf 30, .Labort, lbl 20, .Lgoto 10, lbl 30, .Labort]

/-! ## Calls, tail calls, returns and external calls read everything -/

-- live at a call
#guard dd [setI zf 1, .Lcall 0 (.direct 0), .Labort] == [setI zf 1, .Lcall 0 (.direct 0), .Labort]
-- live at an indirect call
#guard dd [setI zf 1, .Lcall 0 (.indirect (.reg a) [0]), .Labort] ==
  [setI zf 1, .Lcall 0 (.indirect (.reg a) [0]), .Labort]
-- live at a tail call
#guard dd [setI zf 1, .Ltail (.direct 0)] == [setI zf 1, .Ltail (.direct 0)]
-- live at a return
#guard dd [setI zf 1, setI cf 1, .Lret] == [setI zf 1, setI cf 1, .Lret]
-- live at an external call
#guard dd [setI zf 1, .Lext 0, .Labort] == [setI zf 1, .Lext 0, .Labort]
-- written after a call and never read: goes, and the one before the call stays
#guard dd [setI zf 1, .Lcall 0 (.direct 0), setI zf 2, .Labort] ==
  [setI zf 1, .Lcall 0 (.direct 0), .Labort]
-- overwritten before a return: the first goes
#guard dd [setI zf 1, setI zf 2, .Lret] == [setI zf 2, .Lret]
-- falling off the end of the body reads nothing
#guard dd [setI zf 1] == []

/-! ## What is never dropped -/

-- a register that is not a flag, written twice and never read
#guard dd [setI a 1, setI a 2, .Labort] == [setI a 1, setI a 2, .Labort]
-- a load into a flag nothing reads
#guard dd [.Lopn (.load zf .b8 false (.reg a)), .Labort] == [.Lopn (.load zf .b8 false (.reg a)), .Labort]
-- a store
#guard dd [.Lopn (.store .b1 (.reg a) (.imm 7)), .Labort] == [.Lopn (.store .b1 (.reg a) (.imm 7)), .Labort]
-- `skip`
#guard dd [.Lopn .skip, .Labort] == [.Lopn .skip, .Labort]
-- with no registers to look at, nothing goes
#guard dropDead [] [setI zf 1, setI zf 2, .Labort] == [setI zf 1, setI zf 2, .Labort]
-- a register outside the list is not looked at
#guard dropDead [zf] [setI zf 1, setI cf 1, .Labort] == [setI cf 1, .Labort]

/-! ## Running before and after agrees -/

/-- How a body ends, run from `init` (at `Tools.Test.next`, label 1, it ends with the
    registers). -/
def outcome (body : List I) (init : List (R × BitVec 64)) : End R :=
  go body 10000 0 (regsOf init) {}

/-- The two memories have the same bytes. -/
def sameMem (m m' : Mem) : Bool :=
  m.size == m'.size && m.toList.all fun (k, x) => m'.get? k == some x

/-- The body and its pass end alike from `init`, with the same memory and registers, but the
    flags when they end at the next instruction (after which nothing reads them). -/
def agree (body : List I) (init : List (R × BitVec 64)) : Bool :=
  match outcome body init, outcome (dd body) init with
  | .next r m, .next r' m' => [a, b, c].all (fun x => r x == r' x) && sameMem m m'
  | .leaves i r m, .leaves i' r' m' => i == i' && [a, b, c, zf, cf].all (fun x => r x == r' x) &&
    sameMem m m'
  | .abort, .abort => true
  | _, _ => false

/-- Counts `a` up to `b`, adding to `c` and storing at each round, with flag writes that are
    read and some that are not. -/
def counter (last : I) : List I :=
  [lbl 10,
    set zf (.bin .sub (.reg a) (.reg b)), set cf (.bin .ult (.reg a) (.reg b)),
    .Lcond (.cmp "eq" (.reg zf) (.imm 0)) 20,
    set c (.bin .add (.reg c) (.reg cf)),
    setI zf 7, setI cf 0,
    .Lopn (.store .b8 (.bin .mul (.reg a) (.imm 8)) (.reg c)),
    set a (.bin .add (.reg a) (.imm 1)),
    setR zf a,
    .Lgoto 10,
    lbl 20, setI cf 9, last]

-- the pass drops something here
#guard (dd (counter (lbl next))).length < (counter (lbl next)).length
-- the loop, ending at the next instruction: the same registers but flags, the same memory
#guard agree (counter (lbl next)) [(a, 0), (b, 5)]
#guard (outcome (counter (lbl next)) [(a, 0), (b, 5)]).has [(a, 5), (b, 5), (c, 5)]
-- the loop, ending at a return: the same registers, flags too
#guard agree (counter .Lret) [(a, 2), (b, 9), (c, 100)]
-- the loop that runs no round
#guard agree (counter .Lret) [(a, 9), (b, 9)]
-- straight code, ending at the next instruction
#guard agree [setI zf 1, setR cf a, set b (.bin .add (.reg cf) (.imm 1)), setI cf 3, lbl next, .Labort]
  [(a, 4)]

end Tools.Test.Dead
