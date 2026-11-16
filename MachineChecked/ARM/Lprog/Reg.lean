/-
  MachineChecked.ARM.Lprog.Reg

  The registers of AArch64 as an instruction set of the low logical program.

  They are the general registers `x0` to `x30` and the stack pointer; the four condition
  flags, each a register that holds 0 or 1, so that what an instruction does to the flags is
  an operation like any other; and three registers of the lift's own (`t0`, `t1`, `t2`), for
  a value an instruction computes once and uses twice. The zero register is no register: it
  reads as the immediate zero and a write to it is dropped (`Lift.lean`).

  ## Main definitions

  * `Reg`, `Reg.ofGpr`, `allRegs`
-/

import MachineChecked.Lprog.Text

namespace MachineChecked.ARM.Lprog

open MachineChecked.Lprog

/-- A register of AArch64 at Lprog. -/
inductive Reg where
  | x0
  | x1
  | x2
  | x3
  | x4
  | x5
  | x6
  | x7
  | x8
  | x9
  | x10
  | x11
  | x12
  | x13
  | x14
  | x15
  | x16
  | x17
  | x18
  | x19
  | x20
  | x21
  | x22
  | x23
  | x24
  | x25
  | x26
  | x27
  | x28
  | x29
  | x30
  | sp
  | nf
  | zf
  | cf
  | vf
  | t0
  | t1
  | t2
  deriving DecidableEq, Repr, Inhabited

namespace Reg

/-- The general register with a number below 31. -/
def ofGpr (i : BitVec 5) : Reg :=
  match i.toNat with
  | 0 => .x0
  | 1 => .x1
  | 2 => .x2
  | 3 => .x3
  | 4 => .x4
  | 5 => .x5
  | 6 => .x6
  | 7 => .x7
  | 8 => .x8
  | 9 => .x9
  | 10 => .x10
  | 11 => .x11
  | 12 => .x12
  | 13 => .x13
  | 14 => .x14
  | 15 => .x15
  | 16 => .x16
  | 17 => .x17
  | 18 => .x18
  | 19 => .x19
  | 20 => .x20
  | 21 => .x21
  | 22 => .x22
  | 23 => .x23
  | 24 => .x24
  | 25 => .x25
  | 26 => .x26
  | 27 => .x27
  | 28 => .x28
  | 29 => .x29
  | _ => .x30

/-- A register's name in Lprog text, and as a Pancake variable. -/
def name : Reg → String
  | .x0 => "x0"
  | .x1 => "x1"
  | .x2 => "x2"
  | .x3 => "x3"
  | .x4 => "x4"
  | .x5 => "x5"
  | .x6 => "x6"
  | .x7 => "x7"
  | .x8 => "x8"
  | .x9 => "x9"
  | .x10 => "x10"
  | .x11 => "x11"
  | .x12 => "x12"
  | .x13 => "x13"
  | .x14 => "x14"
  | .x15 => "x15"
  | .x16 => "x16"
  | .x17 => "x17"
  | .x18 => "x18"
  | .x19 => "x19"
  | .x20 => "x20"
  | .x21 => "x21"
  | .x22 => "x22"
  | .x23 => "x23"
  | .x24 => "x24"
  | .x25 => "x25"
  | .x26 => "x26"
  | .x27 => "x27"
  | .x28 => "x28"
  | .x29 => "x29"
  | .x30 => "x30"
  | .sp => "sp"
  | .nf => "nf"
  | .zf => "zf"
  | .cf => "cf"
  | .vf => "vf"
  | .t0 => "t0"
  | .t1 => "t1"
  | .t2 => "t2"

end Reg

/-- Every register. -/
def allRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .sp, .nf, .zf, .cf, .vf, .t0, .t1, .t2]

instance : RegText Reg where
  name := Reg.name
  ofName s := allRegs.find? (·.name == s)
  ofName_name r := by cases r <;> simp [allRegs, Reg.name]

end MachineChecked.ARM.Lprog
