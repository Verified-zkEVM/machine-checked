/-
  MachineChecked.X86.Lprog.Reg

  The registers of x86-64 as an instruction set of the low logical program.

  They are the sixteen general registers, in the order of their numbers in an instruction;
  the flags an instruction of a compiled program reads, each a register that holds 0 or 1
  (carry, zero, sign, overflow, and the direction of the string instructions), so that what
  an instruction does to the flags is an operation like any other, and `pf`, which holds
  the last result, the parity of whose low byte is the parity flag; `ra`, where a return
  address is while a call or a return passes it, x86-64 having no register for it
  (`Lift.lean`); and six registers of the lift's own, for values an instruction computes
  once and uses twice. The auxiliary-carry flag is no register: no instruction that reads it
  is decoded.

  ## Main definitions

  * `Reg`, `Reg.ofGpr`, `allRegs`
-/

import MachineChecked.Lprog.Text

namespace MachineChecked.X86.Lprog

open MachineChecked.Lprog

/-- A register of x86-64 at Lprog. -/
inductive Reg where
  | rax
  | rcx
  | rdx
  | rbx
  | rsp
  | rbp
  | rsi
  | rdi
  | r8
  | r9
  | r10
  | r11
  | r12
  | r13
  | r14
  | r15
  | cf
  | zf
  | sf
  | ovf
  | pf
  | df
  | ra
  | t0
  | t1
  | t2
  | t3
  | t4
  | t5
  deriving DecidableEq, Repr, Inhabited

namespace Reg

/-- The general register with a number. -/
def ofGpr (i : Fin 16) : Reg :=
  match i.val with
  | 0 => .rax
  | 1 => .rcx
  | 2 => .rdx
  | 3 => .rbx
  | 4 => .rsp
  | 5 => .rbp
  | 6 => .rsi
  | 7 => .rdi
  | 8 => .r8
  | 9 => .r9
  | 10 => .r10
  | 11 => .r11
  | 12 => .r12
  | 13 => .r13
  | 14 => .r14
  | _ => .r15

/-- A register's name in Lprog text, and as a Pancake variable. -/
def name : Reg → String
  | .rax => "rax"
  | .rcx => "rcx"
  | .rdx => "rdx"
  | .rbx => "rbx"
  | .rsp => "rsp"
  | .rbp => "rbp"
  | .rsi => "rsi"
  | .rdi => "rdi"
  | .r8 => "r8"
  | .r9 => "r9"
  | .r10 => "r10"
  | .r11 => "r11"
  | .r12 => "r12"
  | .r13 => "r13"
  | .r14 => "r14"
  | .r15 => "r15"
  | .cf => "cf"
  | .zf => "zf"
  | .sf => "sf"
  | .ovf => "ovf"
  | .pf => "pf"
  | .df => "df"
  | .ra => "ra"
  | .t0 => "t0"
  | .t1 => "t1"
  | .t2 => "t2"
  | .t3 => "t3"
  | .t4 => "t4"
  | .t5 => "t5"

end Reg

/-- Every register. -/
def allRegs : List Reg :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .cf, .zf, .sf, .ovf, .pf, .df, .ra, .t0, .t1, .t2, .t3, .t4, .t5]

instance : RegText Reg where
  name := Reg.name
  ofName s := allRegs.find? (·.name == s)
  ofName_name r := by cases r <;> simp [allRegs, Reg.name]

end MachineChecked.X86.Lprog
