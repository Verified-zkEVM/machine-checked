/-
  MachineChecked.Lprog.Op

  The operations of the low logical program, shared by every instruction set.

  An operation writes a register with the value of an expression (`set`), loads from memory
  into a register (`load`), stores to memory (`store`), or does nothing (`skip`). Expressions
  are 64-bit bitvector terms over registers and immediates (`Lprog.Expr`). Memory is the
  instruction set's:
  an `Mem` gives the load and store of each width, and may refuse an access (a fault), which
  is how an execution environment's memory checks enter. Conditions compare two operands.

  An instruction set that uses these operations is `Isa.ofOps`: its lift translates each
  instruction into an `Op`, and proves the translation agrees with its machine. So
  everything stated over `Op` (program logics, specifications) is independent of the
  instruction set.
-/

import MachineChecked.Lprog.Sem

namespace MachineChecked.Lprog

/-- An operation. -/
inductive Op (Reg : Type) where
  /-- Write the value of `e` to register `dst`. -/
  | set (dst : Reg) (e : Expr Reg)
  /-- Load `w` bytes at the address `addr`, zero- or sign-extended, into `dst`. -/
  | load (dst : Reg) (w : Width) (signed : Bool) (addr : Expr Reg)
  /-- Store the low `w` bytes of `src` at the address `addr`. -/
  | store (w : Width) (addr : Expr Reg) (src : Expr Reg)
  | skip
  deriving DecidableEq, Repr

/-- An instruction set's memory: the load and store of each width. `none` is a fault. A load
    gives the value zero-extended to 64 bits; a store writes the low bytes of its value. -/
structure Mem (M : Type) where
  load : Width → BitVec 64 → M → Option (BitVec 64)
  store : Width → BitVec 64 → BitVec 64 → M → Option M

/-- The meaning of an operation. -/
def Op.eval {Reg M : Type} [DecidableEq Reg] (mem : Mem M) :
    Op Reg → (Reg → BitVec 64) → M → Option ((Reg → BitVec 64) × M)
  | .set d e, regs, m => some (updReg regs d (e.eval regs), m)
  | .load d w s a, regs, m =>
    (mem.load w (a.eval regs) m).map fun v =>
      (updReg regs d (if s then (UnOp.sext w).eval v else v), m)
  | .store w a e, regs, m => (mem.store w (a.eval regs) (e.eval regs) m).map fun m' => (regs, m')
  | .skip, regs, m => some (regs, m)

/-! ## Conditions -/

/-- An operand's value: a register, or an immediate. -/
def operandVal {Reg : Type} (regs : Reg → BitVec 64) : LOperand Reg → Option (BitVec 64)
  | .reg n => some (regs n)
  | .imm v => some (BitVec.ofInt 64 v)
  | _ => none

/-- The comparison a condition names. -/
def cmpEval (op : String) (a b : BitVec 64) : Option Bool :=
  if op = "eq" then some (a == b)
  else if op = "ne" then some (a != b)
  else if op = "lt" then some (BitVec.slt a b)
  else if op = "ge" then some (!BitVec.slt a b)
  else if op = "ltu" then some (BitVec.ult a b)
  else if op = "geu" then some (!BitVec.ult a b)
  else none

/-- A branch condition: a comparison of two operands. -/
def condEval {Reg : Type} (c : LOperand Reg) (regs : Reg → BitVec 64) : Option Bool :=
  match c with
  | .cmp op a b => do cmpEval op (← operandVal regs a) (← operandVal regs b)
  | _ => none

/-- **An instruction set over the shared operations**: its registers, link register and stack
    pointer, its state beside the registers `M`, and its memory. -/
abbrev Isa.ofOps (Reg : Type) [DecidableEq Reg] (link sp : Reg) (M : Type) (mem : Mem M) : Isa where
  Op := MachineChecked.Lprog.Op Reg
  Reg := Reg
  link := link
  sp := sp
  M := M
  opn o regs m := o.eval mem regs m
  cond c regs _ := condEval c regs

end MachineChecked.Lprog
