/-
  MachineChecked.Lprog.Op

  The operations of the low logical program, shared by every instruction set.

  An operation writes a register with the value of an expression (`set`), loads from memory
  into a register (`load`), stores to memory (`store`), or does nothing (`skip`). Expressions
  are 64-bit bitvector terms over registers and immediates. Memory is the instruction set's:
  an `Mem` gives the load and store of each width, and may refuse an access (a fault), which
  is how an execution environment's memory checks enter. Conditions compare two operands.

  An instruction set that uses these operations is `Isa.ofOps`: its lift translates each
  instruction into an `Op`, and proves the translation agrees with its machine. So
  everything stated over `Op` (program logics, specifications) is independent of the
  instruction set.

  The division operations follow RISC-V's total convention (division by zero gives all ones,
  remainder by zero the dividend). An instruction set whose division traps guards it in its
  lift.
-/

import MachineChecked.Lprog.Sem

namespace MachineChecked.Lprog

/-- The width of a memory access or of a sign or zero extension. -/
inductive Width where
  | b1
  | b2
  | b4
  | b8
  deriving DecidableEq, Repr

/-- The width in bits. -/
def Width.bits : Width → Nat
  | .b1 => 8
  | .b2 => 16
  | .b4 => 32
  | .b8 => 64

/-- The width in bytes. -/
def Width.bytes : Width → Nat
  | .b1 => 1
  | .b2 => 2
  | .b4 => 4
  | .b8 => 8

/-- A unary operation on a 64-bit value. -/
inductive UnOp where
  /-- Sign-extend the low `w` bits. -/
  | sext (w : Width)
  /-- Zero-extend the low `w` bits. -/
  | zext (w : Width)
  | not
  | neg
  deriving DecidableEq, Repr

/-- A binary operation on 64-bit values. Shifts take the amount as given (an instruction set
    that masks its shift amounts says so in its lift); comparisons give 1 or 0. -/
inductive BinOp where
  | add
  | sub
  | mul
  | and
  | or
  | xor
  | shl
  | lshr
  | ashr
  /-- Signed less-than. -/
  | slt
  /-- Unsigned less-than. -/
  | ult
  /-- The high half of the signed product. -/
  | mulh
  /-- The high half of the product of a signed and an unsigned value. -/
  | mulhsu
  /-- The high half of the unsigned product. -/
  | mulhu
  | div
  | divu
  | rem
  | remu
  deriving DecidableEq, Repr

/-- An expression: a 64-bit value computed from registers and immediates. -/
inductive Expr where
  | reg (name : String)
  | imm (value : BitVec 64)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (a b : Expr)
  deriving DecidableEq, Repr

/-- The meaning of a unary operation. -/
def UnOp.eval : UnOp → BitVec 64 → BitVec 64
  | .sext w, x => (x.setWidth w.bits).signExtend 64
  | .zext w, x => (x.setWidth w.bits).zeroExtend 64
  | .not, x => ~~~x
  | .neg, x => -x

/-- The meaning of a binary operation. -/
def BinOp.eval : BinOp → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< b.toNat
  | .lshr, a, b => a >>> b.toNat
  | .ashr, a, b => BitVec.sshiftRight a b.toNat
  | .slt, a, b => if BitVec.slt a b then 1 else 0
  | .ult, a, b => if BitVec.ult a b then 1 else 0
  | .mulh, a, b => ((a.signExtend 128 * b.signExtend 128) >>> 64).truncate 64
  | .mulhsu, a, b => ((a.signExtend 128 * b.zeroExtend 128) >>> 64).truncate 64
  | .mulhu, a, b => ((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).truncate 64
  | .div, a, b => if b == 0#64 then BitVec.allOnes 64 else BitVec.sdiv a b
  | .divu, a, b => if b == 0#64 then BitVec.allOnes 64 else a / b
  | .rem, a, b => if b == 0#64 then a else BitVec.srem a b
  | .remu, a, b => if b == 0#64 then a else a % b

/-- The value of an expression. -/
def Expr.eval (regs : String → BitVec 64) : Expr → BitVec 64
  | .reg n => regs n
  | .imm v => v
  | .un op e => op.eval (e.eval regs)
  | .bin op a b => op.eval (a.eval regs) (b.eval regs)

/-- An operation. -/
inductive Op where
  /-- Write the value of `e` to register `dst`. -/
  | set (dst : String) (e : Expr)
  /-- Load `w` bytes at the address `addr`, zero- or sign-extended, into `dst`. -/
  | load (dst : String) (w : Width) (signed : Bool) (addr : Expr)
  /-- Store the low `w` bytes of `src` at the address `addr`. -/
  | store (w : Width) (addr : Expr) (src : Expr)
  | skip
  deriving DecidableEq, Repr

/-- An instruction set's memory: the load and store of each width. `none` is a fault. A load
    gives the value zero-extended to 64 bits; a store writes the low bytes of its value. -/
structure Mem (M : Type) where
  load : Width → BitVec 64 → M → Option (BitVec 64)
  store : Width → BitVec 64 → BitVec 64 → M → Option M

/-- The meaning of an operation. -/
def Op.eval {M : Type} (mem : Mem M) :
    Op → (String → BitVec 64) → M → Option ((String → BitVec 64) × M)
  | .set d e, regs, m => some (updReg regs d (e.eval regs), m)
  | .load d w s a, regs, m =>
    (mem.load w (a.eval regs) m).map fun v =>
      (updReg regs d (if s then (UnOp.sext w).eval v else v), m)
  | .store w a e, regs, m => (mem.store w (a.eval regs) (e.eval regs) m).map fun m' => (regs, m')
  | .skip, regs, m => some (regs, m)

/-! ## Conditions -/

/-- An operand's value: a register, or an immediate. -/
def operandVal (regs : String → BitVec 64) : LOperand → Option (BitVec 64)
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
def condEval (c : LOperand) (regs : String → BitVec 64) : Option Bool :=
  match c with
  | .cmp op a b => do cmpEval op (← operandVal regs a) (← operandVal regs b)
  | _ => none

/-- **An instruction set over the shared operations**: its state beside the registers `M`, and
    its memory. -/
abbrev Isa.ofOps (M : Type) (mem : Mem M) : Isa where
  Op := MachineChecked.Lprog.Op
  M := M
  opn o regs m := o.eval mem regs m
  cond c regs _ := condEval c regs

end MachineChecked.Lprog
