/-
  MachineChecked.Lprog.Expr

  The expressions of the low logical program: 64-bit bitvector terms over registers and
  immediates, shared by every instruction set. Operations compute them (`Lprog.Op`), and an
  indirect jump or call computes its target with one.

  The division operations follow RISC-V's total convention (division by zero gives all ones,
  remainder by zero the dividend). An instruction set whose division traps guards it in its
  lift.
-/

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
inductive Expr (Reg : Type) where
  | reg (r : Reg)
  | imm (value : BitVec 64)
  | un (op : UnOp) (e : Expr Reg)
  | bin (op : BinOp) (a b : Expr Reg)
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
def Expr.eval {Reg : Type} (regs : Reg → BitVec 64) : Expr Reg → BitVec 64
  | .reg n => regs n
  | .imm v => v
  | .un op e => op.eval (e.eval regs)
  | .bin op a b => op.eval (a.eval regs) (b.eval regs)

end MachineChecked.Lprog
