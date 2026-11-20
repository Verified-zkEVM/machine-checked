/-
  Examples.Gen.Sha256.F1

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Gen.Sha256.Words

namespace Examples.Gen.Sha256

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f1_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000040#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000100#64))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xfffffffffffffff8#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xffffffffffffffe4#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xffffffffffffffc4#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xffffffffffffffc0#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x12)))
        (Expr.imm 0x0000000000000011#64)))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x12)) (Expr.imm 0x000000000000000f#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x12)))
        (Expr.imm 0x0000000000000013#64)))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x12)) (Expr.imm 0x000000000000000d#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x14)))
        (Expr.imm 0x0000000000000007#64)))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x17))
      (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x14)) (Expr.imm 0x0000000000000019#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.or) (Expr.reg (Reg.x6)) (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x14)))
        (Expr.imm 0x0000000000000012#64)))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x17))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x14)) (Expr.imm 0x000000000000000e#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x17))
      (Expr.reg (Reg.x6)))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x16))
      (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x12)))
        (Expr.imm 0x000000000000000a#64)))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x14)))
        (Expr.imm 0x0000000000000003#64)))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x15))
      (Expr.reg (Reg.x17)))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x16))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x15))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x12))), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x11)) (LOperand.reg (Reg.x10)))
  2, LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lret]

/-- The function "sha256_schedule", lifted. -/
def f1 : Lfundef (Op Reg) Reg :=
  { name := "sha256_schedule", addr := 65764, depth := 0,
    body := List.flatten [f1_0] }

kernel_eq f1_head : (liftProg fns)[1]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f1.name, f1.addr, f1.depth)

kernel_eq f1_parts : (liftProg fns)[1]?.map (fun g => chunks chunk g.body) =
    some [f1_0]

/-- **`f1` is the lift of the ELF's words.** -/
theorem f1_eq : (liftProg fns)[1]? = some f1 :=
  getElem?_eq_of_chunks f1_head f1_parts rfl

end

end Examples.Gen.Sha256
