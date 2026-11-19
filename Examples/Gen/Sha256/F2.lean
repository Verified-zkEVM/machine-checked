/-
  Examples.Gen.Sha256.F2

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Gen.Sha256.Words

namespace Examples.Gen.Sha256

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f2_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xfffffffffffffec0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000138#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000130#64))
    (Expr.reg (Reg.x9))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000128#64))
    (Expr.reg (Reg.x18))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000040#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x14))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x11)) (LOperand.reg (Reg.x12)))
  6, LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000068#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000128#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xfffffffffffffff8#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xffffffffffffffe4#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xffffffffffffffc4#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.load
    (Reg.x16)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xffffffffffffffc0#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x13)))
        (Expr.imm 0x0000000000000011#64)))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x13)) (Expr.imm 0x000000000000000f#64))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x13)))
        (Expr.imm 0x0000000000000013#64)))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x13)) (Expr.imm 0x000000000000000d#64))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x14))
      (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x15)))
        (Expr.imm 0x0000000000000007#64)))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x5))
      (Expr.reg (Reg.x17)))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x15)) (Expr.imm 0x0000000000000019#64))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.bin (BinOp.or) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x6)))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x15)))
        (Expr.imm 0x0000000000000012#64)))), LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x5))
      (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x15)) (Expr.imm 0x000000000000000e#64))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.or) (Expr.reg (Reg.x5)) (Expr.reg (Reg.x7)))), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x17))
      (Expr.reg (Reg.x6)))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x13)))
        (Expr.imm 0x000000000000000a#64)))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x15)))
        (Expr.imm 0x0000000000000003#64)))), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x16))
      (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x17))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x16))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x13))), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 40, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x11)) (LOperand.reg (Reg.x12)))
  13, LinstrR.Llabel (LabelKind.internal) 41, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 42, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 43, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 44, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 45, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 46, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x14))), LinstrR.Llabel (LabelKind.internal) 47, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 48, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x13)) (LOperand.reg (Reg.x11)))
  44, LinstrR.Llabel (LabelKind.internal) 49, LinstrR.Lopn
  (Op.load
    (Reg.x7)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 50, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x000000000000000c#64))), LinstrR.Llabel (LabelKind.internal) 51, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 52, LinstrR.Lopn
  (Op.load
    (Reg.x28)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000014#64))), LinstrR.Llabel (LabelKind.internal) 53, LinstrR.Lopn
  (Op.load
    (Reg.x29)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 54, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x000000000000001c#64))), LinstrR.Llabel (LabelKind.internal) 55, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 56, LinstrR.Lopn
  (Op.load
    (Reg.x16)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000024#64))), LinstrR.Llabel (LabelKind.internal) 57, LinstrR.Lopn (Op.set (Reg.x17) (Expr.imm 0x0000000000010000#64)), LinstrR.Llabel (LabelKind.internal) 58, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x17)) (Expr.imm 0x0000000000000368#64))), LinstrR.Llabel (LabelKind.internal) 59, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 60, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x17)) (Expr.imm 0x0000000000000100#64))), LinstrR.Llabel (LabelKind.internal) 61, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x16)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 62, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x15)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 63, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x14)) (Expr.imm 0x0000000000000000#64)))]

def f2_1 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 64, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x29)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 65, LinstrR.Lopn
  (Op.load
    (Reg.x29)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x17)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 66, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x14)))
        (Expr.imm 0x0000000000000006#64)))), LinstrR.Llabel (LabelKind.internal) 67, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x14)) (Expr.imm 0x000000000000001a#64))), LinstrR.Llabel (LabelKind.internal) 68, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x14)))
        (Expr.imm 0x000000000000000b#64)))), LinstrR.Llabel (LabelKind.internal) 69, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x14)) (Expr.imm 0x0000000000000015#64))), LinstrR.Llabel (LabelKind.internal) 70, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x31)))), LinstrR.Llabel (LabelKind.internal) 71, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x14)))
        (Expr.imm 0x0000000000000019#64)))), LinstrR.Llabel (LabelKind.internal) 72, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x18))
      (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 73, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x14)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 74, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x18))
      (Expr.reg (Reg.x8)))), LinstrR.Llabel (LabelKind.internal) 75, LinstrR.Lopn
  (Op.load
    (Reg.x18)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x5)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 76, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x31))
      (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 77, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x15))
      (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 78, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x17)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 79, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x9))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 80, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x9))
      (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 81, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x31))
      (Expr.reg (Reg.x8)))), LinstrR.Llabel (LabelKind.internal) 82, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x18))
      (Expr.reg (Reg.x29)))), LinstrR.Llabel (LabelKind.internal) 83, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x31))
      (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 84, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x29))
      (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 85, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x29))
      (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 86, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x9))
      (Expr.reg (Reg.x28)))), LinstrR.Llabel (LabelKind.internal) 87, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 88, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 89, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x7)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 90, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x7)))
        (Expr.imm 0x0000000000000002#64)))), LinstrR.Llabel (LabelKind.internal) 91, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x12)) (Expr.imm 0x000000000000001e#64))), LinstrR.Llabel (LabelKind.internal) 92, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x12)))
        (Expr.imm 0x000000000000000d#64)))), LinstrR.Llabel (LabelKind.internal) 93, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000013#64))), LinstrR.Llabel (LabelKind.internal) 94, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x12)))
        (Expr.imm 0x0000000000000016#64)))), LinstrR.Llabel (LabelKind.internal) 95, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x30))
      (Expr.reg (Reg.x7)))), LinstrR.Llabel (LabelKind.internal) 96, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x12)) (Expr.imm 0x000000000000000a#64))), LinstrR.Llabel (LabelKind.internal) 97, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x31)))), LinstrR.Llabel (LabelKind.internal) 98, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x28))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 99, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x30))
      (Expr.reg (Reg.x18)))), LinstrR.Llabel (LabelKind.internal) 100, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x28))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 101, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 102, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x7))
      (Expr.reg (Reg.x31)))), LinstrR.Llabel (LabelKind.internal) 103, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x18)))), LinstrR.Llabel (LabelKind.internal) 104, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x7))
      (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 105, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x31))
      (Expr.reg (Reg.x7)))), LinstrR.Llabel (LabelKind.internal) 106, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x7))
      (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 107, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x5)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 108, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x17)) (LOperand.reg (Reg.x6)))
  61, LinstrR.Llabel (LabelKind.internal) 109, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x7))), LinstrR.Llabel (LabelKind.internal) 110, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x000000000000000c#64))
    (Expr.reg (Reg.x12))), LinstrR.Llabel (LabelKind.internal) 111, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.x13))), LinstrR.Llabel (LabelKind.internal) 112, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000014#64))
    (Expr.reg (Reg.x28))), LinstrR.Llabel (LabelKind.internal) 113, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))
    (Expr.reg (Reg.x29))), LinstrR.Llabel (LabelKind.internal) 114, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x000000000000001c#64))
    (Expr.reg (Reg.x14))), LinstrR.Llabel (LabelKind.internal) 115, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.x15))), LinstrR.Llabel (LabelKind.internal) 116, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000024#64))
    (Expr.reg (Reg.x16))), LinstrR.Llabel (LabelKind.internal) 117, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 118, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 119, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 120, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x14))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 121, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x13))), LinstrR.Llabel (LabelKind.internal) 122, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 123, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 124, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x11)))
  118, LinstrR.Llabel (LabelKind.internal) 125, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000138#64))), LinstrR.Llabel (LabelKind.internal) 126, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000130#64))), LinstrR.Llabel (LabelKind.internal) 127, LinstrR.Lopn
  (Op.load
    (Reg.x18)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000128#64)))]

def f2_2 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 128, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000140#64))), LinstrR.Llabel (LabelKind.internal) 129, LinstrR.Lret]

/-- The function "sha256_compress", lifted. -/
def f2 : Lfundef (Op Reg) Reg :=
  { name := "sha256_compress", addr := 65888, depth := 0,
    body := List.flatten [f2_0, f2_1, f2_2] }

kernel_eq f2_head : (liftProg fns)[2]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f2.name, f2.addr, f2.depth)

kernel_eq f2_parts : (liftProg fns)[2]?.map (fun g => chunks chunk g.body) =
    some [f2_0, f2_1, f2_2]

/-- **`f2` is the lift of the ELF's words.** -/
theorem f2_eq : (liftProg fns)[2]? = some f2 :=
  getElem?_eq_of_chunks f2_head f2_parts rfl

end

end Examples.Gen.Sha256
