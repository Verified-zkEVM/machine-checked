/-
  Examples.Big.RiscV.Image.F0

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Big.RiscV.Image.Words

namespace Examples.Big.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f0_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x00000000000004c0#64))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000490#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000568#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000002#64))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000580#64))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000003#64))), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x00000000000004d8#64))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x00000000000004b8#64))), LinstrR.Llabel (LabelKind.internal) 40, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 41, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 42, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 43, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 44, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 45, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000005#64))), LinstrR.Llabel (LabelKind.internal) 46, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 47, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 48, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x00000000000004a0#64))), LinstrR.Llabel (LabelKind.internal) 49, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 50, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 51, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 52, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 53, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 54, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000006#64))), LinstrR.Llabel (LabelKind.internal) 55, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 56, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 57, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000498#64))), LinstrR.Llabel (LabelKind.internal) 58, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 59, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 60, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 61, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 62, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 63, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64)))]

def f0_1 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 64, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 65, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 66, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x00000000000004e0#64))), LinstrR.Llabel (LabelKind.internal) 67, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 68, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 69, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 70, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 71, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 72, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 73, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 74, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 75, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x00000000000004c8#64))), LinstrR.Llabel (LabelKind.internal) 76, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 77, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 78, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 79, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 80, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 81, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000009#64))), LinstrR.Llabel (LabelKind.internal) 82, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 83, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 84, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000560#64))), LinstrR.Llabel (LabelKind.internal) 85, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 86, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 87, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 88, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 89, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 90, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000a#64))), LinstrR.Llabel (LabelKind.internal) 91, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 92, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 93, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000540#64))), LinstrR.Llabel (LabelKind.internal) 94, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 95, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 96, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 97, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 98, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 99, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000b#64))), LinstrR.Llabel (LabelKind.internal) 100, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 101, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 102, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x00000000000004e8#64))), LinstrR.Llabel (LabelKind.internal) 103, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 104, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 105, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 106, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 107, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 108, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000c#64))), LinstrR.Llabel (LabelKind.internal) 109, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 110, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 111, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x00000000000004f8#64))), LinstrR.Llabel (LabelKind.internal) 112, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 113, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 114, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 115, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 116, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 117, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000d#64))), LinstrR.Llabel (LabelKind.internal) 118, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 119, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 120, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000508#64))), LinstrR.Llabel (LabelKind.internal) 121, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 122, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 123, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 124, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 125, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 126, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000e#64))), LinstrR.Llabel (LabelKind.internal) 127, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11))))]

def f0_2 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 128, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 129, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x00000000000004d0#64))), LinstrR.Llabel (LabelKind.internal) 130, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 131, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 132, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 133, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 134, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 135, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000f#64))), LinstrR.Llabel (LabelKind.internal) 136, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 137, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 138, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000570#64))), LinstrR.Llabel (LabelKind.internal) 139, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 140, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 141, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 142, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 143, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 144, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 145, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 146, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 147, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x00000000000004a8#64))), LinstrR.Llabel (LabelKind.internal) 148, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 149, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 150, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 151, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 152, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 153, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000011#64))), LinstrR.Llabel (LabelKind.internal) 154, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 155, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 156, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000578#64))), LinstrR.Llabel (LabelKind.internal) 157, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 158, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 159, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 160, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 161, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 162, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000012#64))), LinstrR.Llabel (LabelKind.internal) 163, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 164, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 165, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000548#64))), LinstrR.Llabel (LabelKind.internal) 166, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 167, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 168, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 169, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 170, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 171, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000013#64))), LinstrR.Llabel (LabelKind.internal) 172, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 173, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 174, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000550#64))), LinstrR.Llabel (LabelKind.internal) 175, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 176, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 177, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 178, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 179, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 180, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000014#64))), LinstrR.Llabel (LabelKind.internal) 181, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 182, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 183, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x00000000000004f0#64))), LinstrR.Llabel (LabelKind.internal) 184, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 185, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 186, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 187, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 188, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 189, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000015#64))), LinstrR.Llabel (LabelKind.internal) 190, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 191, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64))]

def f0_3 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 192, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000588#64))), LinstrR.Llabel (LabelKind.internal) 193, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 194, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 195, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 196, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 197, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 198, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000016#64))), LinstrR.Llabel (LabelKind.internal) 199, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 200, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 201, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000520#64))), LinstrR.Llabel (LabelKind.internal) 202, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 203, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 204, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 205, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 206, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 207, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000017#64))), LinstrR.Llabel (LabelKind.internal) 208, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 209, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 210, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000528#64))), LinstrR.Llabel (LabelKind.internal) 211, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 212, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 213, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 214, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 215, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 216, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 217, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 218, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 219, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000500#64))), LinstrR.Llabel (LabelKind.internal) 220, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 221, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 222, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 223, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 224, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 225, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000019#64))), LinstrR.Llabel (LabelKind.internal) 226, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 227, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 228, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000510#64))), LinstrR.Llabel (LabelKind.internal) 229, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 230, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 231, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 232, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 233, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 234, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001a#64))), LinstrR.Llabel (LabelKind.internal) 235, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 236, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 237, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x00000000000004b0#64))), LinstrR.Llabel (LabelKind.internal) 238, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 239, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 240, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 241, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 242, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 243, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001b#64))), LinstrR.Llabel (LabelKind.internal) 244, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 245, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 246, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000518#64))), LinstrR.Llabel (LabelKind.internal) 247, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 248, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 249, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 250, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 251, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 252, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001c#64))), LinstrR.Llabel (LabelKind.internal) 253, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 254, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 255, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000530#64)))]

def f0_4 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 256, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 257, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 258, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 259, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 260, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 261, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001d#64))), LinstrR.Llabel (LabelKind.internal) 262, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 263, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 264, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000538#64))), LinstrR.Llabel (LabelKind.internal) 265, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 266, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 267, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 268, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 269, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 270, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001e#64))), LinstrR.Llabel (LabelKind.internal) 271, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 272, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000000002000#64)), LinstrR.Llabel (LabelKind.internal) 273, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000558#64))), LinstrR.Llabel (LabelKind.internal) 274, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 275, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 276, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 277, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 278, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 279, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001f#64))), LinstrR.Llabel (LabelKind.internal) 280, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 281, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 282, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 283, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000039#64))), LinstrR.Llabel (LabelKind.internal) 284, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 285, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 286, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 287, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 288, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 289, LinstrR.Lret]

/-- The function "mix", lifted. -/
def f0 : Lfundef (Op Reg) Reg :=
  { name := "mix", addr := 4096, depth := 0,
    body := List.flatten [f0_0, f0_1, f0_2, f0_3, f0_4] }

kernel_eq f0_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f0.name, f0.addr, f0.depth)

kernel_eq f0_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) =
    some [f0_0, f0_1, f0_2, f0_3, f0_4]

/-- **`f0` is the lift of the ELF's words.** -/
theorem f0_eq : (liftProg fns)[0]? = some f0 :=
  getElem?_eq_of_chunks f0_head f0_parts rfl

end

end Examples.Big.RiscV.Image
