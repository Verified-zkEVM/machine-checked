/-
  Examples.Sha256.RiscV.Image.F0

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Sha256.RiscV.Image.Words

namespace Examples.Sha256.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f0_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xfffffffffffffff0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.load
    (Reg.x6)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000c#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.load
    (Reg.x16)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.load
    (Reg.x17)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000014#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.load
    (Reg.x5)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.load
    (Reg.x7)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001c#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x16)))
        (Expr.imm 0x0000000000000006#64)))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x16)) (Expr.imm 0x000000000000001a#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x16)))
        (Expr.imm 0x000000000000000b#64)))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x16)) (Expr.imm 0x0000000000000015#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x16)))
        (Expr.imm 0x0000000000000019#64)))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x16)) (Expr.imm 0x0000000000000007#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x7)))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x13)))
        (Expr.imm 0x0000000000000002#64)))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x28))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x13)) (Expr.imm 0x000000000000001e#64))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x30))
      (Expr.reg (Reg.x29)))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x13)))
        (Expr.imm 0x000000000000000d#64)))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.x31)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x31)))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000013#64))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x28))
      (Expr.reg (Reg.x7)))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.lshr)
        (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x13)))
        (Expr.imm 0x0000000000000016#64)))), LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x13)) (Expr.imm 0x000000000000000a#64))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x28)))), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x29)))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x15))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x7))
      (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x15))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x29))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lopn
  (Op.set
    (Reg.x29)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x29))
      (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x31)))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x17))
      (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x30))
      (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x30))
      (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 40, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 41, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x7))
      (Expr.reg (Reg.x28)))), LinstrR.Llabel (LabelKind.internal) 42, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 43, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x29))
      (Expr.reg (Reg.x7)))), LinstrR.Llabel (LabelKind.internal) 44, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x6)))), LinstrR.Llabel (LabelKind.internal) 45, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x7))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 46, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.x6))), LinstrR.Llabel (LabelKind.internal) 47, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000014#64))
    (Expr.reg (Reg.x16))), LinstrR.Llabel (LabelKind.internal) 48, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000018#64))
    (Expr.reg (Reg.x17))), LinstrR.Llabel (LabelKind.internal) 49, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000001c#64))
    (Expr.reg (Reg.x5))), LinstrR.Llabel (LabelKind.internal) 50, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 51, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000004#64))
    (Expr.reg (Reg.x13))), LinstrR.Llabel (LabelKind.internal) 52, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x14))), LinstrR.Llabel (LabelKind.internal) 53, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000000c#64))
    (Expr.reg (Reg.x15))), LinstrR.Llabel (LabelKind.internal) 54, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 55, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 56, LinstrR.Lret]

/-- The function "sha256_round", lifted. -/
def f0 : Lfundef (Op Reg) Reg :=
  { name := "sha256_round", addr := 65536, depth := 0,
    body := List.flatten [f0_0] }

kernel_eq f0_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f0.name, f0.addr, f0.depth)

kernel_eq f0_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) =
    some [f0_0]

/-- **`f0` is the lift of the ELF's words.** -/
theorem f0_eq : (liftProg fns)[0]? = some f0 :=
  getElem?_eq_of_chunks f0_head f0_parts rfl

end

end Examples.Sha256.RiscV.Image
