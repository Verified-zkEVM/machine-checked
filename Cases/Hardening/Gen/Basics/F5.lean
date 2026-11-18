/-
  Cases.Hardening.Gen.Basics.F5

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Basics.Words

namespace Cases.Hardening.Gen.Basics

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f5_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x10)) (LOperand.imm 0)) 44, LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn (Op.set (Reg.x12) (Expr.imm 0x0000000055555000#64)), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn (Op.set (Reg.x13) (Expr.imm 0x0000000033333000#64)), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn (Op.set (Reg.x14) (Expr.imm 0x000000000f0f1000#64)), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn (Op.set (Reg.x15) (Expr.imm 0x0000000001010000#64)), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000555#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000333#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x14)) (Expr.imm 0xffffffffffffff0f#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x15)) (Expr.imm 0x0000000000000101#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000002#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x14)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x14))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.imm 0xffffffffffffffff#64))), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x15))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.sub)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000002#64))), LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 40, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.mul)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 41, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000038#64))), LinstrR.Llabel (LabelKind.internal) 42, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000040#64))), LinstrR.Llabel (LabelKind.internal) 43, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.sub)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 44, LinstrR.Lret]

/-- The function "count_down", lifted. -/
def f5 : Lfundef (Op Reg) Reg :=
  { name := "count_down", addr := 4216, depth := 0,
    body := List.flatten [f5_0] }

kernel_eq f5_head : (liftProg fns)[5]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f5.name, f5.addr, f5.depth)

kernel_eq f5_parts : (liftProg fns)[5]?.map (fun g => chunks chunk g.body) =
    some [f5_0]

/-- **`f5` is the lift of the ELF's words.** -/
theorem f5_eq : (liftProg fns)[5]? = some f5 :=
  getElem?_eq_of_chunks f5_head f5_parts rfl

end

end Cases.Hardening.Gen.Basics
