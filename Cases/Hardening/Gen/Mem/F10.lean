/-
  Cases.Hardening.Gen.Mem.F10

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Mem.Words

namespace Cases.Hardening.Gen.Mem

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f10_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.load
    (Reg.x11)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000002#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000003#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.un
      (UnOp.sext (Width.b4))
      (Expr.bin
        (BinOp.shl)
        (Expr.reg (Reg.x10))
        (Expr.imm 0x0000000000000018#64)))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lret]

/-- The function "read_le32", lifted. -/
def f10 : Lfundef (Op Reg) Reg :=
  { name := "read_le32", addr := 4248, depth := 0,
    body := List.flatten [f10_0] }

kernel_eq f10_head : (liftProg fns)[10]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f10.name, f10.addr, f10.depth)

kernel_eq f10_parts : (liftProg fns)[10]?.map (fun g => chunks chunk g.body) =
    some [f10_0]

/-- **`f10` is the lift of the ELF's words.** -/
theorem f10_eq : (liftProg fns)[10]? = some f10 :=
  getElem?_eq_of_chunks f10_head f10_parts rfl

end

end Cases.Hardening.Gen.Mem
