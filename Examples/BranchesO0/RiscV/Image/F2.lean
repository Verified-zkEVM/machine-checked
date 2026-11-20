/-
  Examples.BranchesO0.RiscV.Image.F2

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.BranchesO0.RiscV.Image.Words

namespace Examples.BranchesO0.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f2_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xffffffffffffffd0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.x1))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe8#64))
    (Expr.reg (Reg.x10))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe0#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.load
    (Reg.x11)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe8#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe0#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lcond
  (LOperand.cmp "geu" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x11)))
  13, LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lgoto 10, LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe8#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffd8#64))
    (Expr.reg (Reg.x10))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lgoto 16, LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe0#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffd8#64))
    (Expr.reg (Reg.x10))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lgoto 16, LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffd8#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lret]

/-- The function "umax2", lifted. -/
def f2 : Lfundef (Op Reg) Reg :=
  { name := "umax2", addr := 4244, depth := 0,
    body := List.flatten [f2_0] }

kernel_eq f2_head : (liftProg fns)[2]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f2.name, f2.addr, f2.depth)

kernel_eq f2_parts : (liftProg fns)[2]?.map (fun g => chunks chunk g.body) =
    some [f2_0]

/-- **`f2` is the lift of the ELF's words.** -/
theorem f2_eq : (liftProg fns)[2]? = some f2 :=
  getElem?_eq_of_chunks f2_head f2_parts rfl

end

end Examples.BranchesO0.RiscV.Image
