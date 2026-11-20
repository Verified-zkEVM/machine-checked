/-
  Examples.RustBasic.RiscV.Image.F4

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.RustBasic.RiscV.Image.Words

namespace Examples.RustBasic.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f4_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x11)) (LOperand.imm 0)) 10, LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000003#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xfffffffffffffff8#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lcond (LOperand.cmp "ne" (LOperand.reg (Reg.x11)) (LOperand.imm 0)) 4, LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lret, LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lret]

/-- The function "sum_slice", lifted. -/
def f4 : Lfundef (Op Reg) Reg :=
  { name := "sum_slice", addr := 65588, depth := 0,
    body := List.flatten [f4_0] }

kernel_eq f4_head : (liftProg fns)[4]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f4.name, f4.addr, f4.depth)

kernel_eq f4_parts : (liftProg fns)[4]?.map (fun g => chunks chunk g.body) =
    some [f4_0]

/-- **`f4` is the lift of the ELF's words.** -/
theorem f4_eq : (liftProg fns)[4]? = some f4 :=
  getElem?_eq_of_chunks f4_head f4_parts rfl

end

end Examples.RustBasic.RiscV.Image
