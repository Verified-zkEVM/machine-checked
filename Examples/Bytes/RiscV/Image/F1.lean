/-
  Examples.Bytes.RiscV.Image.F1

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Bytes.RiscV.Image.Words

namespace Examples.Bytes.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f1_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x11)) (LOperand.imm 0)) 5, LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b1)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x12))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x11)))
  2, LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lret]

/-- The function "fill", lifted. -/
def f1 : Lfundef (Op Reg) Reg :=
  { name := "fill", addr := 65564, depth := 0,
    body := List.flatten [f1_0] }

kernel_eq f1_head : (liftProg fns)[1]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f1.name, f1.addr, f1.depth)

kernel_eq f1_parts : (liftProg fns)[1]?.map (fun g => chunks chunk g.body) =
    some [f1_0]

/-- **`f1` is the lift of the ELF's words.** -/
theorem f1_eq : (liftProg fns)[1]? = some f1 :=
  getElem?_eq_of_chunks f1_head f1_parts rfl

end

end Examples.Bytes.RiscV.Image
