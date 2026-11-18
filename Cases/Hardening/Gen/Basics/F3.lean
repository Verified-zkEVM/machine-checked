/-
  Cases.Hardening.Gen.Basics.F3

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Basics.Words

namespace Cases.Hardening.Gen.Basics

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f3_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lcond
  (LOperand.cmp "ge" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x12)))
  5, LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lcond
  (LOperand.cmp "ge" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x11)))
  7, LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lret, LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lcond
  (LOperand.cmp "lt" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x11)))
  3, LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lret]

/-- The function "clamp", lifted. -/
def f3 : Lfundef (Op Reg) Reg :=
  { name := "clamp", addr := 4132, depth := 0,
    body := List.flatten [f3_0] }

kernel_eq f3_head : (liftProg fns)[3]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f3.name, f3.addr, f3.depth)

kernel_eq f3_parts : (liftProg fns)[3]?.map (fun g => chunks chunk g.body) =
    some [f3_0]

/-- **`f3` is the lift of the ELF's words.** -/
theorem f3_eq : (liftProg fns)[3]? = some f3 :=
  getElem?_eq_of_chunks f3_head f3_parts rfl

end

end Cases.Hardening.Gen.Basics
