/-
  Examples.RustBasic.RiscV.Image.F2

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.RustBasic.RiscV.Image.Words

namespace Examples.RustBasic.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f2_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x11)) (LOperand.imm 0)) 5, LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.remu)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lcond (LOperand.cmp "ne" (LOperand.reg (Reg.x12)) (LOperand.imm 0)) 1, LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lret]

/-- The function "gcd", lifted. -/
def f2 : Lfundef (Op Reg) Reg :=
  { name := "gcd", addr := 65552, depth := 0,
    body := List.flatten [f2_0] }

kernel_eq f2_head : (liftProg fns)[2]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f2.name, f2.addr, f2.depth)

kernel_eq f2_parts : (liftProg fns)[2]?.map (fun g => chunks chunk g.body) =
    some [f2_0]

/-- **`f2` is the lift of the ELF's words.** -/
theorem f2_eq : (liftProg fns)[2]? = some f2 :=
  getElem?_eq_of_chunks f2_head f2_parts rfl

end

end Examples.RustBasic.RiscV.Image
