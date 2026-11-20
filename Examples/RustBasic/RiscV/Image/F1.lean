/-
  Examples.RustBasic.RiscV.Image.F1

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.RustBasic.RiscV.Image.Words

namespace Examples.RustBasic.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f1_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lret]

/-- The function "add3", lifted. -/
def f1 : Lfundef (Op Reg) Reg :=
  { name := "add3", addr := 65540, depth := 0,
    body := List.flatten [f1_0] }

kernel_eq f1_head : (liftProg fns)[1]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f1.name, f1.addr, f1.depth)

kernel_eq f1_parts : (liftProg fns)[1]?.map (fun g => chunks chunk g.body) =
    some [f1_0]

/-- **`f1` is the lift of the ELF's words.** -/
theorem f1_eq : (liftProg fns)[1]? = some f1 :=
  getElem?_eq_of_chunks f1_head f1_parts rfl

end

end Examples.RustBasic.RiscV.Image
