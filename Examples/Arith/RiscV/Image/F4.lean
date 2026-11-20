/-
  Examples.Arith.RiscV.Image.F4

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Arith.RiscV.Image.Words

namespace Examples.Arith.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f4_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.mulh)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lret]

/-- The function "smulhi", lifted. -/
def f4 : Lfundef (Op Reg) Reg :=
  { name := "smulhi", addr := 4156, depth := 0,
    body := List.flatten [f4_0] }

kernel_eq f4_head : (liftProg fns)[4]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f4.name, f4.addr, f4.depth)

kernel_eq f4_parts : (liftProg fns)[4]?.map (fun g => chunks chunk g.body) =
    some [f4_0]

/-- **`f4` is the lift of the ELF's words.** -/
theorem f4_eq : (liftProg fns)[4]? = some f4 :=
  getElem?_eq_of_chunks f4_head f4_parts rfl

end

end Examples.Arith.RiscV.Image
