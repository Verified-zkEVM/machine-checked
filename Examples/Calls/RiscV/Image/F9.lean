/-
  Examples.Calls.RiscV.Image.F9

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Calls.RiscV.Image.Words

namespace Examples.Calls.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f9_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x11)) (LOperand.imm 0)) 3, LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.div)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lret, LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lcall 0x00000000000010f0#64 (Target.direct 8)]

/-- The function "checked_div", lifted. -/
def f9 : Lfundef (Op Reg) Reg :=
  { name := "checked_div", addr := 4320, depth := 0,
    body := List.flatten [f9_0] }

kernel_eq f9_head : (liftProg fns)[9]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f9.name, f9.addr, f9.depth)

kernel_eq f9_parts : (liftProg fns)[9]?.map (fun g => chunks chunk g.body) =
    some [f9_0]

/-- **`f9` is the lift of the ELF's words.** -/
theorem f9_eq : (liftProg fns)[9]? = some f9 :=
  getElem?_eq_of_chunks f9_head f9_parts rfl

end

end Examples.Calls.RiscV.Image
