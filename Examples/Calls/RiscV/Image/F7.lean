/-
  Examples.Calls.RiscV.Image.F7

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Calls.RiscV.Image.Words

namespace Examples.Calls.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f7_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Ltail (Target.direct 0)]

/-- The function "tail_inc", lifted. -/
def f7 : Lfundef (Op Reg) Reg :=
  { name := "tail_inc", addr := 4308, depth := 0,
    body := List.flatten [f7_0] }

kernel_eq f7_head : (liftProg fns)[7]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f7.name, f7.addr, f7.depth)

kernel_eq f7_parts : (liftProg fns)[7]?.map (fun g => chunks chunk g.body) =
    some [f7_0]

/-- **`f7` is the lift of the ELF's words.** -/
theorem f7_eq : (liftProg fns)[7]? = some f7 :=
  getElem?_eq_of_chunks f7_head f7_parts rfl

end

end Examples.Calls.RiscV.Image
