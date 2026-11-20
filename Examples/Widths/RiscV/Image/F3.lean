/-
  Examples.Widths.RiscV.Image.F3

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Widths.RiscV.Image.Words

namespace Examples.Widths.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f3_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b1)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lret]

/-- The function "load_s8", lifted. -/
def f3 : Lfundef (Op Reg) Reg :=
  { name := "load_s8", addr := 4180, depth := 0,
    body := List.flatten [f3_0] }

kernel_eq f3_head : (liftProg fns)[3]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f3.name, f3.addr, f3.depth)

kernel_eq f3_parts : (liftProg fns)[3]?.map (fun g => chunks chunk g.body) =
    some [f3_0]

/-- **`f3` is the lift of the ELF's words.** -/
theorem f3_eq : (liftProg fns)[3]? = some f3 :=
  getElem?_eq_of_chunks f3_head f3_parts rfl

end

end Examples.Widths.RiscV.Image
