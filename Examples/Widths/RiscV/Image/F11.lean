/-
  Examples.Widths.RiscV.Image.F11

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Widths.RiscV.Image.Words

namespace Examples.Widths.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f11_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x12))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x13))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lret]

/-- The function "swap", lifted. -/
def f11 : Lfundef (Op Reg) Reg :=
  { name := "swap", addr := 4292, depth := 0,
    body := List.flatten [f11_0] }

kernel_eq f11_head : (liftProg fns)[11]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f11.name, f11.addr, f11.depth)

kernel_eq f11_parts : (liftProg fns)[11]?.map (fun g => chunks chunk g.body) =
    some [f11_0]

/-- **`f11` is the lift of the ELF's words.** -/
theorem f11_eq : (liftProg fns)[11]? = some f11 :=
  getElem?_eq_of_chunks f11_head f11_parts rfl

end

end Examples.Widths.RiscV.Image
