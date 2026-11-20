/-
  Examples.Widths.RiscV.Image.F9

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Widths.RiscV.Image.Words

namespace Examples.Widths.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f9_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.store
    (Width.b1)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000002#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b4)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000004#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lret]

/-- The function "store_widths", lifted. -/
def f9 : Lfundef (Op Reg) Reg :=
  { name := "store_widths", addr := 4228, depth := 0,
    body := List.flatten [f9_0] }

kernel_eq f9_head : (liftProg fns)[9]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f9.name, f9.addr, f9.depth)

kernel_eq f9_parts : (liftProg fns)[9]?.map (fun g => chunks chunk g.body) =
    some [f9_0]

/-- **`f9` is the lift of the ELF's words.** -/
theorem f9_eq : (liftProg fns)[9]? = some f9 :=
  getElem?_eq_of_chunks f9_head f9_parts rfl

end

end Examples.Widths.RiscV.Image
