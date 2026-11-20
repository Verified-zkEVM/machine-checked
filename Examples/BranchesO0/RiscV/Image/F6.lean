/-
  Examples.BranchesO0.RiscV.Image.F6

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.BranchesO0.RiscV.Image.Words

namespace Examples.BranchesO0.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f6_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xfffffffffffffff0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x1))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lgoto 5, LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lgoto 5]

/-- The function "_start", lifted. -/
def f6 : Lfundef (Op Reg) Reg :=
  { name := "_start", addr := 4676, depth := 0,
    body := List.flatten [f6_0] }

kernel_eq f6_head : (liftProg fns)[6]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f6.name, f6.addr, f6.depth)

kernel_eq f6_parts : (liftProg fns)[6]?.map (fun g => chunks chunk g.body) =
    some [f6_0]

/-- **`f6` is the lift of the ELF's words.** -/
theorem f6_eq : (liftProg fns)[6]? = some f6 :=
  getElem?_eq_of_chunks f6_head f6_parts rfl

end

end Examples.BranchesO0.RiscV.Image
