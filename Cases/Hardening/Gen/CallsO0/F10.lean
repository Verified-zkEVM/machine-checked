/-
  Cases.Hardening.Gen.CallsO0.F10

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.CallsO0.Words

namespace Cases.Hardening.Gen.CallsO0

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f10_0 : Lcmd (Op Reg) Reg :=
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
def f10 : Lfundef (Op Reg) Reg :=
  { name := "_start", addr := 4716, depth := 0,
    body := List.flatten [f10_0] }

kernel_eq f10_head : (liftProg fns)[10]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f10.name, f10.addr, f10.depth)

kernel_eq f10_parts : (liftProg fns)[10]?.map (fun g => chunks chunk g.body) =
    some [f10_0]

/-- **`f10` is the lift of the ELF's words.** -/
theorem f10_eq : (liftProg fns)[10]? = some f10 :=
  getElem?_eq_of_chunks f10_head f10_parts rfl

end

end Cases.Hardening.Gen.CallsO0
