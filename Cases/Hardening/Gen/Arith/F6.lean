/-
  Cases.Hardening.Gen.Arith.F6

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Arith.Words

namespace Cases.Hardening.Gen.Arith

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f6_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x10)) (LOperand.imm 0)) 6, LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0xffffffffffffffff#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lcond (LOperand.cmp "ne" (LOperand.reg (Reg.x10)) (LOperand.imm 0)) 2, LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lret]

/-- The function "popcount", lifted. -/
def f6 : Lfundef (Op Reg) Reg :=
  { name := "popcount", addr := 4208, depth := 0,
    body := List.flatten [f6_0] }

kernel_eq f6_head : (liftProg fns)[6]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f6.name, f6.addr, f6.depth)

kernel_eq f6_parts : (liftProg fns)[6]?.map (fun g => chunks chunk g.body) =
    some [f6_0]

/-- **`f6` is the lift of the ELF's words.** -/
theorem f6_eq : (liftProg fns)[6]? = some f6 :=
  getElem?_eq_of_chunks f6_head f6_parts rfl

end

end Cases.Hardening.Gen.Arith
