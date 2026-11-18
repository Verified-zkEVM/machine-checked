/-
  Cases.Hardening.Gen.Arith.F5

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Arith.Words

namespace Cases.Hardening.Gen.Arith

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f5_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.shl)
      (Expr.reg (Reg.x10))
      (Expr.bin
        (BinOp.and)
        (Expr.reg (Reg.x11))
        (Expr.imm 0x000000000000003f#64)))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.sub) (Expr.imm 0x0000000000000000#64) (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.bin
        (BinOp.and)
        (Expr.reg (Reg.x11))
        (Expr.imm 0x000000000000003f#64)))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x12))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lret]

/-- The function "rotl", lifted. -/
def f5 : Lfundef (Op Reg) Reg :=
  { name := "rotl", addr := 4188, depth := 0,
    body := List.flatten [f5_0] }

kernel_eq f5_head : (liftProg fns)[5]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f5.name, f5.addr, f5.depth)

kernel_eq f5_parts : (liftProg fns)[5]?.map (fun g => chunks chunk g.body) =
    some [f5_0]

/-- **`f5` is the lift of the ELF's words.** -/
theorem f5_eq : (liftProg fns)[5]? = some f5 :=
  getElem?_eq_of_chunks f5_head f5_parts rfl

end

end Cases.Hardening.Gen.Arith
