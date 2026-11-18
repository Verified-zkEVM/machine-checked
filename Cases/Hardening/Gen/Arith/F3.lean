/-
  Cases.Hardening.Gen.Arith.F3

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Arith.Words

namespace Cases.Hardening.Gen.Arith

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f3_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.mulhu)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lret]

/-- The function "mulhi", lifted. -/
def f3 : Lfundef (Op Reg) Reg :=
  { name := "mulhi", addr := 4148, depth := 0,
    body := List.flatten [f3_0] }

kernel_eq f3_head : (liftProg fns)[3]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f3.name, f3.addr, f3.depth)

kernel_eq f3_parts : (liftProg fns)[3]?.map (fun g => chunks chunk g.body) =
    some [f3_0]

/-- **`f3` is the lift of the ELF's words.** -/
theorem f3_eq : (liftProg fns)[3]? = some f3 :=
  getElem?_eq_of_chunks f3_head f3_parts rfl

end

end Cases.Hardening.Gen.Arith
