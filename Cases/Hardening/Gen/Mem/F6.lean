/-
  Cases.Hardening.Gen.Mem.F6

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Mem.Words

namespace Cases.Hardening.Gen.Mem

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f6_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b2)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lret]

/-- The function "load_u16", lifted. -/
def f6 : Lfundef (Op Reg) Reg :=
  { name := "load_u16", addr := 4204, depth := 0,
    body := List.flatten [f6_0] }

kernel_eq f6_head : (liftProg fns)[6]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f6.name, f6.addr, f6.depth)

kernel_eq f6_parts : (liftProg fns)[6]?.map (fun g => chunks chunk g.body) =
    some [f6_0]

/-- **`f6` is the lift of the ELF's words.** -/
theorem f6_eq : (liftProg fns)[6]? = some f6 :=
  getElem?_eq_of_chunks f6_head f6_parts rfl

end

end Cases.Hardening.Gen.Mem
