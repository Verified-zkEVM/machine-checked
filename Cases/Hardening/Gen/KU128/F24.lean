/-
  Cases.Hardening.Gen.KU128.F24

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.KU128.Words

namespace Cases.Hardening.Gen.KU128

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f24_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn (Op.set (Reg.x6) (Expr.imm 0x0000000078003eec#64)), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Ltail
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x6)) (Expr.imm 0x0000000000000400#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [11])]

/-- The function "sys_write", lifted. -/
def f24 : Lfundef (Op Reg) Reg :=
  { name := "sys_write", addr := 2013286124, depth := 0,
    body := List.flatten [f24_0] }

kernel_eq f24_head : (liftProg fns)[24]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f24.name, f24.addr, f24.depth)

kernel_eq f24_parts : (liftProg fns)[24]?.map (fun g => chunks chunk g.body) =
    some [f24_0]

/-- **`f24` is the lift of the ELF's words.** -/
theorem f24_eq : (liftProg fns)[24]? = some f24 :=
  getElem?_eq_of_chunks f24_head f24_parts rfl

end

end Cases.Hardening.Gen.KU128
