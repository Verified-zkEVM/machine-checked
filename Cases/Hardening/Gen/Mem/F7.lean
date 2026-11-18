/-
  Cases.Hardening.Gen.Mem.F7

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Mem.Words

namespace Cases.Hardening.Gen.Mem

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f7_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b4)
    true
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lret]

/-- The function "load_s32", lifted. -/
def f7 : Lfundef (Op Reg) Reg :=
  { name := "load_s32", addr := 4212, depth := 0,
    body := List.flatten [f7_0] }

kernel_eq f7_head : (liftProg fns)[7]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f7.name, f7.addr, f7.depth)

kernel_eq f7_parts : (liftProg fns)[7]?.map (fun g => chunks chunk g.body) =
    some [f7_0]

/-- **`f7` is the lift of the ELF's words.** -/
theorem f7_eq : (liftProg fns)[7]? = some f7 :=
  getElem?_eq_of_chunks f7_head f7_parts rfl

end

end Cases.Hardening.Gen.Mem
