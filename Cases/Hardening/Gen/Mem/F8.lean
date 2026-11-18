/-
  Cases.Hardening.Gen.Mem.F8

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Mem.Words

namespace Cases.Hardening.Gen.Mem

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f8_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b4)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lret]

/-- The function "load_u32", lifted. -/
def f8 : Lfundef (Op Reg) Reg :=
  { name := "load_u32", addr := 4220, depth := 0,
    body := List.flatten [f8_0] }

kernel_eq f8_head : (liftProg fns)[8]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f8.name, f8.addr, f8.depth)

kernel_eq f8_parts : (liftProg fns)[8]?.map (fun g => chunks chunk g.body) =
    some [f8_0]

/-- **`f8` is the lift of the ELF's words.** -/
theorem f8_eq : (liftProg fns)[8]? = some f8 :=
  getElem?_eq_of_chunks f8_head f8_parts rfl

end

end Cases.Hardening.Gen.Mem
