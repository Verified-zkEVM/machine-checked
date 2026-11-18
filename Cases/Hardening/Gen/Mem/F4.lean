/-
  Cases.Hardening.Gen.Mem.F4

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Mem.Words

namespace Cases.Hardening.Gen.Mem

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f4_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lret]

/-- The function "load_u8", lifted. -/
def f4 : Lfundef (Op Reg) Reg :=
  { name := "load_u8", addr := 4188, depth := 0,
    body := List.flatten [f4_0] }

kernel_eq f4_head : (liftProg fns)[4]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f4.name, f4.addr, f4.depth)

kernel_eq f4_parts : (liftProg fns)[4]?.map (fun g => chunks chunk g.body) =
    some [f4_0]

/-- **`f4` is the lift of the ELF's words.** -/
theorem f4_eq : (liftProg fns)[4]? = some f4 :=
  getElem?_eq_of_chunks f4_head f4_parts rfl

end

end Cases.Hardening.Gen.Mem
