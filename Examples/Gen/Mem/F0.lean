/-
  Examples.Gen.Mem.F0

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Gen.Mem.Words

namespace Examples.Gen.Mem

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f0_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x12)) (LOperand.imm 0)) 7, LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.store
    (Width.b1)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x13))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x12)))
  2, LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lret]

/-- The function "copy_bytes", lifted. -/
def f0 : Lfundef (Op Reg) Reg :=
  { name := "copy_bytes", addr := 65536, depth := 0,
    body := List.flatten [f0_0] }

kernel_eq f0_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f0.name, f0.addr, f0.depth)

kernel_eq f0_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) =
    some [f0_0]

/-- **`f0` is the lift of the ELF's words.** -/
theorem f0_eq : (liftProg fns)[0]? = some f0 :=
  getElem?_eq_of_chunks f0_head f0_parts rfl

end

end Examples.Gen.Mem
