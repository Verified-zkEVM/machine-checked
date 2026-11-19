/-
  Examples.Gen.Bytes.F0

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Gen.Bytes.Words

namespace Examples.Gen.Bytes

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f0_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lcond (LOperand.cmp "ne" (LOperand.reg (Reg.x12)) (LOperand.imm 0)) 1, LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xffffffffffffffff#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lret]

/-- The function "str_len", lifted. -/
def f0 : Lfundef (Op Reg) Reg :=
  { name := "str_len", addr := 65536, depth := 0,
    body := List.flatten [f0_0] }

kernel_eq f0_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f0.name, f0.addr, f0.depth)

kernel_eq f0_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) =
    some [f0_0]

/-- **`f0` is the lift of the ELF's words.** -/
theorem f0_eq : (liftProg fns)[0]? = some f0 :=
  getElem?_eq_of_chunks f0_head f0_parts rfl

end

end Examples.Gen.Bytes
