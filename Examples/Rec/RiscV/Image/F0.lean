/-
  Examples.Rec.RiscV.Image.F0

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Rec.RiscV.Image.Words

namespace Examples.Rec.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f0_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xffffffffffffffe0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))
    (Expr.reg (Reg.x1))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x9))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x18))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000002#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lcond
  (LOperand.cmp "ltu" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x11)))
  15, LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffff#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lcall 0x0000000000001030#64 (Target.direct 0), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xfffffffffffffffe#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lcond
  (LOperand.cmp "ltu" (LOperand.reg (Reg.x18)) (LOperand.reg (Reg.x8)))
  10, LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.load
    (Reg.x18)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lret]

/-- The function "fib", lifted. -/
def f0 : Lfundef (Op Reg) Reg :=
  { name := "fib", addr := 4096, depth := 0,
    body := List.flatten [f0_0] }

kernel_eq f0_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f0.name, f0.addr, f0.depth)

kernel_eq f0_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) =
    some [f0_0]

/-- **`f0` is the lift of the ELF's words.** -/
theorem f0_eq : (liftProg fns)[0]? = some f0 :=
  getElem?_eq_of_chunks f0_head f0_parts rfl

end

end Examples.Rec.RiscV.Image
