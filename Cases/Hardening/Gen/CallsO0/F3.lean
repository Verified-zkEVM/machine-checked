/-
  Cases.Hardening.Gen.CallsO0.F3

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.CallsO0.Words

namespace Cases.Hardening.Gen.CallsO0

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f3_0 : Lcmd (Op Reg) Reg :=
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
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe8#64))
    (Expr.reg (Reg.x10))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe0#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.load
    (Reg.x11)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe8#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe0#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lcall
  0x00000000000010e4#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin
        (BinOp.add)
        (Expr.reg (Reg.x11))
        (Expr.imm 0x0000000000000000#64))
      (Expr.imm 0xfffffffffffffffe#64))
    (List.range 11)), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lret]

/-- The function "apply", lifted. -/
def f3 : Lfundef (Op Reg) Reg :=
  { name := "apply", addr := 4288, depth := 0,
    body := List.flatten [f3_0] }

kernel_eq f3_head : (liftProg fns)[3]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f3.name, f3.addr, f3.depth)

kernel_eq f3_parts : (liftProg fns)[3]?.map (fun g => chunks chunk g.body) =
    some [f3_0]

/-- **`f3` is the lift of the ELF's words.** -/
theorem f3_eq : (liftProg fns)[3]? = some f3 :=
  getElem?_eq_of_chunks f3_head f3_parts rfl

end

end Cases.Hardening.Gen.CallsO0
