/-
  Cases.Hardening.Gen.CallsO0.F9

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.CallsO0.Words

namespace Cases.Hardening.Gen.CallsO0

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f9_0 : Lcmd (Op Reg) Reg :=
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
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe0#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lcond (LOperand.cmp "ne" (LOperand.reg (Reg.x10)) (LOperand.imm 0)) 10, LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lgoto 9, LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lcall 0x0000000000001250#64 (Target.direct 8), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe8#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.load
    (Reg.x11)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffe0#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.div)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lret]

/-- The function "checked_div", lifted. -/
def f9 : Lfundef (Op Reg) Reg :=
  { name := "checked_div", addr := 4648, depth := 0,
    body := List.flatten [f9_0] }

kernel_eq f9_head : (liftProg fns)[9]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f9.name, f9.addr, f9.depth)

kernel_eq f9_parts : (liftProg fns)[9]?.map (fun g => chunks chunk g.body) =
    some [f9_0]

/-- **`f9` is the lift of the ELF's words.** -/
theorem f9_eq : (liftProg fns)[9]? = some f9 :=
  getElem?_eq_of_chunks f9_head f9_parts rfl

end

end Cases.Hardening.Gen.CallsO0
