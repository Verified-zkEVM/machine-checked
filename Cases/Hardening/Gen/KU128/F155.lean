/-
  Cases.Hardening.Gen.KU128.F155

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.KU128.Words

namespace Cases.Hardening.Gen.KU128

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f155_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xffffffffffffffd0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.x1))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffd0#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x000000007800edac#64)), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lcall
  0x000000007800edb4#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0xfffffffffffff868#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [154]), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffd0#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.load
    (Reg.x11)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xffffffffffffffd8#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lret]

/-- The function "__udivti3", lifted. -/
def f155 : Lfundef (Op Reg) Reg :=
  { name := "__udivti3", addr := 2013326728, depth := 0,
    body := List.flatten [f155_0] }

kernel_eq f155_head : (liftProg fns)[155]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f155.name, f155.addr, f155.depth)

kernel_eq f155_parts : (liftProg fns)[155]?.map (fun g => chunks chunk g.body) =
    some [f155_0]

/-- **`f155` is the lift of the ELF's words.** -/
theorem f155_eq : (liftProg fns)[155]? = some f155 :=
  getElem?_eq_of_chunks f155_head f155_parts rfl

end

end Cases.Hardening.Gen.KU128
