/-
  Examples.Sp1Runtime.RiscV.Image.F104

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Sp1Runtime.RiscV.Image.Words

namespace Examples.Sp1Runtime.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f104_0 : Lcmd (Op Reg) Reg :=
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
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0xfffffffffffffff0#64))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x12)) (LOperand.imm 0)) 14, LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0xfffffffffffffff0#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x9)) (LOperand.imm 0)) 7, LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.load
    (Reg.x11)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lgoto 16, LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000002#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x00000000780050a8#64)), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lcall
  0x000000007800c0b0#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0xfffffffffffffe44#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [24]), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lret]

/-- The function "_RNvYNtNtNtNtCsaFPe17dgLU6_3std3sys5stdio4zkvm6StderrNtNtBa_2io5Write14write_vectoredBa_", lifted. -/
def f104 : Lfundef (Op Reg) Reg :=
  { name := "_RNvYNtNtNtNtCsaFPe17dgLU6_3std3sys5stdio4zkvm6StderrNtNtBa_2io5Write14write_vectoredBa_", addr := 2013315168, depth := 0,
    body := List.flatten [f104_0] }

kernel_eq f104_head : (liftProg fns)[104]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f104.name, f104.addr, f104.depth)

kernel_eq f104_parts : (liftProg fns)[104]?.map (fun g => chunks chunk g.body) =
    some [f104_0]

/-- **`f104` is the lift of the ELF's words.** -/
theorem f104_eq : (liftProg fns)[104]? = some f104 :=
  getElem?_eq_of_chunks f104_head f104_parts rfl

end

end Examples.Sp1Runtime.RiscV.Image
