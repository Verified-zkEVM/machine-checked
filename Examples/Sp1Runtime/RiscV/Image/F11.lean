/-
  Examples.Sp1Runtime.RiscV.Image.F11

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Sp1Runtime.RiscV.Image.Words

namespace Examples.Sp1Runtime.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f11_0 : Lcmd (Op Reg) Reg :=
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
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))
    (Expr.reg (Reg.x9))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.x18))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x19))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.x20))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000002#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lext 0, LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x000000000000000d#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x10)) (LOperand.reg (Reg.x12)))
  62, LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn (Op.set (Reg.x10) (Expr.imm 0x000000007801831c#64)), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0xfffffffffffffccc#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x10)) (LOperand.imm 0)) 70, LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.load
    (Reg.x19)
    (Width.b1)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000070#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000040#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.sub)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lcond
  (LOperand.cmp "geu" (LOperand.reg (Reg.x8)) (LOperand.reg (Reg.x12)))
  27, LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x18))
      (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x0000000078004348#64)), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lcall
  0x0000000078004350#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0x00000000000000cc#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [12]), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lgoto 61, LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x19)) (LOperand.imm 0)) 43, LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.sub)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn
  (Op.set
    (Reg.x20)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x9))
      (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x000000007800436c#64)), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lcall
  0x0000000078004374#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0x00000000000000a8#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [12]), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.x10))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 40, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x000000007800538c#64)), LinstrR.Llabel (LabelKind.internal) 41, LinstrR.Lcall
  0x0000000078004394#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0xfffffffffffffdb8#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [32]), LinstrR.Llabel (LabelKind.internal) 42, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x20)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 43, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0xffffffffffffff81#64))), LinstrR.Llabel (LabelKind.internal) 44, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x10))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 45, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 46, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.and) (Expr.reg (Reg.x8)) (Expr.imm 0x000000000000003f#64))), LinstrR.Llabel (LabelKind.internal) 47, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000006#64))), LinstrR.Llabel (LabelKind.internal) 48, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 49, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x12)) (LOperand.imm 0)) 56, LinstrR.Llabel (LabelKind.internal) 50, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 51, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 52, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.x10))), LinstrR.Llabel (LabelKind.internal) 53, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 54, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x00000000780053c4#64)), LinstrR.Llabel (LabelKind.internal) 55, LinstrR.Lcall
  0x00000000780043cc#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0xfffffffffffffd80#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [32]), LinstrR.Llabel (LabelKind.internal) 56, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 57, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 58, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 59, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x00000000780043d8#64)), LinstrR.Llabel (LabelKind.internal) 60, LinstrR.Lcall
  0x00000000780043e0#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0x000000000000003c#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [12]), LinstrR.Llabel (LabelKind.internal) 61, LinstrR.Lopn
  (Op.store
    (Width.b1)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000070#64))
    (Expr.reg (Reg.x9))), LinstrR.Llabel (LabelKind.internal) 62, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 63, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64)))]

def f11_1 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 64, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 65, LinstrR.Lopn
  (Op.load
    (Reg.x18)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 66, LinstrR.Lopn
  (Op.load
    (Reg.x19)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 67, LinstrR.Lopn
  (Op.load
    (Reg.x20)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 68, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 69, LinstrR.Lret, LinstrR.Llabel (LabelKind.internal) 70, LinstrR.Lopn (Op.set (Reg.x10) (Expr.imm 0x0000000078000404#64)), LinstrR.Llabel (LabelKind.internal) 71, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x00000000000004ec#64))), LinstrR.Llabel (LabelKind.internal) 72, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm 0x000000007800e40c#64)), LinstrR.Llabel (LabelKind.internal) 73, LinstrR.Lcall
  0x0000000078004414#64
  (Target.indirect
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0x0000000000000058#64))
      (Expr.imm 0xfffffffffffffffe#64))
    [153])]

/-- The function "syscall_write", lifted. -/
def f11 : Lfundef (Op Reg) Reg :=
  { name := "syscall_write", addr := 2013283052, depth := 0,
    body := List.flatten [f11_0, f11_1] }

kernel_eq f11_head : (liftProg fns)[11]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f11.name, f11.addr, f11.depth)

kernel_eq f11_parts : (liftProg fns)[11]?.map (fun g => chunks chunk g.body) =
    some [f11_0, f11_1]

/-- **`f11` is the lift of the ELF's words.** -/
theorem f11_eq : (liftProg fns)[11]? = some f11 :=
  getElem?_eq_of_chunks f11_head f11_parts rfl

end

end Examples.Sp1Runtime.RiscV.Image
