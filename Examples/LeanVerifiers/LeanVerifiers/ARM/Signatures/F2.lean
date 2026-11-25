/-
  LeanVerifiers.ARM.Signatures.F2

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import LeanVerifiers.ARM.Signatures.Code

namespace LeanVerifiers.ARM.Signatures

open Lprog Lprog.ARM Tools.Program Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f2_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.or)
      (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x1)))
      (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x0))))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.or)
      (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x8)))
      (Expr.un (UnOp.zext (Width.b4)) (Expr.reg (Reg.x2))))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.set
    (Reg.t0)
    (Expr.bin (BinOp.and) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000007#64))), LinstrR.Lopn
  (Op.set
    (Reg.nf)
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.t0)) (Expr.imm 0x000000000000003f#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.zf)
    (Expr.bin (BinOp.ult) (Expr.reg (Reg.t0)) (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn (Op.set (Reg.cf) (Expr.imm 0x0000000000000000#64)), LinstrR.Lopn (Op.set (Reg.vf) (Expr.imm 0x0000000000000000#64)), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lcond (LOperand.cmp "ne" (LOperand.reg (Reg.zf)) (LOperand.imm 0)) 11, LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x2)) (LOperand.imm 0)) 18, LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.or) (Expr.imm 0x0000000000000000#64) (Expr.reg (Reg.x0)))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn (Op.load (Reg.x9) (Width.b1) false (Expr.reg (Reg.x1))), LinstrR.Lopn
  (Op.set
    (Reg.x1)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.t0)
    (Expr.bin (BinOp.sub) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.nf)
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.t0)) (Expr.imm 0x000000000000003f#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.zf)
    (Expr.bin (BinOp.ult) (Expr.reg (Reg.t0)) (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.cf)
    (Expr.bin
      (BinOp.xor)
      (Expr.bin (BinOp.ult) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000001#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.vf)
    (Expr.bin
      (BinOp.and)
      (Expr.bin
        (BinOp.lshr)
        (Expr.bin
          (BinOp.and)
          (Expr.bin (BinOp.xor) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000001#64))
          (Expr.bin (BinOp.xor) (Expr.reg (Reg.x2)) (Expr.reg (Reg.t0))))
        (Expr.imm 0x000000000000003f#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn (Op.set (Reg.x2) (Expr.reg (Reg.t0))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.store (Width.b1) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x9))), LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.zf)) (LOperand.imm 0)) 6, LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lgoto 18, LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x2)) (LOperand.imm 0)) 18, LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.or) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.reg (Reg.x8)))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.reg (Reg.x8)))
    (Expr.reg (Reg.x9))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.set
    (Reg.t0)
    (Expr.bin (BinOp.sub) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x2)))), LinstrR.Lopn
  (Op.set
    (Reg.nf)
    (Expr.bin
      (BinOp.and)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.t0)) (Expr.imm 0x000000000000003f#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.zf)
    (Expr.bin (BinOp.ult) (Expr.reg (Reg.t0)) (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.cf)
    (Expr.bin
      (BinOp.xor)
      (Expr.bin (BinOp.ult) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x2)))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.vf)
    (Expr.bin
      (BinOp.and)
      (Expr.bin
        (BinOp.lshr)
        (Expr.bin
          (BinOp.and)
          (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x2)))
          (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.t0))))
        (Expr.imm 0x000000000000003f#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.cf)) (LOperand.imm 0)) 13, LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lret, LinstrR.Labort]

/-- The function "memcpy", lifted. -/
def f2 : Lfundef (Op Reg) Reg :=
  { name := "memcpy", addr := 2164312, depth := 0,
    body := List.flatten [f2_0] }

theorem f2_head : program.lifted[2]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f2.name, f2.addr, f2.depth) := by
  decide +kernel

theorem f2_parts : program.lifted[2]?.map (fun g => chunks chunk g.body) =
    some [f2_0] := by
  decide +kernel

/-- **`f2` is the lift of the ELF's code.** -/
theorem f2_eq : program.lifted[2]? = some f2 :=
  getElem?_eq_of_chunks f2_head f2_parts rfl

end

end LeanVerifiers.ARM.Signatures
