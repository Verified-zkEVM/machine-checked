/-
  LeanVerifiers.ARM.Signatures.F10

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import LeanVerifiers.ARM.Signatures.Code

namespace LeanVerifiers.ARM.Signatures

open Lprog Lprog.ARM Tools.Program Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f10_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.sp)
    (Expr.bin (BinOp.sub) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000c0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x28))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x27))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000070#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000070#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x26))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x25))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000080#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000080#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x24))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x23))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000090#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000090#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x22))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x21))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000a0#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000a0#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x20))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x19))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000b0#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000b0#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000020#64))), LinstrR.Lopn (Op.load (Reg.x15) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.set
    (Reg.x27)
    (Expr.bin (BinOp.or) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000070#64))), LinstrR.Lopn (Op.load (Reg.x5) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x0))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000000#64))), LinstrR.Lopn (Op.load (Reg.x9) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000050#64))), LinstrR.Lopn (Op.load (Reg.x11) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x2)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x22)
    (Expr.bin (BinOp.or) (Expr.imm 0x0000000000000000#64) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000030#64))), LinstrR.Lopn (Op.load (Reg.x4) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000050#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.x12))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000080#64))), LinstrR.Lopn (Op.load (Reg.x19) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x3)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x11))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x9))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000030#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000030#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x11)) (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x30))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x10))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000060#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000060#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000010#64))), LinstrR.Lopn (Op.load (Reg.x11) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000060#64))), LinstrR.Lopn (Op.load (Reg.x1) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x7)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x4)) (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000090#64))), LinstrR.Lopn (Op.load (Reg.x25) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x21)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x2)) (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000040#64))), LinstrR.Lopn (Op.load (Reg.x12) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x6)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x9)) (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000058#64))
    (Expr.reg (Reg.x11))), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x13)) (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x1)) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x14))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x13))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000040#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000040#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x25)))), LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x12)) (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x00000000000000a0#64))), LinstrR.Lopn (Op.load (Reg.x23) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x18)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x00000000000000b0#64))), LinstrR.Lopn (Op.load (Reg.x16) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x20)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x11)) (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x6)) (Expr.reg (Reg.x15))))]

def f10_1 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 40, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x5)) (Expr.reg (Reg.x21)))), LinstrR.Llabel (LabelKind.internal) 41, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x13)) (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 42, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x0)) (Expr.imm 0x00000000000000c0#64))), LinstrR.Llabel (LabelKind.internal) 43, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x23)))), LinstrR.Llabel (LabelKind.internal) 44, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x9)) (Expr.reg (Reg.x18)))), LinstrR.Llabel (LabelKind.internal) 45, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 46, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x11)) (Expr.reg (Reg.x20)))), LinstrR.Llabel (LabelKind.internal) 47, LinstrR.Lopn
  (Op.set
    (Reg.x0)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x13)) (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 48, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.x5))), LinstrR.Llabel (LabelKind.internal) 49, LinstrR.Lopn
  (Op.set
    (Reg.x24)
    (Expr.bin (BinOp.or) (Expr.imm 0x0000000000000000#64) (Expr.reg (Reg.x2)))), LinstrR.Llabel (LabelKind.internal) 50, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x0))
      (Expr.bin
        (BinOp.or)
        (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x30)) (Expr.imm 0x000000000000003f#64))
        (Expr.bin
          (BinOp.shl)
          (Expr.reg (Reg.x30))
          (Expr.imm 0x0000000000000001#64))))), LinstrR.Llabel (LabelKind.internal) 51, LinstrR.Lopn
  (Op.set
    (Reg.x26)
    (Expr.bin (BinOp.or) (Expr.imm 0x0000000000000000#64) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 52, LinstrR.Lopn
  (Op.set
    (Reg.x3)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x30))
      (Expr.bin
        (BinOp.or)
        (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x15)) (Expr.imm 0x000000000000003f#64))
        (Expr.bin
          (BinOp.shl)
          (Expr.reg (Reg.x15))
          (Expr.imm 0x0000000000000001#64))))), LinstrR.Llabel (LabelKind.internal) 53, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x28))
      (Expr.bin
        (BinOp.or)
        (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x8)) (Expr.imm 0x000000000000003f#64))
        (Expr.bin (BinOp.shl) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000001#64))))), LinstrR.Llabel (LabelKind.internal) 54, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x8))
      (Expr.bin
        (BinOp.or)
        (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x0)) (Expr.imm 0x000000000000003f#64))
        (Expr.bin (BinOp.shl) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000001#64))))), LinstrR.Llabel (LabelKind.internal) 55, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000038#64))), LinstrR.Llabel (LabelKind.internal) 56, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x12))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x18))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000010#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 57, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x15))
      (Expr.bin
        (BinOp.or)
        (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x28)) (Expr.imm 0x000000000000003f#64))
        (Expr.bin
          (BinOp.shl)
          (Expr.reg (Reg.x28))
          (Expr.imm 0x0000000000000001#64))))), LinstrR.Llabel (LabelKind.internal) 58, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x1)) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 59, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000068#64))), LinstrR.Llabel (LabelKind.internal) 60, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x2)))), LinstrR.Llabel (LabelKind.internal) 61, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x4)) (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 62, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x25)) (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 63, LinstrR.Lopn
  (Op.set
    (Reg.x4)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000014#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x8)) (Expr.imm 0x000000000000002c#64)))), LinstrR.Llabel (LabelKind.internal) 64, LinstrR.Lopn
  (Op.set
    (Reg.x1)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x10)) (Expr.imm 0x000000000000002b#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000015#64)))), LinstrR.Llabel (LabelKind.internal) 65, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000040#64))), LinstrR.Llabel (LabelKind.internal) 66, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 67, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x14)) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 68, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000015#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x9)) (Expr.imm 0x000000000000002b#64)))), LinstrR.Llabel (LabelKind.internal) 69, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x6)) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 70, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000032#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x11)) (Expr.imm 0x000000000000000e#64)))), LinstrR.Llabel (LabelKind.internal) 71, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 72, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.reg (Reg.x2)))), LinstrR.Llabel (LabelKind.internal) 73, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x9)) (Expr.imm 0x000000000000002c#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000014#64)))), LinstrR.Llabel (LabelKind.internal) 74, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x16)) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 75, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000024#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x8)) (Expr.imm 0x000000000000001c#64)))), LinstrR.Llabel (LabelKind.internal) 76, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x19)) (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 77, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x13)) (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 78, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000003#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x9)) (Expr.imm 0x000000000000003d#64)))), LinstrR.Llabel (LabelKind.internal) 79, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 80, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000013#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x8)) (Expr.imm 0x000000000000002d#64)))), LinstrR.Llabel (LabelKind.internal) 81, LinstrR.Lopn
  (Op.set
    (Reg.x19)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x16)) (Expr.imm 0x000000000000003f#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x16)) (Expr.imm 0x0000000000000001#64)))), LinstrR.Llabel (LabelKind.internal) 82, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000048#64))), LinstrR.Llabel (LabelKind.internal) 83, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000027#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000019#64)))), LinstrR.Llabel (LabelKind.internal) 84, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000050#64))), LinstrR.Lopn (Op.load (Reg.x9) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x7)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 85, LinstrR.Lopn
  (Op.set
    (Reg.x0)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x21)) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 86, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 87, LinstrR.Lopn
  (Op.set
    (Reg.x21)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000038#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000008#64)))), LinstrR.Llabel (LabelKind.internal) 88, LinstrR.Lopn
  (Op.set
    (Reg.x0)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x22)) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 89, LinstrR.Lopn
  (Op.set
    (Reg.x25)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x8)) (Expr.imm 0x000000000000003a#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000006#64)))), LinstrR.Llabel (LabelKind.internal) 90, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x23)) (Expr.reg (Reg.x2)))), LinstrR.Llabel (LabelKind.internal) 91, LinstrR.Lopn
  (Op.set
    (Reg.x23)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x26)) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 92, LinstrR.Lopn
  (Op.set
    (Reg.x3)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 93, LinstrR.Lopn
  (Op.load
    (Reg.x7)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 94, LinstrR.Lopn
  (Op.set
    (Reg.x22)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x9)) (Expr.reg (Reg.x2)))), LinstrR.Llabel (LabelKind.internal) 95, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x8)) (Expr.imm 0x000000000000002e#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000012#64)))), LinstrR.Llabel (LabelKind.internal) 96, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x0)) (Expr.imm 0x0000000000000025#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x0)) (Expr.imm 0x000000000000001b#64)))), LinstrR.Llabel (LabelKind.internal) 97, LinstrR.Lopn
  (Op.set
    (Reg.x0)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x22)) (Expr.imm 0x000000000000001c#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x22)) (Expr.imm 0x0000000000000024#64)))), LinstrR.Llabel (LabelKind.internal) 98, LinstrR.Lopn
  (Op.set
    (Reg.x22)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x24)) (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 99, LinstrR.Lopn
  (Op.set
    (Reg.x24)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x20)) (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 100, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x5)))), LinstrR.Llabel (LabelKind.internal) 101]

def f10_2 : Lcmd (Op Reg) Reg :=
  [LinstrR.Lopn
  (Op.load
    (Reg.x7)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 102, LinstrR.Lopn
  (Op.set
    (Reg.x26)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x22)) (Expr.imm 0x0000000000000036#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x22)) (Expr.imm 0x000000000000000a#64)))), LinstrR.Llabel (LabelKind.internal) 103, LinstrR.Lopn
  (Op.set
    (Reg.x22)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x23)) (Expr.imm 0x0000000000000031#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x23)) (Expr.imm 0x000000000000000f#64)))), LinstrR.Llabel (LabelKind.internal) 104, LinstrR.Lopn
  (Op.set
    (Reg.x23)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x24)) (Expr.imm 0x0000000000000008#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x24)) (Expr.imm 0x0000000000000038#64)))), LinstrR.Llabel (LabelKind.internal) 105, LinstrR.Lopn
  (Op.set
    (Reg.x3)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x3)) (Expr.imm 0x0000000000000002#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x3)) (Expr.imm 0x000000000000003e#64)))), LinstrR.Llabel (LabelKind.internal) 106, LinstrR.Lopn
  (Op.set
    (Reg.x24)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x5)) (Expr.imm 0x0000000000000009#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x5)) (Expr.imm 0x0000000000000037#64)))), LinstrR.Llabel (LabelKind.internal) 107, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 108, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x1))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x17))))), LinstrR.Llabel (LabelKind.internal) 109, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x11)) (Expr.imm 0x000000000000003d#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000003#64)))), LinstrR.Llabel (LabelKind.internal) 110, LinstrR.Lopn
  (Op.set
    (Reg.x20)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x15)) (Expr.imm 0x0000000000000019#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x15)) (Expr.imm 0x0000000000000027#64)))), LinstrR.Llabel (LabelKind.internal) 111, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 112, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x5)) (Expr.reg (Reg.x4)))), LinstrR.Llabel (LabelKind.internal) 113, LinstrR.Lopn (Op.set (Reg.x5) (Expr.imm 0x0000000000200000#64)), LinstrR.Llabel (LabelKind.internal) 114, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x5)) (Expr.imm 0x00000000000002b0#64))), LinstrR.Llabel (LabelKind.internal) 115, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.x3))), LinstrR.Llabel (LabelKind.internal) 116, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x15)) (Expr.reg (Reg.x2)))), LinstrR.Llabel (LabelKind.internal) 117, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 118, LinstrR.Lopn
  (Op.load
    (Reg.x5)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x5)) (Expr.reg (Reg.x27)))), LinstrR.Llabel (LabelKind.internal) 119, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000017#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000029#64)))), LinstrR.Llabel (LabelKind.internal) 120, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x18))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x1))))), LinstrR.Llabel (LabelKind.internal) 121, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000068#64))
    (Expr.reg (Reg.x7))), LinstrR.Llabel (LabelKind.internal) 122, LinstrR.Lopn
  (Op.set
    (Reg.x3)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x15)) (Expr.reg (Reg.x30)))), LinstrR.Llabel (LabelKind.internal) 123, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x2)) (Expr.reg (Reg.x17)))), LinstrR.Llabel (LabelKind.internal) 124, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x17))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x4))))), LinstrR.Llabel (LabelKind.internal) 125, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin
      (BinOp.or)
      (Expr.bin (BinOp.lshr) (Expr.reg (Reg.x3)) (Expr.imm 0x000000000000003e#64))
      (Expr.bin (BinOp.shl) (Expr.reg (Reg.x3)) (Expr.imm 0x0000000000000002#64)))), LinstrR.Llabel (LabelKind.internal) 126, LinstrR.Lopn
  (Op.set
    (Reg.x3)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x12))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x18))))), LinstrR.Llabel (LabelKind.internal) 127, LinstrR.Lopn
  (Op.set
    (Reg.x27)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x27)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 128, LinstrR.Lopn
  (Op.set
    (Reg.x3)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x3)) (Expr.reg (Reg.x1)))), LinstrR.Llabel (LabelKind.internal) 129, LinstrR.Lopn
  (Op.set
    (Reg.x1)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x4))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x12))))), LinstrR.Llabel (LabelKind.internal) 130, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x5)) (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 131, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x18)) (Expr.reg (Reg.x1)))), LinstrR.Llabel (LabelKind.internal) 132, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x17)) (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 133, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x11))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x10))))), LinstrR.Llabel (LabelKind.internal) 134, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x13))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x11))))), LinstrR.Llabel (LabelKind.internal) 135, LinstrR.Lopn
  (Op.set
    (Reg.x1)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x17)) (Expr.reg (Reg.x6)))), LinstrR.Llabel (LabelKind.internal) 136, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x14))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x13))))), LinstrR.Llabel (LabelKind.internal) 137, LinstrR.Lopn
  (Op.set
    (Reg.x4)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x18)) (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 138, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x10))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x6))))), LinstrR.Llabel (LabelKind.internal) 139, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x17)) (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 140, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x6))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x14))))), LinstrR.Llabel (LabelKind.internal) 141, LinstrR.Lopn
  (Op.set
    (Reg.x6)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x14)) (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 142, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x19))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x9))))), LinstrR.Llabel (LabelKind.internal) 143, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x11)) (Expr.reg (Reg.x13)))), LinstrR.Llabel (LabelKind.internal) 144, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x4)))), LinstrR.Llabel (LabelKind.internal) 145, LinstrR.Lopn
  (Op.set
    (Reg.x7)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x14)) (Expr.reg (Reg.x21)))), LinstrR.Llabel (LabelKind.internal) 146, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x21))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x16))))), LinstrR.Llabel (LabelKind.internal) 147, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x1))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x2))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000050#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000050#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 148, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x2)) (Expr.reg (Reg.x17)))), LinstrR.Llabel (LabelKind.internal) 149, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x14)) (Expr.reg (Reg.x25)))), LinstrR.Llabel (LabelKind.internal) 150, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x25))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x19))))), LinstrR.Llabel (LabelKind.internal) 151, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x5))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x3))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000038#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000038#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 152, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x5)) (Expr.reg (Reg.x1)))), LinstrR.Llabel (LabelKind.internal) 153, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x9))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x21))))), LinstrR.Llabel (LabelKind.internal) 154, LinstrR.Lopn
  (Op.set
    (Reg.x5)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x9)) (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 155, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x26))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x0))))), LinstrR.Llabel (LabelKind.internal) 156, LinstrR.Lopn
  (Op.set
    (Reg.x1)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x18)) (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 157, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x16))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x25))))), LinstrR.Llabel (LabelKind.internal) 158, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x9)) (Expr.reg (Reg.x8)))), LinstrR.Llabel (LabelKind.internal) 159, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x22))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x26))))), LinstrR.Llabel (LabelKind.internal) 160, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x16)) (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 161, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x23))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x22))))), LinstrR.Llabel (LabelKind.internal) 162]

def f10_3 : Lcmd (Op Reg) Reg :=
  [LinstrR.Lopn
  (Op.set
    (Reg.x19)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x9)) (Expr.reg (Reg.x0)))), LinstrR.Llabel (LabelKind.internal) 163, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x0))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x8))))), LinstrR.Llabel (LabelKind.internal) 164, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x8))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x23))))), LinstrR.Llabel (LabelKind.internal) 165, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000048#64))
    (Expr.reg (Reg.x17))), LinstrR.Llabel (LabelKind.internal) 166, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x3)) (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 167, LinstrR.Lopn
  (Op.set
    (Reg.x3)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x14)) (Expr.reg (Reg.x26)))), LinstrR.Llabel (LabelKind.internal) 168, LinstrR.Lopn
  (Op.set
    (Reg.x25)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x22)))), LinstrR.Llabel (LabelKind.internal) 169, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x16)) (Expr.reg (Reg.x18)))), LinstrR.Llabel (LabelKind.internal) 170, LinstrR.Lopn
  (Op.set
    (Reg.x21)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x23)) (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 171, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.reg (Reg.x8)))), LinstrR.Llabel (LabelKind.internal) 172, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x1)) (Expr.reg (Reg.x3)))), LinstrR.Llabel (LabelKind.internal) 173, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x13)) (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 174, LinstrR.Lopn
  (Op.set
    (Reg.x22)
    (Expr.bin (BinOp.or) (Expr.imm 0x0000000000000000#64) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 175, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x15)) (Expr.reg (Reg.x6)))), LinstrR.Llabel (LabelKind.internal) 176, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x5)) (Expr.reg (Reg.x21)))), LinstrR.Llabel (LabelKind.internal) 177, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 178, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x2)) (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 179, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x13)) (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 180, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x20))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x24))))), LinstrR.Llabel (LabelKind.internal) 181, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x11)) (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 182, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x7)) (Expr.reg (Reg.x25)))), LinstrR.Llabel (LabelKind.internal) 183, LinstrR.Lopn
  (Op.set
    (Reg.x23)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x14)) (Expr.reg (Reg.x15)))), LinstrR.Llabel (LabelKind.internal) 184, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x28))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x20))))), LinstrR.Llabel (LabelKind.internal) 185, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x18))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x16))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000028#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 186, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x17)) (Expr.reg (Reg.x11)))), LinstrR.Llabel (LabelKind.internal) 187, LinstrR.Lopn
  (Op.set
    (Reg.x17)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x30))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x28))))), LinstrR.Llabel (LabelKind.internal) 188, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x14)) (Expr.reg (Reg.x24)))), LinstrR.Llabel (LabelKind.internal) 189, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x24))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x15))))), LinstrR.Llabel (LabelKind.internal) 190, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin
      (BinOp.and)
      (Expr.reg (Reg.x15))
      (Expr.un (UnOp.not) (Expr.reg (Reg.x30))))), LinstrR.Llabel (LabelKind.internal) 191, LinstrR.Lopn
  (Op.set
    (Reg.x16)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x17)) (Expr.reg (Reg.x20)))), LinstrR.Llabel (LabelKind.internal) 192, LinstrR.Lopn
  (Op.set
    (Reg.x20)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x15)) (Expr.reg (Reg.x28)))), LinstrR.Llabel (LabelKind.internal) 193, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x30)) (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 194, LinstrR.Lopn
  (Op.set
    (Reg.x28)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x8)) (Expr.reg (Reg.x23)))), LinstrR.Llabel (LabelKind.internal) 195, LinstrR.Lopn
  (Op.set
    (Reg.x30)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x9)) (Expr.reg (Reg.x18)))), LinstrR.Llabel (LabelKind.internal) 196, LinstrR.Lopn
  (Op.set
    (Reg.t0)
    (Expr.bin (BinOp.sub) (Expr.reg (Reg.x27)) (Expr.imm 0x00000000000000c0#64))), LinstrR.Lopn
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
      (Expr.bin (BinOp.ult) (Expr.reg (Reg.x27)) (Expr.imm 0x00000000000000c0#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Lopn
  (Op.set
    (Reg.vf)
    (Expr.bin
      (BinOp.and)
      (Expr.bin
        (BinOp.lshr)
        (Expr.bin
          (BinOp.and)
          (Expr.bin (BinOp.xor) (Expr.reg (Reg.x27)) (Expr.imm 0x00000000000000c0#64))
          (Expr.bin (BinOp.xor) (Expr.reg (Reg.x27)) (Expr.reg (Reg.t0))))
        (Expr.imm 0x000000000000003f#64))
      (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 197, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x10)) (Expr.reg (Reg.x16)))), LinstrR.Llabel (LabelKind.internal) 198, LinstrR.Lopn
  (Op.set
    (Reg.x15)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x11)) (Expr.reg (Reg.x20)))), LinstrR.Llabel (LabelKind.internal) 199, LinstrR.Lopn
  (Op.set
    (Reg.x0)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x13)) (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 200, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.zf)) (LOperand.imm 0)) 48, LinstrR.Llabel (LabelKind.internal) 201, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 202, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000038#64))), LinstrR.Llabel (LabelKind.internal) 203, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000060#64))), LinstrR.Lopn (Op.load (Reg.x30) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 204, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000070#64))), LinstrR.Lopn (Op.load (Reg.x28) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x27)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 205, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x10))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x9))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000000#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000000#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 206, LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000058#64))), LinstrR.Llabel (LabelKind.internal) 207, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000040#64))), LinstrR.Llabel (LabelKind.internal) 208, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x19))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x3))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000080#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000080#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 209, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x10))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x9))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000010#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 210, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000048#64))), LinstrR.Lopn (Op.load (Reg.x9) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 211, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x25))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x21))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000090#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000090#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 212, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000080#64))), LinstrR.Lopn (Op.load (Reg.x26) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x25)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64)))]

def f10_4 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 213, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x23))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x18))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x00000000000000a0#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x00000000000000a0#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 214, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000090#64))), LinstrR.Lopn (Op.load (Reg.x24) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x23)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 215, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x22))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x10))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000020#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 216, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000a0#64))), LinstrR.Lopn (Op.load (Reg.x22) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x21)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 217, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x4))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x9))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000030#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000030#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 218, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x0000000000000028#64))), LinstrR.Lopn (Op.load (Reg.x9) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x10)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 219, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x16))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x20))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x00000000000000b0#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x00000000000000b0#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 220, LinstrR.Lopn
  (Op.set
    (Reg.t2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000b0#64))), LinstrR.Lopn (Op.load (Reg.x20) (Width.b8) false (Expr.reg (Reg.t2))), LinstrR.Lopn
  (Op.load
    (Reg.x19)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.t2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 221, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x12))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x6))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000040#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000040#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 222, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x10))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x2))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000050#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000050#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 223, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x1))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x7))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000060#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000060#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 224, LinstrR.Lopn (Op.set (Reg.t0) (Expr.reg (Reg.x5))), LinstrR.Lopn (Op.set (Reg.t1) (Expr.reg (Reg.x9))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000070#64))
    (Expr.reg (Reg.t0))), LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin
      (BinOp.add)
      (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000070#64))
      (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.t1))), LinstrR.Llabel (LabelKind.internal) 225, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x00000000000000c0#64))
    (Expr.reg (Reg.x14))), LinstrR.Llabel (LabelKind.internal) 226, LinstrR.Lopn
  (Op.set
    (Reg.sp)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.sp)) (Expr.imm 0x00000000000000c0#64))), LinstrR.Llabel (LabelKind.internal) 227, LinstrR.Lret, LinstrR.Labort]

/-- The function "_RNvCsndc0WgnAaH_9keccak2568keccak_f", lifted. -/
def f10 : Lfundef (Op Reg) Reg :=
  { name := "_RNvCsndc0WgnAaH_9keccak2568keccak_f", addr := 2176616, depth := 0,
    body := List.flatten [f10_0, f10_1, f10_2, f10_3, f10_4] }

theorem f10_head : program.lifted[10]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f10.name, f10.addr, f10.depth) := by
  decide +kernel

theorem f10_parts : program.lifted[10]?.map (fun g => chunks chunk g.body) =
    some [f10_0, f10_1, f10_2, f10_3, f10_4] := by
  decide +kernel

/-- **`f10` is the lift of the ELF's code.** -/
theorem f10_eq : program.lifted[10]? = some f10 :=
  getElem?_eq_of_chunks f10_head f10_parts rfl

end

end LeanVerifiers.ARM.Signatures
