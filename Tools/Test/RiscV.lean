/-
  Tools.Test.RiscV

  Tests of the RISC-V decoder (`decodeWord`) and the lift of whole programs (`Whole.liftI`),
  run when the module is built: each instruction from its bytes (as `llvm-mc --triple=riscv64
  -mattr=+m --show-encoding` gives them), decoded, lifted and run (`Tools.Test.Run`), against
  what the RISC-V unprivileged ISA manual says it does (RV64IM).

  The expected values are worked out by hand from the manual. The nine 32-bit operations
  riscv-zkvm's decoder lacks (`Lprog/Decode.lean`) are stated by the decompiler itself, and are
  tested here hardest.
-/

import MachineChecked.RiscV.Lift.Whole
import Tools.Test.Run

namespace Tools.Test.RiscV

open RiscvZkvm.Rv64 Lprog MachineChecked.RiscV.Lift
open Lprog.Linked (At Cx)

/-- Where the instructions of the tests are. -/
def at0 : BitVec 64 := 0x10000

/-- The word of four bytes, little-endian. -/
def wordOf (bytes : List Nat) : BitVec 32 :=
  BitVec.ofNat 32 (bytes.foldr (fun b acc => acc * 256 + b) 0)

/-- The instruction of `bytes` at `a`. -/
def instrAt (a : BitVec 64) (bytes : List Nat) : At Decoded :=
  { addr := a, size := 4, instr := decodeWord (wordOf bytes) }

/-- The instruction of `bytes` at `at0` after `prev`, lifted in `c`, run from `init` and `m`. -/
def execCx (c : Cx) (bytes : List Nat) (init : List (Reg × BitVec 64)) (m : Mem := {})
    (prev : Option (At Decoded) := none) : End Reg :=
  if bytes.length ≠ 4 then .wrong "not a word" else
  run (Whole.liftI c prev (instrAt at0 bytes)) init m

/-- The same, where the program has functions at `entries` and computed jumps may go to
    `cands` (`Tools.Test.Run.cx`). -/
def exec (bytes : List Nat) (init : List (Reg × BitVec 64)) (m : Mem := {})
    (prev : Option (At Decoded) := none) (entries : List (BitVec 64) := [])
    (cands : List (BitVec 64) := []) : End Reg :=
  execCx (cx at0 4 entries cands) bytes init m prev

/-- Straight-line instructions one after another from `at0`, each lifted after the one before
    it, and run as one piece of code. -/
def seq (code : List (List Nat)) (init : List (Reg × BitVec 64)) (m : Mem := {})
    (entries : List (BitVec 64) := []) : End Reg :=
  let is := code.zipIdx.map fun (b, k) => instrAt (at0 + BitVec.ofNat 64 (4 * k)) b
  let c := cx at0 (4 * code.length) entries
  run ((is.zip (none :: is.map some)).flatMap fun (i, p) => Whole.liftI c p i) init m

/-- A call of `ret` to an indirect target that is `tgt`, among the functions `fns`. -/
def callsInd (e : End Reg) (ret tgt : BitVec 64) (fns : List Nat) : Bool :=
  match e with
  | .leaves (.Lcall r (.indirect x fs)) regs _ => r == ret && x.eval regs == tgt && fs == fns
  | _ => false

/-- A tail call to an indirect target that is `tgt`, among the functions `fns`. -/
def tailsInd (e : End Reg) (tgt : BitVec 64) (fns : List Nat) : Bool :=
  match e with
  | .leaves (.Ltail (.indirect x fs)) regs _ => x.eval regs == tgt && fs == fns
  | _ => false

/-- The instruction a run leaves the function by. -/
def leavesBy (e : End Reg) (i : LinstrR (Op Reg) Reg) : Bool :=
  match e with
  | .leaves j _ _ => j == i
  | _ => false

/-- The eight bytes at `a` after a run that reaches the next instruction. -/
def memAfter (e : End Reg) (a : BitVec 64) : Option (BitVec 64) :=
  match e with
  | .next _ m => some (m.read .b8 a)
  | _ => none

def max64 : BitVec 64 := -1
def min64 : BitVec 64 := 0x8000000000000000

-- The encodings, from llvm-mc (`a0` is `x10`, `a1` `x11`, `a2` `x12`).
def ADD := [0x33, 0x85, 0xc5, 0x00]      -- add a0, a1, a2
def SUB := [0x33, 0x85, 0xc5, 0x40]      -- sub a0, a1, a2
def SLT := [0x33, 0xa5, 0xc5, 0x00]      -- slt a0, a1, a2
def SLTU := [0x33, 0xb5, 0xc5, 0x00]     -- sltu a0, a1, a2
def SLL := [0x33, 0x95, 0xc5, 0x00]      -- sll a0, a1, a2
def SRL := [0x33, 0xd5, 0xc5, 0x00]      -- srl a0, a1, a2
def SRA := [0x33, 0xd5, 0xc5, 0x40]      -- sra a0, a1, a2
def AND := [0x33, 0xf5, 0xc5, 0x00]      -- and a0, a1, a2
def OR := [0x33, 0xe5, 0xc5, 0x00]       -- or a0, a1, a2
def XOR := [0x33, 0xc5, 0xc5, 0x00]      -- xor a0, a1, a2
def ADDW := [0x3b, 0x85, 0xc5, 0x00]     -- addw a0, a1, a2
def SUBW := [0x3b, 0x85, 0xc5, 0x40]     -- subw a0, a1, a2
def SLLW := [0x3b, 0x95, 0xc5, 0x00]     -- sllw a0, a1, a2
def SRLW := [0x3b, 0xd5, 0xc5, 0x00]     -- srlw a0, a1, a2
def SRAW := [0x3b, 0xd5, 0xc5, 0x40]     -- sraw a0, a1, a2
def MULW := [0x3b, 0x85, 0xc5, 0x02]     -- mulw a0, a1, a2
def DIVW := [0x3b, 0xc5, 0xc5, 0x02]     -- divw a0, a1, a2
def DIVUW := [0x3b, 0xd5, 0xc5, 0x02]    -- divuw a0, a1, a2
def REMW := [0x3b, 0xe5, 0xc5, 0x02]     -- remw a0, a1, a2
def REMUW := [0x3b, 0xf5, 0xc5, 0x02]    -- remuw a0, a1, a2
def MUL := [0x33, 0x85, 0xc5, 0x02]      -- mul a0, a1, a2
def MULH := [0x33, 0x95, 0xc5, 0x02]     -- mulh a0, a1, a2
def MULHSU := [0x33, 0xa5, 0xc5, 0x02]   -- mulhsu a0, a1, a2
def MULHU := [0x33, 0xb5, 0xc5, 0x02]    -- mulhu a0, a1, a2
def DIV := [0x33, 0xc5, 0xc5, 0x02]      -- div a0, a1, a2
def DIVU := [0x33, 0xd5, 0xc5, 0x02]     -- divu a0, a1, a2
def REM := [0x33, 0xe5, 0xc5, 0x02]      -- rem a0, a1, a2
def REMU := [0x33, 0xf5, 0xc5, 0x02]     -- remu a0, a1, a2

/-! ## add, sub -/

-- add: 1 + 2
#guard (exec ADD [(.x11, 1), (.x12, 2)]).has [(.x10, 3), (.x11, 1), (.x12, 2)]
-- add wraps at 64 bits
#guard (exec ADD [(.x11, max64), (.x12, 1)]).has [(.x10, 0)]
-- add: the greatest signed number plus one is the least
#guard (exec ADD [(.x11, 0x7fffffffffffffff), (.x12, 1)]).has [(.x10, min64)]
-- sub: 1 - 2 is -1
#guard (exec SUB [(.x11, 1), (.x12, 2)]).has [(.x10, max64)]
-- sub: 0 - INT_MIN is INT_MIN
#guard (exec SUB [(.x11, 0), (.x12, min64)]).has [(.x10, min64)]

/-! ## slt, sltu -/

-- slt: -1 < 1 signed
#guard (exec SLT [(.x11, -1), (.x12, 1)]).has [(.x10, 1)]
-- slt: 1 < -1 is false signed
#guard (exec SLT [(.x11, 1), (.x12, -1)]).has [(.x10, 0)]
-- slt: equal is not less
#guard (exec SLT [(.x11, 5), (.x12, 5)]).has [(.x10, 0)]
-- slt: INT_MIN < INT_MAX
#guard (exec SLT [(.x11, min64), (.x12, 0x7fffffffffffffff)]).has [(.x10, 1)]
-- sltu: all ones is the greatest unsigned number
#guard (exec SLTU [(.x11, -1), (.x12, 1)]).has [(.x10, 0)]
-- sltu: 1 < all ones
#guard (exec SLTU [(.x11, 1), (.x12, -1)]).has [(.x10, 1)]
-- sltu: 0 < 0 is false
#guard (exec SLTU [(.x11, 0), (.x12, 0)]).has [(.x10, 0)]

/-! ## and, or, xor -/

-- and
#guard (exec AND [(.x11, 0xf0f0), (.x12, 0xff00)]).has [(.x10, 0xf000)]
-- or
#guard (exec OR [(.x11, 0xf0f0), (.x12, 0xff00)]).has [(.x10, 0xfff0)]
-- xor
#guard (exec XOR [(.x11, 0xf0f0), (.x12, 0xff00)]).has [(.x10, 0x0ff0)]

/-! ## sll, srl, sra: the amount is the low six bits of rs2 -/

-- sll by 63
#guard (exec SLL [(.x11, 1), (.x12, 63)]).has [(.x10, min64)]
-- sll by 64 is by 0
#guard (exec SLL [(.x11, 1), (.x12, 64)]).has [(.x10, 1)]
-- sll by 65 is by 1
#guard (exec SLL [(.x11, 1), (.x12, 65)]).has [(.x10, 2)]
-- srl by 63, logical
#guard (exec SRL [(.x11, min64), (.x12, 63)]).has [(.x10, 1)]
-- srl by 127 is by 63
#guard (exec SRL [(.x11, min64), (.x12, 127)]).has [(.x10, 1)]
-- srl by 64 is by 0
#guard (exec SRL [(.x11, min64), (.x12, 64)]).has [(.x10, min64)]
-- sra by 63 fills with the sign
#guard (exec SRA [(.x11, min64), (.x12, 63)]).has [(.x10, max64)]
-- sra by 1
#guard (exec SRA [(.x11, min64), (.x12, 1)]).has [(.x10, 0xc000000000000000)]
-- sra by 65 is by 1
#guard (exec SRA [(.x11, min64), (.x12, 65)]).has [(.x10, 0xc000000000000000)]
-- sra of a positive number by all ones (63)
#guard (exec SRA [(.x11, 0x7fffffffffffffff), (.x12, -1)]).has [(.x10, 0)]

/-! ## Immediates: sign-extended 12 bits -/

-- addi a0, a1, -1
#guard (exec [0x13, 0x85, 0xf5, 0xff] [(.x11, 0)]).has [(.x10, max64)]
-- addi a0, a1, 2047
#guard (exec [0x13, 0x85, 0xf5, 0x7f] [(.x11, 1)]).has [(.x10, 2048)]
-- addi a0, a1, -2048
#guard (exec [0x13, 0x85, 0x05, 0x80] [(.x11, 0)]).has [(.x10, 0xfffffffffffff800)]
-- slti a0, a1, -1: -2 < -1
#guard (exec [0x13, 0xa5, 0xf5, 0xff] [(.x11, -2)]).has [(.x10, 1)]
-- slti a0, a1, -1: 0 < -1 is false
#guard (exec [0x13, 0xa5, 0xf5, 0xff] [(.x11, 0)]).has [(.x10, 0)]
-- sltiu a0, a1, -1: the immediate is sign-extended, then compared unsigned (all ones)
#guard (exec [0x13, 0xb5, 0xf5, 0xff] [(.x11, 0)]).has [(.x10, 1)]
-- sltiu a0, a1, -1: all ones is not below all ones
#guard (exec [0x13, 0xb5, 0xf5, 0xff] [(.x11, -1)]).has [(.x10, 0)]
-- xori a0, a1, -1 (not)
#guard (exec [0x13, 0xc5, 0xf5, 0xff] [(.x11, 0x1234)]).has [(.x10, 0xffffffffffffedcb)]
-- andi a0, a1, -16
#guard (exec [0x13, 0xf5, 0x05, 0xff] [(.x11, -1)]).has [(.x10, 0xfffffffffffffff0)]
-- andi a0, a1, -16, on a positive number
#guard (exec [0x13, 0xf5, 0x05, 0xff] [(.x11, 0x1234567f)]).has [(.x10, 0x12345670)]
-- ori a0, a1, 2047
#guard (exec [0x13, 0xe5, 0xf5, 0x7f] [(.x11, 0x800)]).has [(.x10, 0xfff)]
-- slli a0, a1, 63
#guard (exec [0x13, 0x95, 0xf5, 0x03] [(.x11, 3)]).has [(.x10, min64)]
-- slli a0, a1, 32: a six-bit amount
#guard (exec [0x13, 0x95, 0x05, 0x02] [(.x11, 0xffffffff)]).has [(.x10, 0xffffffff00000000)]
-- srli a0, a1, 63
#guard (exec [0x13, 0xd5, 0xf5, 0x03] [(.x11, -1)]).has [(.x10, 1)]
-- srai a0, a1, 63
#guard (exec [0x13, 0xd5, 0xf5, 0x43] [(.x11, min64)]).has [(.x10, max64)]
-- srai a0, a1, 1, of a negative number
#guard (exec [0x13, 0xd5, 0x15, 0x40] [(.x11, -4)]).has [(.x10, -2)]

/-! ## lui, auipc -/

-- lui a0, 0x12345
#guard (exec [0x37, 0x55, 0x34, 0x12] []).has [(.x10, 0x12345000)]
-- lui a0, 0x80000: the 32-bit result is sign-extended
#guard (exec [0x37, 0x05, 0x00, 0x80] []).has [(.x10, 0xffffffff80000000)]
-- lui a0, 0xfffff
#guard (exec [0x37, 0xf5, 0xff, 0xff] []).has [(.x10, 0xfffffffffffff000)]
-- lui a0, 0x7ffff
#guard (exec [0x37, 0xf5, 0xff, 0x7f] []).has [(.x10, 0x7ffff000)]
-- auipc a0, 0: the instruction's own address
#guard (exec [0x17, 0x05, 0x00, 0x00] []).has [(.x10, 0x10000)]
-- auipc a0, 1
#guard (exec [0x17, 0x15, 0x00, 0x00] []).has [(.x10, 0x11000)]
-- auipc a0, 0xfffff: minus 0x1000
#guard (exec [0x17, 0xf5, 0xff, 0xff] []).has [(.x10, 0xf000)]
-- auipc a0, 0x80000: minus 2^31
#guard (exec [0x17, 0x05, 0x00, 0x80] []).has [(.x10, 0xffffffff80010000)]
-- auipc a0, 1 at another address
#guard (execCx (cx 0x10000 4) [0x17, 0x15, 0x00, 0x00] []).has [(.x10, 0x11000)] &&
  (run (Whole.liftI (cx 0x20000 4) none (instrAt 0x20000 [0x17, 0x15, 0x00, 0x00])) []).has
    [(.x10, 0x21000)]

/-! ## The 32-bit operations: each result is the low 32 bits, sign-extended -/

-- addw: 0x7fffffff + 1 is negative
#guard (exec ADDW [(.x11, 0x7fffffff), (.x12, 1)]).has [(.x10, 0xffffffff80000000)]
-- addw: the upper halves of the operands are ignored
#guard (exec ADDW [(.x11, 0x1234567800000005), (.x12, 0xabcdef0000000003)]).has [(.x10, 8)]
-- addw: a carry out of bit 31 is lost
#guard (exec ADDW [(.x11, 0x1ffffffff), (.x12, 1)]).has [(.x10, 0)]
-- addw: -1 + -1
#guard (exec ADDW [(.x11, 0xffffffff), (.x12, 0xffffffff)]).has [(.x10, -2)]
-- subw: 0 - 1
#guard (exec SUBW [(.x11, 0), (.x12, 1)]).has [(.x10, max64)]
-- subw: 0x80000000 - 1 is positive
#guard (exec SUBW [(.x11, 0x80000000), (.x12, 1)]).has [(.x10, 0x7fffffff)]
-- subw: only the low halves
#guard (exec SUBW [(.x11, 0x100000000), (.x12, 0)]).has [(.x10, 0)]
-- sllw by 31: into the sign bit
#guard (exec SLLW [(.x11, 1), (.x12, 31)]).has [(.x10, 0xffffffff80000000)]
-- sllw by 32 is by 0 (five bits of the amount)
#guard (exec SLLW [(.x11, 1), (.x12, 32)]).has [(.x10, 1)]
-- sllw by 33 is by 1
#guard (exec SLLW [(.x11, 1), (.x12, 33)]).has [(.x10, 2)]
-- sllw by 0: the upper half of rs1 is dropped
#guard (exec SLLW [(.x11, 0x100000001), (.x12, 0)]).has [(.x10, 1)]
-- sllw: bits shifted past bit 31 are lost
#guard (exec SLLW [(.x11, 0x3), (.x12, 31)]).has [(.x10, 0xffffffff80000000)]
-- srlw by 31: the upper half of rs1 is not shifted in
#guard (exec SRLW [(.x11, 0xffffffff80000000), (.x12, 31)]).has [(.x10, 1)]
-- srlw by 0 sign-extends bit 31
#guard (exec SRLW [(.x11, 0x80000000), (.x12, 0)]).has [(.x10, 0xffffffff80000000)]
-- srlw by 32 is by 0
#guard (exec SRLW [(.x11, 0x80000000), (.x12, 32)]).has [(.x10, 0xffffffff80000000)]
-- srlw by 1 is logical
#guard (exec SRLW [(.x11, 0x80000000), (.x12, 1)]).has [(.x10, 0x40000000)]
-- srlw: ones above bit 31 are not shifted in
#guard (exec SRLW [(.x11, 0xffffffff00000000), (.x12, 4)]).has [(.x10, 0)]
-- sraw by 31 of bit 31 set: all ones
#guard (exec SRAW [(.x11, 0x80000000), (.x12, 31)]).has [(.x10, max64)]
-- sraw by 4: bit 31 is the sign
#guard (exec SRAW [(.x11, 0x80000000), (.x12, 4)]).has [(.x10, 0xfffffffff8000000)]
-- sraw by 36 is by 4
#guard (exec SRAW [(.x11, 0x80000000), (.x12, 36)]).has [(.x10, 0xfffffffff8000000)]
-- sraw by 0 of a positive word
#guard (exec SRAW [(.x11, 0x7fffffff), (.x12, 0)]).has [(.x10, 0x7fffffff)]
-- sraw: the upper half of rs1 is not the sign
#guard (exec SRAW [(.x11, 0xffffffff00000010), (.x12, 4)]).has [(.x10, 1)]
-- sraw: a positive word with ones above it stays positive
#guard (exec SRAW [(.x11, 0xffffffff7fffffff), (.x12, 31)]).has [(.x10, 0)]
-- addiw a0, a1, -1 of 0
#guard (exec [0x1b, 0x85, 0xf5, 0xff] [(.x11, 0)]).has [(.x10, max64)]
-- addiw a0, a1, -1 of 2^32: the low half is 0, so -1
#guard (exec [0x1b, 0x85, 0xf5, 0xff] [(.x11, 0x100000000)]).has [(.x10, max64)]
-- addiw a0, a1, 1 of 0x7fffffff overflows to negative
#guard (exec [0x1b, 0x85, 0x15, 0x00] [(.x11, 0x7fffffff)]).has [(.x10, 0xffffffff80000000)]
-- addiw a0, a1, 1 of all ones
#guard (exec [0x1b, 0x85, 0x15, 0x00] [(.x11, -1)]).has [(.x10, 0)]
-- slliw a0, a1, 31
#guard (exec [0x1b, 0x95, 0xf5, 0x01] [(.x11, 1)]).has [(.x10, 0xffffffff80000000)]
-- slliw a0, a1, 31: bit 1 shifted out of the word
#guard (exec [0x1b, 0x95, 0xf5, 0x01] [(.x11, 2)]).has [(.x10, 0)]
-- slliw a0, a1, 0: sign-extends the low word
#guard (exec [0x1b, 0x95, 0x05, 0x00] [(.x11, 0x80000000)]).has [(.x10, 0xffffffff80000000)]
-- slliw a0, a1, 0: drops the upper half
#guard (exec [0x1b, 0x95, 0x05, 0x00] [(.x11, 0x17fffffff)]).has [(.x10, 0x7fffffff)]
-- srliw a0, a1, 31
#guard (exec [0x1b, 0xd5, 0xf5, 0x01] [(.x11, 0xffffffff)]).has [(.x10, 1)]
-- srliw a0, a1, 31: the upper half is not shifted in
#guard (exec [0x1b, 0xd5, 0xf5, 0x01] [(.x11, 0x100000000)]).has [(.x10, 0)]
-- srliw a0, a1, 0 sign-extends bit 31
#guard (exec [0x1b, 0xd5, 0x05, 0x00] [(.x11, 0x80000000)]).has [(.x10, 0xffffffff80000000)]
-- sraiw a0, a1, 31
#guard (exec [0x1b, 0xd5, 0xf5, 0x41] [(.x11, 0x80000000)]).has [(.x10, max64)]
-- sraiw a0, a1, 31 of a positive word
#guard (exec [0x1b, 0xd5, 0xf5, 0x41] [(.x11, 0x7fffffff)]).has [(.x10, 0)]
-- sraiw a0, a1, 4
#guard (exec [0x1b, 0xd5, 0x45, 0x40] [(.x11, 0x80000000)]).has [(.x10, 0xfffffffff8000000)]
-- sraiw a0, a1, 4: the upper half is not the sign
#guard (exec [0x1b, 0xd5, 0x45, 0x40] [(.x11, 0xffffffff00000010)]).has [(.x10, 1)]
-- sraiw with bit 25 set (a shift amount of 32 or more) is reserved: not lifted
#guard (exec [0x1b, 0xd5, 0xf5, 0x43] [(.x11, 0x80000000)]).isAbort
-- slliw with bit 25 set is reserved: not lifted
#guard (exec [0x1b, 0x95, 0xf5, 0x03] [(.x11, 1)]).isAbort
-- mulw: 2^16 * 2^16 has a zero low word
#guard (exec MULW [(.x11, 0x10000), (.x12, 0x10000)]).has [(.x10, 0)]
-- mulw: 0x7fffffff * 2 is negative
#guard (exec MULW [(.x11, 0x7fffffff), (.x12, 2)]).has [(.x10, -2)]
-- mulw: -1 * 5
#guard (exec MULW [(.x11, -1), (.x12, 5)]).has [(.x10, -5)]
-- mulw: only the low words count
#guard (exec MULW [(.x11, 0xffffffff00000003), (.x12, 0x100000004)]).has [(.x10, 12)]
-- divw: -7 / 2 rounds toward zero; rs1's upper half is ignored
#guard (exec DIVW [(.x11, 0xfffffff9), (.x12, 2)]).has [(.x10, -3)]
-- divw: 7 / -2
#guard (exec DIVW [(.x11, 7), (.x12, 0xfffffffe)]).has [(.x10, -3)]
-- divw by zero is all ones
#guard (exec DIVW [(.x11, 5), (.x12, 0)]).has [(.x10, max64)]
-- divw by a divisor whose low word is zero is by zero
#guard (exec DIVW [(.x11, 5), (.x12, 0x100000000)]).has [(.x10, max64)]
-- divw: INT32_MIN / -1 overflows to INT32_MIN
#guard (exec DIVW [(.x11, 0x80000000), (.x12, 0xffffffff)]).has [(.x10, 0xffffffff80000000)]
-- divuw: 0xffffffff / 2, unsigned
#guard (exec DIVUW [(.x11, 0xffffffff), (.x12, 2)]).has [(.x10, 0x7fffffff)]
-- divuw: a quotient with bit 31 set is sign-extended
#guard (exec DIVUW [(.x11, 0xfffffffe), (.x12, 1)]).has [(.x10, -2)]
-- divuw by zero is all ones
#guard (exec DIVUW [(.x11, 5), (.x12, 0)]).has [(.x10, max64)]
-- divuw: only the low words
#guard (exec DIVUW [(.x11, 0x100000006), (.x12, 0x500000003)]).has [(.x10, 2)]
-- divuw: a negative 64-bit divisor whose low word is 2
#guard (exec DIVUW [(.x11, 0x80000000), (.x12, 0xffffffff00000002)]).has [(.x10, 0x40000000)]
-- remw: -7 rem 2 is -1
#guard (exec REMW [(.x11, 0xfffffff9), (.x12, 2)]).has [(.x10, -1)]
-- remw: 7 rem -2 is 1
#guard (exec REMW [(.x11, 7), (.x12, 0xfffffffe)]).has [(.x10, 1)]
-- remw by zero is the dividend's low word, sign-extended
#guard (exec REMW [(.x11, 0x80000001), (.x12, 0)]).has [(.x10, 0xffffffff80000001)]
-- remw: INT32_MIN rem -1 is 0
#guard (exec REMW [(.x11, 0x80000000), (.x12, 0xffffffff)]).has [(.x10, 0)]
-- remuw: 0xffffffff rem 16
#guard (exec REMUW [(.x11, 0xffffffff), (.x12, 0x10)]).has [(.x10, 0xf)]
-- remuw by zero is the dividend's low word, sign-extended
#guard (exec REMUW [(.x11, 0x180000000), (.x12, 0)]).has [(.x10, 0xffffffff80000000)]
-- remuw: 0xffffffff rem 0xfffffffe, unsigned
#guard (exec REMUW [(.x11, 0xffffffff), (.x12, 0xfffffffe)]).has [(.x10, 1)]
-- remuw: a remainder with bit 31 set is sign-extended
#guard (exec REMUW [(.x11, 0x80000005), (.x12, 0xfffffff0)]).has [(.x10, 0xffffffff80000005)]

/-! ## mul, mulh, mulhsu, mulhu -/

-- mul: 3 * -4
#guard (exec MUL [(.x11, 3), (.x12, -4)]).has [(.x10, -12)]
-- mul: all ones squared is 1, mod 2^64
#guard (exec MUL [(.x11, -1), (.x12, -1)]).has [(.x10, 1)]
-- mul: 2^32 * 2^32 is 0, mod 2^64
#guard (exec MUL [(.x11, 0x100000000), (.x12, 0x100000000)]).has [(.x10, 0)]
-- mulh: -1 * -1 is 1, whose upper half is 0
#guard (exec MULH [(.x11, -1), (.x12, -1)]).has [(.x10, 0)]
-- mulh: -1 * 1 is -1, whose upper half is all ones
#guard (exec MULH [(.x11, -1), (.x12, 1)]).has [(.x10, max64)]
-- mulh: INT_MIN * INT_MIN is 2^126
#guard (exec MULH [(.x11, min64), (.x12, min64)]).has [(.x10, 0x4000000000000000)]
-- mulhsu: -1 (signed) * (2^64 - 1) (unsigned) is -2^64 + 1
#guard (exec MULHSU [(.x11, -1), (.x12, -1)]).has [(.x10, max64)]
-- mulhsu: 2 * (2^64 - 1) is 2^65 - 2
#guard (exec MULHSU [(.x11, 2), (.x12, -1)]).has [(.x10, 1)]
-- mulhsu: -1 * 1
#guard (exec MULHSU [(.x11, -1), (.x12, 1)]).has [(.x10, max64)]
-- mulhu: (2^64 - 1)^2 = 2^128 - 2^65 + 1
#guard (exec MULHU [(.x11, -1), (.x12, -1)]).has [(.x10, 0xfffffffffffffffe)]
-- mulhu: 2^32 * 2^32
#guard (exec MULHU [(.x11, 0x100000000), (.x12, 0x100000000)]).has [(.x10, 1)]

/-! ## div, divu, rem, remu: no trap -/

-- div: -7 / 2 rounds toward zero
#guard (exec DIV [(.x11, -7), (.x12, 2)]).has [(.x10, -3)]
-- div: 7 / -2
#guard (exec DIV [(.x11, 7), (.x12, -2)]).has [(.x10, -3)]
-- div by zero is -1
#guard (exec DIV [(.x11, 7), (.x12, 0)]).has [(.x10, max64)]
-- div: INT_MIN / -1 overflows to INT_MIN
#guard (exec DIV [(.x11, min64), (.x12, -1)]).has [(.x10, min64)]
-- divu: (2^64 - 1) / 2
#guard (exec DIVU [(.x11, -1), (.x12, 2)]).has [(.x10, 0x7fffffffffffffff)]
-- divu by zero is all ones
#guard (exec DIVU [(.x11, 7), (.x12, 0)]).has [(.x10, max64)]
-- rem: -7 rem 2 has the dividend's sign
#guard (exec REM [(.x11, -7), (.x12, 2)]).has [(.x10, -1)]
-- rem: 7 rem -2
#guard (exec REM [(.x11, 7), (.x12, -2)]).has [(.x10, 1)]
-- rem by zero is the dividend
#guard (exec REM [(.x11, -7), (.x12, 0)]).has [(.x10, -7)]
-- rem: INT_MIN rem -1 is 0
#guard (exec REM [(.x11, min64), (.x12, -1)]).has [(.x10, 0)]
-- remu: (2^64 - 1) rem 10 = 18446744073709551615 rem 10
#guard (exec REMU [(.x11, -1), (.x12, 10)]).has [(.x10, 5)]
-- remu by zero is the dividend
#guard (exec REMU [(.x11, -7), (.x12, 0)]).has [(.x10, -7)]

/-! ## Loads: every width, sign- and zero-extended -/

/-- Memory with `80 ff 7f 90 01 02 03 84` at 0x2000. -/
def ldMem : Mem := memAt 0x2000 [0x80, 0xff, 0x7f, 0x90, 0x01, 0x02, 0x03, 0x84]

-- lb a0, 0(a1): sign-extended
#guard (exec [0x03, 0x85, 0x05, 0x00] [(.x11, 0x2000)] ldMem).has [(.x10, 0xffffffffffffff80)]
-- lb a0, 0(a1) of a positive byte
#guard (exec [0x03, 0x85, 0x05, 0x00] [(.x11, 0x2002)] ldMem).has [(.x10, 0x7f)]
-- lbu a0, 0(a1)
#guard (exec [0x03, 0xc5, 0x05, 0x00] [(.x11, 0x2000)] ldMem).has [(.x10, 0x80)]
-- lh a0, 0(a1)
#guard (exec [0x03, 0x95, 0x05, 0x00] [(.x11, 0x2000)] ldMem).has [(.x10, 0xffffffffffffff80)]
-- lh a0, 0(a1) at 0x2002: 0x907f
#guard (exec [0x03, 0x95, 0x05, 0x00] [(.x11, 0x2002)] ldMem).has [(.x10, 0xffffffffffff907f)]
-- lhu a0, 0(a1)
#guard (exec [0x03, 0xd5, 0x05, 0x00] [(.x11, 0x2000)] ldMem).has [(.x10, 0xff80)]
-- lw a0, 0(a1)
#guard (exec [0x03, 0xa5, 0x05, 0x00] [(.x11, 0x2000)] ldMem).has [(.x10, 0xffffffff907fff80)]
-- lwu a0, 0(a1)
#guard (exec [0x03, 0xe5, 0x05, 0x00] [(.x11, 0x2000)] ldMem).has [(.x10, 0x907fff80)]
-- lwu a0, 0(a1) at 0x2004
#guard (exec [0x03, 0xe5, 0x05, 0x00] [(.x11, 0x2004)] ldMem).has [(.x10, 0x84030201)]
-- ld a0, 0(a1)
#guard (exec [0x03, 0xb5, 0x05, 0x00] [(.x11, 0x2000)] ldMem).has [(.x10, 0x84030201907fff80)]
-- lw a0, -4(a1): a negative offset
#guard (exec [0x03, 0xa5, 0xc5, 0xff] [(.x11, 0x2004)] ldMem).has [(.x10, 0xffffffff907fff80)]
-- ld a0, 8(a1)
#guard (exec [0x03, 0xb5, 0x85, 0x00] [(.x11, 0x1ff8)] ldMem).has [(.x10, 0x84030201907fff80)]

/-! ## Stores: the low bytes of rs2, nothing beside them -/

/-- Memory with eight bytes 0xaa at 0x3000. -/
def stMem : Mem := memAt 0x3000 [0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa]
def v : BitVec 64 := 0x1122334455667788

-- sb a2, 0(a1)
#guard memAfter (exec [0x23, 0x80, 0xc5, 0x00] [(.x11, 0x3000), (.x12, v)] stMem) 0x3000 ==
  some 0xaaaaaaaaaaaaaa88
-- sh a2, 0(a1)
#guard memAfter (exec [0x23, 0x90, 0xc5, 0x00] [(.x11, 0x3000), (.x12, v)] stMem) 0x3000 ==
  some 0xaaaaaaaaaaaa7788
-- sw a2, 0(a1)
#guard memAfter (exec [0x23, 0xa0, 0xc5, 0x00] [(.x11, 0x3000), (.x12, v)] stMem) 0x3000 ==
  some 0xaaaaaaaa55667788
-- sd a2, 0(a1)
#guard memAfter (exec [0x23, 0xb0, 0xc5, 0x00] [(.x11, 0x3000), (.x12, v)] stMem) 0x3000 == some v
-- sd a2, -8(a1)
#guard memAfter (exec [0x23, 0xbc, 0xc5, 0xfe] [(.x11, 0x3008), (.x12, v)] stMem) 0x3000 == some v
-- sb a2, 0(a1) at 0x3003: little-endian place
#guard memAfter (exec [0x23, 0x80, 0xc5, 0x00] [(.x11, 0x3003), (.x12, v)] stMem) 0x3000 ==
  some 0xaaaaaaaa88aaaaaa
-- a store writes no register
#guard (exec [0x23, 0xb0, 0xc5, 0x00] [(.x10, 9), (.x11, 0x3000), (.x12, v)] stMem).has
  [(.x10, 9), (.x11, 0x3000), (.x12, v)]

/-! ## x0: reads 0, and a write to it is lost -/

-- add a0, zero, zero reads 0 whatever the register file holds for x0
#guard (exec [0x33, 0x05, 0x00, 0x00] [(.x0, 7)]).has [(.x10, 0)]
-- li a0, 5 (addi a0, zero, 5)
#guard (exec [0x13, 0x05, 0x50, 0x00] [(.x0, 99)]).has [(.x10, 5)]
-- sd zero, 0(a1) stores 0
#guard memAfter (exec [0x23, 0xb0, 0x05, 0x00] [(.x0, 0x55), (.x11, 0x3000)] stMem) 0x3000 ==
  some 0
-- add zero, a1, a2 changes no other register
#guard (exec [0x33, 0x80, 0xc5, 0x00] [(.x10, 4), (.x11, 1), (.x12, 2)]).has
  [(.x10, 4), (.x11, 1), (.x12, 2)]
-- addi zero, zero, 5; add a0, zero, zero: the write to x0 is lost
#guard (seq [[0x13, 0x00, 0x50, 0x00], [0x33, 0x05, 0x00, 0x00]] []).has [(.x10, 0)]
-- lui zero, 0x12345; addi a0, zero, 1
#guard (seq [[0x37, 0x50, 0x34, 0x12], [0x13, 0x05, 0x10, 0x00]] []).has [(.x10, 1)]
-- ld zero, 0(a1); add a0, zero, zero: a load into x0 is lost
#guard (seq [[0x03, 0xb0, 0x05, 0x00], [0x33, 0x05, 0x00, 0x00]] [(.x11, 0x2000)] ldMem).has
  [(.x10, 0)]

/-! ## Branches: taken to `taken`, not taken to `next` -/

-- beq a1, a2, .+16
#guard (exec [0x63, 0x88, 0xc5, 0x00] [(.x11, 3), (.x12, 3)]).isTaken
#guard (exec [0x63, 0x88, 0xc5, 0x00] [(.x11, 3), (.x12, 4)]).isNext
-- bne a1, a2, .+16
#guard (exec [0x63, 0x98, 0xc5, 0x00] [(.x11, 3), (.x12, 4)]).isTaken
#guard (exec [0x63, 0x98, 0xc5, 0x00] [(.x11, 3), (.x12, 3)]).isNext
-- blt a1, a2, .+16: signed
#guard (exec [0x63, 0xc8, 0xc5, 0x00] [(.x11, -1), (.x12, 1)]).isTaken
#guard (exec [0x63, 0xc8, 0xc5, 0x00] [(.x11, 1), (.x12, -1)]).isNext
#guard (exec [0x63, 0xc8, 0xc5, 0x00] [(.x11, 1), (.x12, 1)]).isNext
-- bge a1, a2, .+16: signed, equal is taken
#guard (exec [0x63, 0xd8, 0xc5, 0x00] [(.x11, 1), (.x12, 1)]).isTaken
#guard (exec [0x63, 0xd8, 0xc5, 0x00] [(.x11, -1), (.x12, 1)]).isNext
-- bltu a1, a2, .+16: unsigned
#guard (exec [0x63, 0xe8, 0xc5, 0x00] [(.x11, 1), (.x12, -1)]).isTaken
#guard (exec [0x63, 0xe8, 0xc5, 0x00] [(.x11, -1), (.x12, 1)]).isNext
-- bgeu a1, a2, .+16: unsigned
#guard (exec [0x63, 0xf8, 0xc5, 0x00] [(.x11, -1), (.x12, 1)]).isTaken
#guard (exec [0x63, 0xf8, 0xc5, 0x00] [(.x11, 0), (.x12, 1)]).isNext
-- beq a1, a2, .+4: taken or not, the next instruction
#guard (exec [0x63, 0x82, 0xc5, 0x00] [(.x11, 3), (.x12, 3)]).isNext
-- beqz a1, .-8: x0 reads 0 whatever the register file holds
#guard (exec [0xe3, 0x8c, 0x05, 0xfe] [(.x0, 5), (.x11, 0)]).isTaken
#guard (exec [0xe3, 0x8c, 0x05, 0xfe] [(.x0, 5), (.x11, 5)]).isNext
-- a taken branch writes no register
#guard (exec [0x63, 0x88, 0xc5, 0x00] [(.x10, 9), (.x11, 3), (.x12, 3)]).hasTaken
  [(.x10, 9), (.x11, 3), (.x12, 3)]
/-- A program where only the next instruction is in the function, and nothing is a function. -/
def outside : Cx where
  label a := if a == at0 + 4 then some next else none
  entry _ := none
  cands := []
  all := []
  abort := abort

-- a branch out of the function gives up
#guard (execCx outside [0x63, 0x88, 0xc5, 0x00] [(.x11, 3), (.x12, 3)]).isAbort

/-! ## jal -/

-- jal ra, .+256 to a function: a call returning to the next instruction
#guard leavesBy (exec [0xef, 0x00, 0x00, 0x10] [] (entries := [at0 + 256]))
  (.Lcall (at0 + 4) (.direct 0))
-- jal ra, .-16 to the second function
#guard leavesBy (exec [0xef, 0xf0, 0x1f, 0xff] [] (entries := [0x50000, at0 - 16]))
  (.Lcall (at0 + 4) (.direct 1))
-- jal ra, .+256 to no function gives up
#guard (exec [0xef, 0x00, 0x00, 0x10] []).isAbort
-- j .+256 inside the function
#guard (exec [0x6f, 0x00, 0x00, 0x10] [(.x1, 7)]).hasTaken [(.x1, 7)]
-- j .+4
#guard (exec [0x6f, 0x00, 0x40, 0x00] []).isNext
-- jal t0, .+256: links through t0, a jump inside the function
#guard (exec [0xef, 0x02, 0x00, 0x10] [(.x1, 7)]).hasTaken [(.x5, at0 + 4), (.x1, 7)]
/-- A program where `at0 + 256` is function 3, outside this function. -/
def far : Cx where
  label _ := none
  entry a := if a == at0 + 256 then some 3 else none
  cands := []
  all := [0, 1, 2, 3]
  abort := abort

-- j .+256 to the entry of another function: a tail call
#guard leavesBy (execCx far [0x6f, 0x00, 0x00, 0x10] [])
  (.Ltail (.direct 3))

/-! ## jalr -/

-- ret
#guard leavesBy (exec [0x67, 0x80, 0x00, 0x00] [(.x1, 0x1234)]) .Lret
-- jalr a1: an indirect call among all functions
#guard callsInd (exec [0xe7, 0x80, 0x05, 0x00] [(.x11, 0x20000)] (entries := [0x30000, 0x20000]))
  (at0 + 4) 0x20000 [0, 1]
-- jalr ra, 1(a1): the target's lowest bit is cleared
#guard callsInd (exec [0xe7, 0x80, 0x15, 0x00] [(.x11, 0x20000)] (entries := [0x20000]))
  (at0 + 4) 0x20000 [0]
-- jalr 16(ra): the target is from ra before the call writes it
#guard callsInd (exec [0xe7, 0x80, 0x00, 0x01] [(.x1, 0x20000)] (entries := [0x20010]))
  (at0 + 4) 0x20010 [0]
-- jalr a1 with no functions gives up
#guard (exec [0xe7, 0x80, 0x05, 0x00] [(.x11, 0x20000)]).isAbort
-- jr a1 to a candidate inside the function
#guard (exec [0x67, 0x80, 0x05, 0x00] [(.x11, at0 + 0x40)] (cands := [at0 + 0x40])).isTaken
-- jr a1 to the next instruction
#guard (exec [0x67, 0x80, 0x05, 0x00] [(.x11, at0 + 4)] (cands := [at0 + 4, at0 + 0x40])).isNext
-- jr a1 to no candidate, with no function: gives up
#guard (exec [0x67, 0x80, 0x05, 0x00] [(.x11, at0 + 8)] (cands := [at0 + 0x40])).isAbort
-- jr a1 with no candidates: a tail call among the functions
#guard tailsInd (exec [0x67, 0x80, 0x05, 0x00] [(.x11, 0x30000)] (entries := [0x30000])) 0x30000 [0]
-- jalr t0, t0: the target is t0 before t0 is written with the return address
#guard (exec [0xe7, 0x82, 0x02, 0x00] [(.x5, at0 + 0x40)] (cands := [at0 + 0x40])).hasTaken
  [(.x5, at0 + 4)]

/-! ## auipc then jalr: `prev` makes the target known -/

/-- `auipc t1, 0` just before `at0`. -/
def auipcT1 : At Decoded := instrAt (at0 - 4) [0x17, 0x03, 0x00, 0x00]
/-- `auipc a0, 0` just before `at0`. -/
def auipcA0 : At Decoded := instrAt (at0 - 4) [0x17, 0x05, 0x00, 0x00]
/-- `jalr 16(t1)`. -/
def JALR16T1 := [0xe7, 0x00, 0x03, 0x01]

-- after auipc t1: a call of the one function at at0 - 4 + 16
#guard callsInd (exec JALR16T1 [(.x6, at0 - 4)] (prev := some auipcT1)
  (entries := [0x50000, at0 + 12])) (at0 + 4) (at0 + 12) [1]
-- without it: a call among all the functions
#guard callsInd (exec JALR16T1 [(.x6, at0 - 4)] (entries := [0x50000, at0 + 12]))
  (at0 + 4) (at0 + 12) [0, 1]
-- after an auipc of another register: among all the functions
#guard callsInd (exec JALR16T1 [(.x6, at0 - 4)] (prev := some auipcA0)
  (entries := [0x50000, at0 + 12])) (at0 + 4) (at0 + 12) [0, 1]
-- after auipc t1, to an address that is no function: gives up
#guard (exec JALR16T1 [(.x6, at0 - 4)] (prev := some auipcT1) (entries := [0x50000])).isAbort
-- auipc t1, 0; jalr 16(t1) in sequence: t1 is set by the auipc, the call is of at0 + 16
#guard callsInd (seq [[0x17, 0x03, 0x00, 0x00], JALR16T1] [] (entries := [0x50000, at0 + 16]))
  (at0 + 8) (at0 + 16) [1]
-- auipc t1; jr 16(t1): a far jump inside the function
#guard (exec [0x67, 0x00, 0x03, 0x01] [(.x6, at0 - 4)] (prev := some auipcT1)).isTaken
-- the same jump reached with another value in t1 gives up
#guard (exec [0x67, 0x00, 0x03, 0x01] [(.x6, 0x777000)] (prev := some auipcT1)).isAbort

/-! ## ecall, ebreak, fence, words that are no instruction -/

-- ecall leaves for the environment, registers unchanged
#guard match exec [0x73, 0x00, 0x00, 0x00] [(.x5, 93), (.x10, 1)] with
  | .leaves (.Lext 0) regs _ => regs .x5 == 93 && regs .x10 == 1
  | _ => false
-- ebreak is not lifted
#guard (exec [0x73, 0x00, 0x10, 0x00] []).isAbort
-- fence does nothing to registers
#guard (exec [0x0f, 0x00, 0xf0, 0x0f] [(.x10, 3)]).has [(.x10, 3)]
-- the word 0 is no instruction
#guard (exec [0x00, 0x00, 0x00, 0x00] []).isAbort
-- all ones is no instruction
#guard (exec [0xff, 0xff, 0xff, 0xff] []).isAbort
-- a compressed instruction's bytes (c.addi a0, 1 then c.nop) are no instruction
#guard (exec [0x05, 0x05, 0x01, 0x00] []).isAbort

/-! ## decodeWord: which instructions riscv-zkvm takes, which the decompiler adds -/

-- add is riscv-zkvm's
#guard (decodeWord (wordOf ADD)) matches .instr (.ADD .x10 .x11 .x12)
-- subw and srlw are riscv-zkvm's
#guard (decodeWord (wordOf SUBW)) matches .instr (.SUBW .x10 .x11 .x12)
#guard (decodeWord (wordOf SRLW)) matches .instr (.SRLW .x10 .x11 .x12)
-- the nine others are the decompiler's operations
#guard [ADDW, SLLW, SRAW, MULW, DIVW, DIVUW, REMW, REMUW, [0x1b, 0xd5, 0xf5, 0x41]].all
  fun b => (decodeWord (wordOf b)) matches .op _
-- the word 0 is none
#guard (decodeWord 0) matches .none

/-! ## The candidates of a computed jump in the `--proved` lift (`jalrCands`)

  Two functions: `f` at 0x1000 calls `g` at 0x2000 by `auipc ra, 1; jalr ra, 0(ra)`, then
  jumps through `t0`, which nothing before sets. -/

def fnsC : List Fn :=
  [{ name := "f", base := 0x1000,
     prog := [.AUIPC .x1 1, .JALR .x1 .x1 0, .JALR .x0 .x5 0] },
   { name := "g", base := 0x2000, prog := [.JALR .x0 .x1 0] }]

-- `auipc ra` then `jalr ra`: the one function at the address
#guard jalrCands (entryOf fnsC) (List.range 2) 0x1004 (some (.AUIPC .x1 1)) .x1 0 == [1]
-- the offset of `jalr` counts: 0x2000 + 4 is no function's entry, so every function
#guard jalrCands (entryOf fnsC) (List.range 2) 0x1004 (some (.AUIPC .x1 1)) .x1 4 == [0, 1]
-- a register `auipc` did not set: every function
#guard jalrCands (entryOf fnsC) (List.range 2) 0x1008 (some (.JALR .x1 .x1 0)) .x5 0 == [0, 1]
-- nothing before it (the first instruction of a function): every function
#guard jalrCands (entryOf fnsC) (List.range 2) 0x2000 none .x1 0 == [0, 1]

/-! ## The lift of a function from its own code (`Fn.targets`, `getElem?_liftProg_of_targets`)

  `f` above asks for the function at 0x2000 alone: its last `jalr` follows no `auipc`. `h` at
  0x3000 calls `g` by `jal ra`, jumps inside itself, returns, and tail-calls `f` by `jal x0`. -/

/-- `jal ra, g; jal x0, +8; ret; jal x0, f`. -/
def hJ : Fn :=
  { name := "h", base := 0x3000,
    prog := [.JAL .x1 (-0x1000), .JAL .x0 8, .JALR .x0 .x1 0, .JAL .x0 (-0x200c)] }

def fnsJ : List Fn := fnsC ++ [hJ]

-- the paired `jalr` asks; the bare one does not
#guard (fnsC[0]?.map Fn.targets) == some [0x2000]
-- the call and the tail call ask; the jump inside the function and the return do not
#guard hJ.targets == [0x2000, 0x1000]

/-- A table of `h`'s two callees, in place of the program. -/
def tblJ (a : BitVec 64) : Option Nat :=
  if a == 0x2000 then some 1 else if a == 0x1000 then some 0 else none

/-- `h` in the program is `h` lifted with its own table. The agreement is checked as a `Bool`:
    as a `Prop`, `decide` goes through `DecidableEq` on addresses, which the kernel is slow on. -/
example : (liftProg fnsJ)[2]? = some (liftFn tblJ (List.range 3) hJ) :=
  getElem?_liftProg_of_targets rfl fun a ha => beq_iff_eq.mp <| List.all_eq_true.mp
    (by decide +kernel : (hJ.targets.all fun a => entryOf fnsJ a == tblJ a) = true) a ha

-- the table is needed: with no callee, the call is `Labort`, not a call of `g`
#guard (liftFn (fun _ => none) (List.range 3) hJ).body[1]? matches some LinstrR.Labort
#guard ((liftProg fnsJ)[2]?.bind (·.body[1]?)) matches some (LinstrR.Lcall _ (.direct 1))

end Tools.Test.RiscV
