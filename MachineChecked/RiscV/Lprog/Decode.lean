/-
  MachineChecked.RiscV.Lprog.Decode

  A word of code, decoded for the lifts of whole binaries (`Flat.lean`, `Whole.lean`).

  riscv-zkvm's `Instr` has the instructions its machine steps. RV64IM has nine more, all on
  the low 32 bits of their operands with the result sign-extended: `addw`, `sllw`, `sraw`,
  `sraiw`, `mulw`, `divw`, `divuw`, `remw` and `remuw`. A compiler emits them, so the lifts
  take them: each is a shared operation (`wordOp`), stated here from the RISC-V manual.
  riscv-zkvm's machine does not run them, so no theorem about that machine can cover them;
  they are checked by running (`scripts/decompile-check`).

  ## Main definitions

  * `Decoded`, `decodeWord`, `wordOp`
-/

import RiscvZkvm.Interpreter.Decode
import MachineChecked.RiscV.Lprog.Instance

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter MachineChecked.Lprog

/-- The low 32 bits, sign-extended and zero-extended. -/
private def s32 (e : Expr Reg) : Expr Reg := .un (.sext .b4) e
private def z32 (e : Expr Reg) : Expr Reg := .un (.zext .b4) e

/-- **The 32-bit operations of RV64IM that `Instr` lacks**, as shared operations. A shift
    takes the low five bits of its amount. Division by zero gives all ones and the dividend
    as remainder, and the one overflow (the least number by -1) gives the dividend, as the
    64-bit operations do on the extended operands before the result is cut to 32 bits. -/
def wordOp (w : BitVec 32) : Option (Op Reg) :=
  let rd := regOfBits (w.extractLsb' 7 5)
  let a := rv (regOfBits (w.extractLsb' 15 5))
  let b := rv (regOfBits (w.extractLsb' 20 5))
  let f3 := (w.extractLsb' 12 3).toNat
  let f7 := (w.extractLsb' 25 7).toNat
  let amount : Expr Reg := .bin .and b (.imm 31)
  match (w.extractLsb' 0 7).toNat, f7, f3 with
  | 0x3B, 0, 0 => some (.set rd (s32 (.bin .add a b)))
  | 0x3B, 0, 1 => some (.set rd (s32 (.bin .shl a amount)))
  | 0x3B, 0x20, 5 => some (.set rd (.bin .ashr (s32 a) amount))
  | 0x3B, 1, 0 => some (.set rd (s32 (.bin .mul a b)))
  | 0x3B, 1, 4 => some (.set rd (s32 (.bin .div (s32 a) (s32 b))))
  | 0x3B, 1, 5 => some (.set rd (s32 (.bin .divu (z32 a) (z32 b))))
  | 0x3B, 1, 6 => some (.set rd (s32 (.bin .rem (s32 a) (s32 b))))
  | 0x3B, 1, 7 => some (.set rd (s32 (.bin .remu (z32 a) (z32 b))))
  | 0x1B, 0x20, 5 => some (.set rd (.bin .ashr (s32 a) (.imm (BitVec.ofNat 64 (w.extractLsb' 20 5).toNat))))
  | _, _, _ => none

/-- A word of code, decoded. -/
inductive Decoded where
  /-- An instruction riscv-zkvm has. -/
  | instr (i : Instr)
  /-- One it lacks, as its operation. -/
  | op (o : Op Reg)
  /-- No instruction of RV64IM. -/
  | none
  deriving Inhabited

/-- **A word, decoded**: by riscv-zkvm's decoder, then as one of the operations it lacks. -/
def decodeWord (w : BitVec 32) : Decoded :=
  match decode w with
  | some i => .instr i
  | none => match wordOp w with
    | some o => .op o
    | none => .none

end MachineChecked.RiscV.Lprog
