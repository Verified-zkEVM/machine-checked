/-
  MachineChecked.RiscV.Lprog.Instance

  RISC-V as an instruction set of the low logical program, on riscv-zkvm.

  Each instruction that does not transfer control (a pure instruction other than `auipc`, or a
  load or store) is translated to a shared operation (`opOf`). Registers are named
  `x0`..`x31`, and `x0` is read as the immediate zero. The state beside the registers is a
  riscv-zkvm `MachineState`, whose registers and pc are ignored. Its memory (`rvMem`) is
  riscv-zkvm's, behind SP1's memory check, so `rvIsa` is `Isa.ofOps` over SP1's memory.

  `opOf_spec` is the translation's correctness: the operation succeeds exactly when SP1's
  memory check `memOkSp1` passes, and its result agrees with riscv-zkvm's `execInstrBr`.

  `Agree t u` says two machine states agree on everything an instruction reads or writes other
  than the pc: registers as `getReg` reads them, memory, code and the I/O fields. A pure or
  memory instruction keeps it (`Agree.execInstrBr`), and `memOkSp1` cannot tell such states
  apart (`Agree.memOkSp1`).
-/

import MachineChecked.Lprog.Op
import MachineChecked.RiscV.Sym.Core
import Std.Tactic.BVDecide

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog

/-- The name of a register in Lprog. -/
def regName (r : Reg) : String := toString r

/-- The register a name stands for. -/
def regOfName (n : String) : Option Reg := allRegs.find? (fun r => regName r == n)

theorem regOfName_regName (r : Reg) : regOfName (regName r) = some r := by
  cases r <;> rfl

theorem regName_inj {r r' : Reg} (h : regName r = regName r') : r = r' := by
  have := regOfName_regName r
  rw [h, regOfName_regName] at this
  exact (Option.some.inj this).symm

/-- A machine state with the registers of an Lprog register file. -/
def ofParts (regs : String → BitVec 64) (m : MachineState) : MachineState :=
  { m with regs := fun r => regs (regName r) }

/-- The register file a machine state gives Lprog: each register name reads `getReg`, every
    other name keeps its value in `old`. -/
def regsOf (old : String → BitVec 64) (t : MachineState) : String → BitVec 64 :=
  fun n => match regOfName n with
    | some r => t.getReg r
    | none => old n

/-! ## Operations -/

/-- Writes at most one register and falls through: no memory access, no control transfer,
    no system call. -/
def isStraight : Instr → Bool
  | .ADD .. | .SUB .. | .SLL .. | .SRL .. | .SRA .. | .AND .. | .OR .. | .XOR ..
  | .SLT .. | .SLTU .. | .ADDI .. | .ANDI .. | .ORI .. | .XORI .. | .SLTI .. | .SLTIU ..
  | .SLLI .. | .SRLI .. | .SRAI .. | .LUI .. | .AUIPC .. | .MV .. | .LI .. | .NOP
  | .ADDIW .. | .SUBW .. | .SRLW .. | .SLLIW .. | .SRLIW .. | .FENCE
  | .MUL .. | .MULH .. | .MULHSU .. | .MULHU .. | .DIV .. | .DIVU .. | .REM .. | .REMU .. =>
    true
  | _ => false

theorem isStraight_isMemAccess {i : Instr} (h : isStraight i = true) :
    i.isMemAccess = false := by
  cases i <;> simp_all [isStraight, Instr.isMemAccess]

theorem isStraight_ne_ecall {i : Instr} (h : isStraight i = true) : i ≠ .ECALL := by
  rintro rfl; simp [isStraight] at h

theorem isStraight_ne_ebreak {i : Instr} (h : isStraight i = true) : i ≠ .EBREAK := by
  rintro rfl; simp [isStraight] at h

/-- Straight and not reading the pc: the effect is a function of the registers. -/
def isPure (i : Instr) : Bool :=
  isStraight i && match i with
    | .AUIPC .. => false
    | _ => true

/-- An operation: pure, or a load or store. -/
def opnOk (i : Instr) : Bool := isPure i || (i.isMemAccess && !isCSRS i)

/-! ## The translation -/

/-- A register as an operand of a condition; `x0` is the immediate zero. -/
def opnd (r : Reg) : LOperand := if r = .x0 then .imm 0 else .reg (regName r)

/-- A register as an expression; `x0` is the immediate zero. -/
def rv (r : Reg) : Expr := if r = .x0 then .imm 0 else .reg (regName r)

/-- A sign-extended 12-bit immediate. -/
def se12 (imm : BitVec 12) : Expr := .imm (signExtend12 imm)

/-- A shift amount. -/
def sh (n : Nat) : Expr := .imm (BitVec.ofNat 64 n)

/-- The address `rs1 + offset` of a load or store. -/
def addr (rs1 : Reg) (off : BitVec 12) : Expr := .bin .add (rv rs1) (se12 off)

/-- **The translation of an instruction into a shared operation.** Defined for the
    operations (`opnOk`); anything else is `skip`, and is not lifted as an operation. -/
def opOf : Instr → Op
  | .ADD rd a b => .set (regName rd) (.bin .add (rv a) (rv b))
  | .SUB rd a b => .set (regName rd) (.bin .sub (rv a) (rv b))
  | .SLL rd a b => .set (regName rd) (.bin .shl (rv a) (.bin .and (rv b) (.imm 63)))
  | .SRL rd a b => .set (regName rd) (.bin .lshr (rv a) (.bin .and (rv b) (.imm 63)))
  | .SRA rd a b => .set (regName rd) (.bin .ashr (rv a) (.bin .and (rv b) (.imm 63)))
  | .AND rd a b => .set (regName rd) (.bin .and (rv a) (rv b))
  | .OR rd a b => .set (regName rd) (.bin .or (rv a) (rv b))
  | .XOR rd a b => .set (regName rd) (.bin .xor (rv a) (rv b))
  | .SLT rd a b => .set (regName rd) (.bin .slt (rv a) (rv b))
  | .SLTU rd a b => .set (regName rd) (.bin .ult (rv a) (rv b))
  | .ADDI rd a i => .set (regName rd) (.bin .add (rv a) (se12 i))
  | .ANDI rd a i => .set (regName rd) (.bin .and (rv a) (se12 i))
  | .ORI rd a i => .set (regName rd) (.bin .or (rv a) (se12 i))
  | .XORI rd a i => .set (regName rd) (.bin .xor (rv a) (se12 i))
  | .SLTI rd a i => .set (regName rd) (.bin .slt (rv a) (se12 i))
  | .SLTIU rd a i => .set (regName rd) (.bin .ult (rv a) (se12 i))
  | .SLLI rd a s => .set (regName rd) (.bin .shl (rv a) (sh s.toNat))
  | .SRLI rd a s => .set (regName rd) (.bin .lshr (rv a) (sh s.toNat))
  | .SRAI rd a s => .set (regName rd) (.bin .ashr (rv a) (sh s.toNat))
  | .LUI rd i => .set (regName rd) (.imm ((i.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64))
  | .LD rd a o => .load (regName rd) .b8 false (addr a o)
  | .LW rd a o => .load (regName rd) .b4 true (addr a o)
  | .LWU rd a o => .load (regName rd) .b4 false (addr a o)
  | .LB rd a o => .load (regName rd) .b1 true (addr a o)
  | .LH rd a o => .load (regName rd) .b2 true (addr a o)
  | .LBU rd a o => .load (regName rd) .b1 false (addr a o)
  | .LHU rd a o => .load (regName rd) .b2 false (addr a o)
  | .SD a b o => .store .b8 (addr a o) (rv b)
  | .SW a b o => .store .b4 (addr a o) (rv b)
  | .SB a b o => .store .b1 (addr a o) (rv b)
  | .SH a b o => .store .b2 (addr a o) (rv b)
  | .MV rd a => .set (regName rd) (rv a)
  | .LI rd v => .set (regName rd) (.imm v)
  | .ADDIW rd a i => .set (regName rd) (.un (.sext .b4) (.bin .add (rv a) (se12 i)))
  | .SUBW rd a b => .set (regName rd) (.un (.sext .b4) (.bin .sub (rv a) (rv b)))
  | .SRLW rd a b =>
    .set (regName rd) (.un (.sext .b4) (.bin .lshr (.un (.zext .b4) (rv a)) (.bin .and (rv b) (.imm 31))))
  | .SLLIW rd a s => .set (regName rd) (.un (.sext .b4) (.bin .shl (rv a) (sh s.toNat)))
  | .SRLIW rd a s => .set (regName rd) (.un (.sext .b4) (.bin .lshr (.un (.zext .b4) (rv a)) (sh s.toNat)))
  | .MUL rd a b => .set (regName rd) (.bin .mul (rv a) (rv b))
  | .MULH rd a b => .set (regName rd) (.bin .mulh (rv a) (rv b))
  | .MULHSU rd a b => .set (regName rd) (.bin .mulhsu (rv a) (rv b))
  | .MULHU rd a b => .set (regName rd) (.bin .mulhu (rv a) (rv b))
  | .DIV rd a b => .set (regName rd) (.bin .div (rv a) (rv b))
  | .DIVU rd a b => .set (regName rd) (.bin .divu (rv a) (rv b))
  | .REM rd a b => .set (regName rd) (.bin .rem (rv a) (rv b))
  | .REMU rd a b => .set (regName rd) (.bin .remu (rv a) (rv b))
  | _ => .skip

/-- SP1's memory, on riscv-zkvm's machine state: an access must be in SP1's address space and
    aligned, and a store must not hit code. -/
def rvMem : Mem MachineState where
  load w a m :=
    if isValidMemAddrSp1 a && alignedFor w.bytes a then
      some (match w with
        | .b1 => (m.getByte a).zeroExtend 64
        | .b2 => (m.getHalfword a).zeroExtend 64
        | .b4 => (m.getWord32 a).zeroExtend 64
        | .b8 => m.getMem a)
    else none
  store w a v m :=
    if isValidMemAddrSp1 a && alignedFor w.bytes a && noCodeAt m a w.bytes then
      some (match w with
        | .b1 => m.setByte a (v.truncate 8)
        | .b2 => m.setHalfword a (v.truncate 16)
        | .b4 => m.setWord32 a (v.truncate 32)
        | .b8 => m.setMem a v)
    else none

/-- **RISC-V on SP1**, over the shared operations. -/
abbrev rvIsa : Isa := Isa.ofOps MachineState rvMem

/-! ## Agreement -/

/-- Two machine states agree on everything an instruction reads or writes, but the pc. -/
structure Agree (t u : MachineState) : Prop where
  regs : ∀ r, t.getReg r = u.getReg r
  mem : ∀ a, t.getMem a = u.getMem a
  code : t.code = u.code
  committed : t.committed = u.committed
  publicValues : t.publicValues = u.publicValues
  privateInput : t.privateInput = u.privateInput
  inputBufBase : t.inputBufBase = u.inputBufBase

theorem Agree.memOkSp1 {t u : MachineState} (h : Agree t u) (i : Instr) :
    RiscvZkvm.Rv64.memOkSp1 t i = RiscvZkvm.Rv64.memOkSp1 u i := by
  cases i <;> simp [RiscvZkvm.Rv64.memOkSp1, memAccess, noCodeAt, h.regs, h.code]

/-- A pure or memory instruction keeps agreement. -/
theorem Agree.execInstrBr {t u : MachineState} (h : Agree t u) {i : Instr} (hi : opnOk i = true) :
    Agree (RiscvZkvm.Rv64.execInstrBr t i) (RiscvZkvm.Rv64.execInstrBr u i) := by
  obtain ⟨hr, hm, hc, h1, h2, h3, h4⟩ := h
  cases i <;> simp only [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, Bool.or_false,
      Bool.and_true, Bool.false_and, Bool.true_and, Bool.not_true, Bool.and_false, Bool.or_self,
      Bool.false_eq_true] at hi <;>
    constructor <;>
    simp [RiscvZkvm.Rv64.execInstrBr, getReg_setReg, getReg_setMem, getMem_setMem,
      MachineState.setByte, MachineState.setHalfword, MachineState.setWord32, MachineState.getByte,
      MachineState.getHalfword, MachineState.getWord32, hr, hm, hc, h1, h2, h3, h4]

/-! ## The translation is correct -/

theorem getReg_ofParts (regs : String → BitVec 64) (m : MachineState) (r : Reg) :
    (ofParts regs m).getReg r = if r = .x0 then 0 else regs (regName r) := by
  cases r <;> rfl

theorem rv_eval (regs : String → BitVec 64) (m : MachineState) (r : Reg) :
    (rv r).eval regs = (ofParts regs m).getReg r := by
  rw [getReg_ofParts]; unfold rv; split <;> rfl

theorem opnd_val (regs : String → BitVec 64) (m : MachineState) (r : Reg) :
    operandVal regs (opnd r) = some ((ofParts regs m).getReg r) := by
  rw [getReg_ofParts]; unfold opnd; split <;> rfl

theorem agree_setPC (t : MachineState) (v : Word) : Agree t (t.setPC v) :=
  ⟨fun _ => by simp, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Writing a register in Lprog agrees with writing it in the machine. -/
theorem agree_set (regs : String → BitVec 64) (m : MachineState) (rd : Reg) {v v' : Word} (p : Word)
    (h : v = v') :
    Agree (ofParts (updReg regs (regName rd) v) m) (((ofParts regs m).setReg rd v').setPC p) := by
  subst h
  refine ⟨fun r => ?_, fun _ => by simp; rfl, by simp; rfl, by simp; rfl, by simp; rfl,
    by simp; rfl, by simp; rfl⟩
  rw [getReg_ofParts, MachineState.getReg_setPC, getReg_setReg, getReg_ofParts]
  by_cases h0 : r = .x0
  · subst h0; simp [eq_comm]
  · by_cases hr : rd = r
    · subst hr; simp [h0, updReg]
    · have : regName r ≠ regName rd := fun e => hr (regName_inj e).symm
      simp [h0, Ne.symm hr, updReg, this]

theorem ofParts_setMem (regs : String → BitVec 64) (m : MachineState) (a v : Word) :
    ofParts regs (m.setMem a v) = (ofParts regs m).setMem a v := rfl

theorem toNat_and_63 (x : Word) : x.toNat &&& 63 = x.toNat % 64 :=
  Nat.and_two_pow_sub_one_eq_mod x.toNat 6

theorem toNat_and_31 (x : Word) : x.toNat &&& 31 = x.toNat % 32 :=
  Nat.and_two_pow_sub_one_eq_mod x.toNat 5

theorem mod_two_pow_64_of_lt {n k : Nat} (h : n < 2 ^ k) (hk : k ≤ 64) : n % 18446744073709551616 = n :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hk))

theorem sext32_add (x y : Word) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (x + y)) =
      BitVec.signExtend 64 (x.truncate 32 + y.truncate 32) := by bv_decide

theorem sext32_sub (x y : Word) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (x - y)) =
      BitVec.signExtend 64 (x.truncate 32 - y.truncate 32) := by bv_decide

theorem sext32_lshr_zext (x : Word) (n : Nat) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) >>> n)) =
      BitVec.signExtend 64 (x.truncate 32 >>> n) := by
  congr 1; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.truncate_eq_setWidth]
  by_cases h : n + i < 32
  · simp [h, hi, show n + i < 64 by omega]
  · simp [h]

/-! What `ofParts` leaves alone. -/

@[simp] theorem getMem_ofParts (regs : String → BitVec 64) (m : MachineState) (a : Word) :
    (ofParts regs m).getMem a = m.getMem a := rfl
@[simp] theorem getByte_ofParts (regs : String → BitVec 64) (m : MachineState) (a : Word) :
    (ofParts regs m).getByte a = m.getByte a := rfl
@[simp] theorem getHalfword_ofParts (regs : String → BitVec 64) (m : MachineState) (a : Word) :
    (ofParts regs m).getHalfword a = m.getHalfword a := rfl
@[simp] theorem getWord32_ofParts (regs : String → BitVec 64) (m : MachineState) (a : Word) :
    (ofParts regs m).getWord32 a = m.getWord32 a := rfl
@[simp] theorem noCodeAt_ofParts (regs : String → BitVec 64) (m : MachineState) (a : Word) (w : Nat) :
    noCodeAt (ofParts regs m) a w = noCodeAt m a w := rfl

theorem ite_some_eq_some {α : Type} {c : Prop} [Decidable c] {x y : α} :
    (if c then some x else none) = some y ↔ c ∧ x = y := by
  by_cases h : c <;> simp [h]

theorem ite_some_eq_none {α : Type} {c : Prop} [Decidable c] {x : α} :
    (if c then some x else none) = none ↔ ¬ c := by
  by_cases h : c <;> simp [h]

/-- **Correctness of the translation.** For an operation, the shared operation succeeds exactly
    when SP1's memory check passes, and then agrees with riscv-zkvm's `execInstrBr`. -/
theorem opOf_spec {i : Instr} (hi : opnOk i = true) (regs : String → BitVec 64) (m : MachineState) :
    match (opOf i).eval rvMem regs m with
    | some (r', m') =>
      memOkSp1 (ofParts regs m) i = true ∧ Agree (ofParts r' m') (execInstrBr (ofParts regs m) i)
    | none => memOkSp1 (ofParts regs m) i = false := by
  cases i <;> simp only [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, Bool.or_false,
    Bool.and_true, Bool.false_and, Bool.true_and, Bool.not_true, Bool.and_false, Bool.or_self,
    Bool.false_eq_true] at hi
  all_goals first
    | (refine ⟨by simp [memOkSp1, memAccess], agree_set regs m _ _ ?_⟩
       simp [Expr.eval, BinOp.eval, UnOp.eval, rv_eval regs m, se12, sh, Width.bits, toNat_and_63,
         toNat_and_31, mod_two_pow_64_of_lt (BitVec.isLt _), sext32_add, sext32_sub,
         sext32_lshr_zext, rv64_mulh, rv64_mulhsu, rv64_mulhu, rv64_div, rv64_divu, rv64_rem, rv64_remu])
    | exact ⟨by simp [memOkSp1, memAccess], agree_setPC _ _⟩
    | skip
  -- loads and stores: the access succeeds exactly when SP1's check passes
  all_goals
    simp only [opOf, Op.eval, rvMem, addr, Expr.eval, BinOp.eval, rv_eval regs m, se12, Width.bytes,
      Bool.false_eq_true, ↓reduceIte]
    split
    · next heq =>
      obtain ⟨a, ha, hf⟩ := Option.map_eq_some_iff.mp heq
      clear heq
      obtain ⟨hc, rfl⟩ := ite_some_eq_some.mp ha
      · simp only [Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        simp only [Bool.and_eq_true] at hc
        refine ⟨by simp [memOkSp1, memAccess, hc], ?_⟩
        first
          | exact agree_setPC _ _
          | exact agree_set regs m _ _ (by simp [UnOp.eval, Width.bits])
    · next heq =>
      have hc := ite_some_eq_none.mp (Option.map_eq_none_iff.mp heq)
      · simp only [memOkSp1, memAccess]
        simpa using hc

end MachineChecked.RiscV.Lprog
