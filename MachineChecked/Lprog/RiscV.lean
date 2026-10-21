/-
  MachineChecked.Lprog.RiscV

  The RISC-V instruction set of Lprog, on riscv-zkvm.

  An operation is a riscv-zkvm `Instr` that does not transfer control: a pure instruction or a
  load or store. It runs by riscv-zkvm's own `execInstrBr`, behind the SP1 memory check
  `memOkSp1`, so an Lprog step and a `stepSp1` step agree (`rvIsa`). The state beside the
  registers is a riscv-zkvm `MachineState`, whose registers and pc are ignored; registers are
  named `x0`..`x31`. Conditions are the six RISC-V comparisons (`cmp "eq"` etc.).

  `Agree t u` says two machine states agree on everything an instruction reads or writes other
  than the pc: registers as `getReg` reads them, memory, code and the I/O fields. A pure or
  memory instruction keeps it (`Agree.execInstrBr`), and `memOkSp1` cannot tell such states
  apart (`Agree.memOkSp1`).
-/

import MachineChecked.Lprog.Sem
import MachineChecked.RiscV.Corres.Run
import MachineChecked.RiscV.Corres.Regs

namespace MachineChecked.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym

/-- The name of a register in Lprog. -/
def regName (r : Reg) : String := toString r

/-- The 32 registers. -/
def allRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16,
    .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

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

/-- An operation: pure, or a load or store. -/
def opnOk (i : Instr) : Bool := isPure i || (i.isMemAccess && !isCSRS i)

/-- The comparison a condition names. -/
def cmpEval (op : String) (a b : BitVec 64) : Option Bool :=
  if op = "eq" then some (a == b)
  else if op = "ne" then some (a != b)
  else if op = "lt" then some (BitVec.slt a b)
  else if op = "ge" then some (!BitVec.slt a b)
  else if op = "ltu" then some (BitVec.ult a b)
  else if op = "geu" then some (!BitVec.ult a b)
  else none

/-- A register operand's value; `x0` reads zero. -/
def regVal (regs : String → BitVec 64) : LOperand → Option (BitVec 64)
  | .reg n => match regOfName n with
    | some .x0 => some 0
    | _ => some (regs n)
  | _ => none

/-- **The RISC-V instruction set.** -/
abbrev rvIsa : Isa where
  Op := Instr
  M := MachineState
  opn _ i _ regs m :=
    let t := ofParts regs m
    if opnOk i && memOkSp1 t i then
      let t' := execInstrBr t i
      some (regsOf regs t', t')
    else none
  cond c regs _ := match c with
    | .cmp op a b => do
      let va ← regVal regs a
      let vb ← regVal regs b
      cmpEval op va vb
    | _ => none

/-! ## Agreement -/

section Fields

variable (s : MachineState)

/-! What each update leaves alone. -/

@[simp] theorem code_setReg' (r : Reg) (v : Word) : (s.setReg r v).code = s.code := by cases r <;> rfl
@[simp] theorem committed_setReg' (r : Reg) (v : Word) : (s.setReg r v).committed = s.committed := by
  cases r <;> rfl
@[simp] theorem publicValues_setReg' (r : Reg) (v : Word) :
    (s.setReg r v).publicValues = s.publicValues := by cases r <;> rfl
@[simp] theorem privateInput_setReg' (r : Reg) (v : Word) :
    (s.setReg r v).privateInput = s.privateInput := by cases r <;> rfl
@[simp] theorem inputBufBase_setReg' (r : Reg) (v : Word) :
    (s.setReg r v).inputBufBase = s.inputBufBase := by cases r <;> rfl
@[simp] theorem getMem_setReg' (r : Reg) (v a : Word) : (s.setReg r v).getMem a = s.getMem a := by
  cases r <;> rfl

@[simp] theorem code_setPC'' (v : Word) : (s.setPC v).code = s.code := rfl
@[simp] theorem committed_setPC' (v : Word) : (s.setPC v).committed = s.committed := rfl
@[simp] theorem publicValues_setPC' (v : Word) : (s.setPC v).publicValues = s.publicValues := rfl
@[simp] theorem privateInput_setPC' (v : Word) : (s.setPC v).privateInput = s.privateInput := rfl
@[simp] theorem inputBufBase_setPC' (v : Word) : (s.setPC v).inputBufBase = s.inputBufBase := rfl
@[simp] theorem getMem_setPC' (v a : Word) : (s.setPC v).getMem a = s.getMem a := rfl

@[simp] theorem code_setMem' (a v : Word) : (s.setMem a v).code = s.code := rfl
@[simp] theorem committed_setMem' (a v : Word) : (s.setMem a v).committed = s.committed := rfl
@[simp] theorem publicValues_setMem' (a v : Word) : (s.setMem a v).publicValues = s.publicValues := rfl
@[simp] theorem privateInput_setMem' (a v : Word) : (s.setMem a v).privateInput = s.privateInput := rfl
@[simp] theorem inputBufBase_setMem' (a v : Word) : (s.setMem a v).inputBufBase = s.inputBufBase := rfl

theorem getMem_setMem_ite (a v a' : Word) :
    (s.setMem a v).getMem a' = if a' = a then v else s.getMem a' := by
  simp [MachineState.getMem, MachineState.setMem]

end Fields

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
    simp [RiscvZkvm.Rv64.execInstrBr, getReg_setReg_ite, getReg_setMem', getMem_setMem_ite,
      MachineState.setByte, MachineState.setHalfword, MachineState.setWord32, MachineState.getByte,
      MachineState.getHalfword, MachineState.getWord32, hr, hm, hc, h1, h2, h3, h4]

end MachineChecked.Lprog
