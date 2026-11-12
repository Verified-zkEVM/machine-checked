/-
  MachineChecked.RiscV.Sym.Exec

  `execInstrBr` unfolded one constructor at a time, and the projection facts
  the symbolic executor reads off the result.

  Every instruction the model executes lands in one of a few shapes:

  * `(s.setReg rd v).setPC p`             -- ALU, loads, jumps, `LI`, `MV`
  * `(s.setMem a v).setPC p`              -- `SD`
  * `(s.setWord32/Halfword/Byte a v).setPC p` -- `SW`, `SH`, `SB`
  * `s.setPC p`                           -- branches, `NOP`, `FENCE`

  The executor rewrites with the `exec_*` equation for the constructor it
  fetched and then applies the `*_shape` projections below, which is one lemma
  application per fact rather than a `simp` over the state. Everything here is
  `rfl` or a one-line consequence of the upstream `MachineState` simp set.
-/

import MachineChecked.RiscV.Sym.Core

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

/-! ## Unfold equations -/

section unfold
variable (s : MachineState)

theorem exec_ADD (rd rs1 rs2 : Reg) :
    execInstrBr s (.ADD rd rs1 rs2) = (s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4) := rfl
theorem exec_SUB (rd rs1 rs2 : Reg) :
    execInstrBr s (.SUB rd rs1 rs2) = (s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4) := rfl
theorem exec_SLL (rd rs1 rs2 : Reg) :
    execInstrBr s (.SLL rd rs1 rs2) = (s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4) := rfl
theorem exec_SRL (rd rs1 rs2 : Reg) :
    execInstrBr s (.SRL rd rs1 rs2) = (s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4) := rfl
theorem exec_SRA (rd rs1 rs2 : Reg) :
    execInstrBr s (.SRA rd rs1 rs2) = (s.setReg rd (BitVec.sshiftRight (s.getReg rs1) ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4) := rfl
theorem exec_AND (rd rs1 rs2 : Reg) :
    execInstrBr s (.AND rd rs1 rs2) = (s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (s.pc + 4) := rfl
theorem exec_OR (rd rs1 rs2 : Reg) :
    execInstrBr s (.OR rd rs1 rs2) = (s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4) := rfl
theorem exec_XOR (rd rs1 rs2 : Reg) :
    execInstrBr s (.XOR rd rs1 rs2) = (s.setReg rd (s.getReg rs1 ^^^ s.getReg rs2)).setPC (s.pc + 4) := rfl
theorem exec_SLT (rd rs1 rs2 : Reg) :
    execInstrBr s (.SLT rd rs1 rs2) = (s.setReg rd (if BitVec.slt (s.getReg rs1) (s.getReg rs2) then 1 else 0)).setPC (s.pc + 4) := rfl
theorem exec_SLTU (rd rs1 rs2 : Reg) :
    execInstrBr s (.SLTU rd rs1 rs2) = (s.setReg rd (if BitVec.ult (s.getReg rs1) (s.getReg rs2) then 1 else 0)).setPC (s.pc + 4) := rfl
theorem exec_ADDI (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrBr s (.ADDI rd rs1 imm) = (s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4) := rfl
theorem exec_ANDI (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrBr s (.ANDI rd rs1 imm) = (s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4) := rfl
theorem exec_ORI (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrBr s (.ORI rd rs1 imm) = (s.setReg rd (s.getReg rs1 ||| signExtend12 imm)).setPC (s.pc + 4) := rfl
theorem exec_XORI (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrBr s (.XORI rd rs1 imm) = (s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4) := rfl
theorem exec_SLTI (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrBr s (.SLTI rd rs1 imm) = (s.setReg rd (if BitVec.slt (s.getReg rs1) (signExtend12 imm) then 1 else 0)).setPC (s.pc + 4) := rfl
theorem exec_SLTIU (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrBr s (.SLTIU rd rs1 imm) = (s.setReg rd (if BitVec.ult (s.getReg rs1) (signExtend12 imm) then 1 else 0)).setPC (s.pc + 4) := rfl
theorem exec_SLLI (rd rs1 : Reg) (sh : BitVec 6) :
    execInstrBr s (.SLLI rd rs1 sh) = (s.setReg rd (s.getReg rs1 <<< sh.toNat)).setPC (s.pc + 4) := rfl
theorem exec_SRLI (rd rs1 : Reg) (sh : BitVec 6) :
    execInstrBr s (.SRLI rd rs1 sh) = (s.setReg rd (s.getReg rs1 >>> sh.toNat)).setPC (s.pc + 4) := rfl
theorem exec_SRAI (rd rs1 : Reg) (sh : BitVec 6) :
    execInstrBr s (.SRAI rd rs1 sh) = (s.setReg rd (BitVec.sshiftRight (s.getReg rs1) sh.toNat)).setPC (s.pc + 4) := rfl
theorem exec_LUI (rd : Reg) (imm : BitVec 20) :
    execInstrBr s (.LUI rd imm) = (s.setReg rd (((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_AUIPC (rd : Reg) (imm : BitVec 20) :
    execInstrBr s (.AUIPC rd imm) = (s.setReg rd (s.pc + ((imm.zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_LD (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.LD rd rs1 off) = (s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (s.pc + 4) := rfl
theorem exec_SD (rs1 rs2 : Reg) (off : BitVec 12) :
    execInstrBr s (.SD rs1 rs2 off) = (s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4) := rfl
theorem exec_LW (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.LW rd rs1 off) = (s.setReg rd ((s.getWord32 (s.getReg rs1 + signExtend12 off)).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_LWU (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.LWU rd rs1 off) = (s.setReg rd ((s.getWord32 (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_SW (rs1 rs2 : Reg) (off : BitVec 12) :
    execInstrBr s (.SW rs1 rs2 off) = (s.setWord32 (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 32)).setPC (s.pc + 4) := rfl
theorem exec_LB (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.LB rd rs1 off) = (s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_LH (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.LH rd rs1 off) = (s.setReg rd ((s.getHalfword (s.getReg rs1 + signExtend12 off)).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_LBU (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.LBU rd rs1 off) = (s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_LHU (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.LHU rd rs1 off) = (s.setReg rd ((s.getHalfword (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_SB (rs1 rs2 : Reg) (off : BitVec 12) :
    execInstrBr s (.SB rs1 rs2 off) = (s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4) := rfl
theorem exec_SH (rs1 rs2 : Reg) (off : BitVec 12) :
    execInstrBr s (.SH rs1 rs2 off) = (s.setHalfword (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 16)).setPC (s.pc + 4) := rfl
theorem exec_BEQ (rs1 rs2 : Reg) (off : BitVec 13) :
    execInstrBr s (.BEQ rs1 rs2 off) = if s.getReg rs1 == s.getReg rs2 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4) := rfl
theorem exec_BNE (rs1 rs2 : Reg) (off : BitVec 13) :
    execInstrBr s (.BNE rs1 rs2 off) = if s.getReg rs1 != s.getReg rs2 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4) := rfl
theorem exec_BLT (rs1 rs2 : Reg) (off : BitVec 13) :
    execInstrBr s (.BLT rs1 rs2 off) = if BitVec.slt (s.getReg rs1) (s.getReg rs2) then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4) := rfl
theorem exec_BGE (rs1 rs2 : Reg) (off : BitVec 13) :
    execInstrBr s (.BGE rs1 rs2 off) = if ¬ BitVec.slt (s.getReg rs1) (s.getReg rs2) then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4) := rfl
theorem exec_BLTU (rs1 rs2 : Reg) (off : BitVec 13) :
    execInstrBr s (.BLTU rs1 rs2 off) = if BitVec.ult (s.getReg rs1) (s.getReg rs2) then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4) := rfl
theorem exec_BGEU (rs1 rs2 : Reg) (off : BitVec 13) :
    execInstrBr s (.BGEU rs1 rs2 off) = if ¬ BitVec.ult (s.getReg rs1) (s.getReg rs2) then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4) := rfl
theorem exec_JAL (rd : Reg) (off : BitVec 21) :
    execInstrBr s (.JAL rd off) = (s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 off) := rfl
theorem exec_JALR (rd rs1 : Reg) (off : BitVec 12) :
    execInstrBr s (.JALR rd rs1 off) = (s.setReg rd (s.pc + 4)).setPC ((s.getReg rs1 + signExtend12 off) &&& ~~~1#64) := rfl
theorem exec_MV (rd rs : Reg) :
    execInstrBr s (.MV rd rs) = (s.setReg rd (s.getReg rs)).setPC (s.pc + 4) := rfl
theorem exec_LI (rd : Reg) (imm : Word) :
    execInstrBr s (.LI rd imm) = (s.setReg rd imm).setPC (s.pc + 4) := rfl
theorem exec_NOP : execInstrBr s .NOP = s.setPC (s.pc + 4) := rfl
theorem exec_FENCE : execInstrBr s .FENCE = s.setPC (s.pc + 4) := rfl
theorem exec_ECALL : execInstrBr s .ECALL = s.setPC (s.pc + 4) := rfl
theorem exec_SUBW (rd rs1 rs2 : Reg) :
    execInstrBr s (.SUBW rd rs1 rs2) = (s.setReg rd ((((s.getReg rs1).truncate 32) - ((s.getReg rs2).truncate 32) : BitVec 32).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_SRLW (rd rs1 rs2 : Reg) :
    execInstrBr s (.SRLW rd rs1 rs2) = (s.setReg rd ((((s.getReg rs1).truncate 32) >>> ((s.getReg rs2).toNat % 32) : BitVec 32).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_SLLIW (rd rs1 : Reg) (sh : BitVec 5) :
    execInstrBr s (.SLLIW rd rs1 sh) = (s.setReg rd ((((s.getReg rs1).truncate 32) <<< sh.toNat : BitVec 32).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_SRLIW (rd rs1 : Reg) (sh : BitVec 5) :
    execInstrBr s (.SRLIW rd rs1 sh) = (s.setReg rd ((((s.getReg rs1).truncate 32) >>> sh.toNat : BitVec 32).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_ADDIW (rd rs1 : Reg) (imm : BitVec 12) :
    execInstrBr s (.ADDIW rd rs1 imm) = (s.setReg rd ((((s.getReg rs1).truncate 32) + ((signExtend12 imm).truncate 32) : BitVec 32).signExtend 64)).setPC (s.pc + 4) := rfl
theorem exec_MUL (rd rs1 rs2 : Reg) :
    execInstrBr s (.MUL rd rs1 rs2) = (s.setReg rd (s.getReg rs1 * s.getReg rs2)).setPC (s.pc + 4) := rfl
theorem exec_MULH (rd rs1 rs2 : Reg) :
    execInstrBr s (.MULH rd rs1 rs2) = (s.setReg rd (rv64_mulh (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4) := rfl
theorem exec_MULHSU (rd rs1 rs2 : Reg) :
    execInstrBr s (.MULHSU rd rs1 rs2) = (s.setReg rd (rv64_mulhsu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4) := rfl
theorem exec_MULHU (rd rs1 rs2 : Reg) :
    execInstrBr s (.MULHU rd rs1 rs2) = (s.setReg rd (rv64_mulhu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4) := rfl
theorem exec_DIV (rd rs1 rs2 : Reg) :
    execInstrBr s (.DIV rd rs1 rs2) = (s.setReg rd (rv64_div (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4) := rfl
theorem exec_DIVU (rd rs1 rs2 : Reg) :
    execInstrBr s (.DIVU rd rs1 rs2) = (s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4) := rfl
theorem exec_REM (rd rs1 rs2 : Reg) :
    execInstrBr s (.REM rd rs1 rs2) = (s.setReg rd (rv64_rem (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4) := rfl
theorem exec_REMU (rd rs1 rs2 : Reg) :
    execInstrBr s (.REMU rd rs1 rs2) = (s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4) := rfl

end unfold

/-! ## Projections off the three shapes -/

section shapes
variable {s : MachineState}

-- `(s.setReg rd v).setPC p`

theorem regShape_getReg_eq {rd : Reg} {v p : Word} (h : rd ≠ .x0) :
    ((s.setReg rd v).setPC p).getReg rd = v := by
  rw [MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq h
theorem regShape_getReg_ne {rd r : Reg} {v p : Word} (h : rd ≠ r) :
    ((s.setReg rd v).setPC p).getReg r = s.getReg r := by
  rw [MachineState.getReg_setPC]; exact MachineState.getReg_setReg_ne s rd r v h
theorem regShape_pc {rd : Reg} {v p : Word} : ((s.setReg rd v).setPC p).pc = p := rfl
theorem regShape_mem {rd : Reg} {v p : Word} : ((s.setReg rd v).setPC p).mem = s.mem := by
  cases rd <;> rfl
theorem regShape_getMem {rd : Reg} {v p a : Word} :
    ((s.setReg rd v).setPC p).getMem a = s.getMem a := by
  simp only [MachineState.getMem, regShape_mem]
theorem regShape_privateInput {rd : Reg} {v p : Word} :
    ((s.setReg rd v).setPC p).privateInput = s.privateInput := by cases rd <;> rfl
theorem regShape_committed {rd : Reg} {v p : Word} :
    ((s.setReg rd v).setPC p).committed = s.committed := by cases rd <;> rfl

-- `(s.setMem a v).setPC p`

theorem memShape_getReg {a v p : Word} {r : Reg} : ((s.setMem a v).setPC p).getReg r = s.getReg r := by
  cases r <;> rfl
theorem memShape_pc {a v p : Word} : ((s.setMem a v).setPC p).pc = p := rfl
theorem memShape_getMem_eq {a v p : Word} : ((s.setMem a v).setPC p).getMem a = v := by
  simp [MachineState.getMem, MachineState.setMem, MachineState.setPC]
theorem memShape_getMem_ne {a v p a' : Word} (h : a' ≠ a) :
    ((s.setMem a v).setPC p).getMem a' = s.getMem a' := by
  simp [MachineState.getMem, MachineState.setMem, MachineState.setPC, h]
theorem memShape_mem {a v p : Word} :
    ((s.setMem a v).setPC p).mem = fun a' => if a' == a then v else s.mem a' := rfl
theorem memShape_privateInput {a v p : Word} :
    ((s.setMem a v).setPC p).privateInput = s.privateInput := rfl
theorem memShape_committed {a v p : Word} :
    ((s.setMem a v).setPC p).committed = s.committed := rfl

-- `s.setPC p`

theorem pcShape_getReg {p : Word} {r : Reg} : (s.setPC p).getReg r = s.getReg r := by cases r <;> rfl
theorem pcShape_pc {p : Word} : (s.setPC p).pc = p := rfl
theorem pcShape_getMem {p a : Word} : (s.setPC p).getMem a = s.getMem a := rfl
theorem pcShape_mem {p : Word} : (s.setPC p).mem = s.mem := rfl
theorem pcShape_privateInput {p : Word} : (s.setPC p).privateInput = s.privateInput := rfl
theorem pcShape_committed {p : Word} : (s.setPC p).committed = s.committed := rfl

-- Sub-dword stores unfold to a `setMem` of the containing doubleword.

theorem setByte_eq (a : Word) (b : BitVec 8) :
    s.setByte a b = s.setMem (alignToDword a) (replaceByte (s.getMem (alignToDword a)) (byteOffset a) b) := rfl
theorem setHalfword_eq (a : Word) (h : BitVec 16) :
    s.setHalfword a h = s.setMem (alignToDword a) (replaceHalfword (s.getMem (alignToDword a)) (byteOffset a / 2) h) := rfl
theorem setWord32_eq (a : Word) (v : BitVec 32) :
    s.setWord32 a v = s.setMem (alignToDword a) (replaceWord32 (s.getMem (alignToDword a)) (byteOffset a / 4) v) := rfl
theorem getByte_eq (a : Word) : s.getByte a = extractByte (s.getMem (alignToDword a)) (byteOffset a) := rfl
theorem getHalfword_eq (a : Word) : s.getHalfword a = extractHalfword (s.getMem (alignToDword a)) (byteOffset a / 2) := rfl
theorem getWord32_eq (a : Word) : s.getWord32 a = extractWord32 (s.getMem (alignToDword a)) (byteOffset a / 4) := rfl

end shapes

/-! ## Branch direction -/

theorem ite_true_of {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := ite_eq_left h
theorem ite_false_of {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := ite_eq_right h

theorem beq_word_true {a b : Word} (h : a = b) : (a == b) = true := by subst h; simp
theorem beq_word_false {a b : Word} (h : a ≠ b) : (a == b) = false := by simpa using h
theorem bne_word_true {a b : Word} (h : a ≠ b) : (a != b) = true := by simpa using h
theorem bne_word_false {a b : Word} (h : a = b) : (a != b) = false := by subst h; simp

/-! ## Memory-access side conditions -/

/-- `memOkSp1` for a load: in range and aligned. -/
theorem memOk_LD {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (h : isValidDwordAccessSp1 (s.getReg rs1 + signExtend12 off) = true) :
    memOkSp1 s (.LD rd rs1 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor, isValidDwordAccessSp1] at *
  simp_all
theorem memOk_SD {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (h : isValidDwordAccessSp1 (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 8 = true) :
    memOkSp1 s (.SD rs1 rs2 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor, isValidDwordAccessSp1] at *
  simp_all
theorem memOk_LW {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true)
    (ha : isAligned4 (s.getReg rs1 + signExtend12 off) = true) :
    memOkSp1 s (.LW rd rs1 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_LWU {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true)
    (ha : isAligned4 (s.getReg rs1 + signExtend12 off) = true) :
    memOkSp1 s (.LWU rd rs1 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_SW {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true)
    (ha : isAligned4 (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 4 = true) :
    memOkSp1 s (.SW rs1 rs2 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_LH {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true)
    (ha : isAligned2 (s.getReg rs1 + signExtend12 off) = true) :
    memOkSp1 s (.LH rd rs1 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_LHU {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true)
    (ha : isAligned2 (s.getReg rs1 + signExtend12 off) = true) :
    memOkSp1 s (.LHU rd rs1 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_SH {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true)
    (ha : isAligned2 (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 2 = true) :
    memOkSp1 s (.SH rs1 rs2 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_LB {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true) :
    memOkSp1 s (.LB rd rs1 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_LBU {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true) :
    memOkSp1 s (.LBU rd rs1 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all
theorem memOk_SB {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (h : isValidMemAddrSp1 (s.getReg rs1 + signExtend12 off) = true)
    (hcode : noCodeAt s (s.getReg rs1 + signExtend12 off) 1 = true) :
    memOkSp1 s (.SB rs1 rs2 off) = true := by
  simp only [memOkSp1, memAccess, alignedFor] at *; simp_all

/-- `align4` as `Nat` arithmetic. -/
theorem align4_toNat (y : Word) : (align4 y).toNat = y.toNat - y.toNat % 4 := by
  have hlow : (y &&& 3#64).toNat = y.toNat % 4 := by
    rw [BitVec.toNat_and]; simp; exact Nat.and_two_pow_sub_one_eq_mod y.toNat 2
  have hdisj : (y &&& ~~~3#64) &&& (y &&& 3#64) = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases (3#64).getLsbD i <;> cases y.getLsbD i <;> simp
  have hsum : (y &&& ~~~3#64) + (y &&& 3#64) = y := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, ← BitVec.and_or_distrib_left]
    have : (~~~3#64 ||| 3#64) = BitVec.allOnes 64 := by decide
    rw [this, BitVec.and_allOnes]
  have hle : (y &&& ~~~3#64).toNat ≤ y.toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_left
  have h := congrArg BitVec.toNat hsum
  rw [BitVec.toNat_add, hlow] at h
  have hy := y.isLt
  unfold align4
  omega

/-- A store whose whole extent lies outside the code window hits no code. -/
theorem noCodeAt_of_codeWithin {lo hi : Nat} {s : MachineState} (hcw : CodeWithin lo hi s)
    (a : Word) (w : Nat) (hw : 0 < w)
    (hout : a.toNat + w ≤ lo ∨ hi ≤ a.toNat - a.toNat % 4)
    (hnowrap : a.toNat + w ≤ 2 ^ 64) :
    noCodeAt s a w = true := by
  unfold noCodeAt
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  simp only [Option.isNone_iff_eq_none]
  have hlo := align4_toNat a
  have hhi := align4_toNat (a + BitVec.ofNat 64 (w - 1))
  have ha := a.isLt
  have hw1 : (a + BitVec.ofNat 64 (w - 1)).toNat = a.toNat + (w - 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w - 1) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hw1] at hhi
  have hsub : (align4 (a + BitVec.ofNat 64 (w - 1)) - align4 a).toNat
      = (align4 (a + BitVec.ofNat 64 (w - 1))).toNat - (align4 a).toNat := by
    rw [BitVec.toNat_sub]
    have h1 := (align4 a).isLt
    have h2 := (align4 (a + BitVec.ofNat 64 (w - 1))).isLt
    rw [show 2 ^ 64 - (align4 a).toNat + (align4 (a + BitVec.ofNat 64 (w - 1))).toNat
        = ((align4 (a + BitVec.ofNat 64 (w - 1))).toNat - (align4 a).toNat) + 2 ^ 64 by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hsub] at hi
  have hx : (align4 a + BitVec.ofNat 64 (4 * i)).toNat = (align4 a).toNat + 4 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * i) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  cases hc : s.code (align4 a + BitVec.ofNat 64 (4 * i)) with
  | none => rfl
  | some _ =>
    exfalso
    have hb := hcw _ (by rw [hc]; exact Option.some_ne_none _)
    rw [hx] at hb
    omega

/-- Unsigned-range check as a `Nat` bound. -/
theorem isValidMemAddrSp1_of_lt {a : Word} (h : a.toNat < SP1_MAX_MEMORY) :
    isValidMemAddrSp1 a = true := by
  simp [isValidMemAddrSp1, h]
theorem isValidDwordAccessSp1_of {a : Word} (h : a.toNat < SP1_MAX_MEMORY) (h8 : a.toNat % 8 = 0) :
    isValidDwordAccessSp1 a = true := by
  simp [isValidDwordAccessSp1, isValidMemAddrSp1, isAligned8, h, h8]
theorem isAligned4_of {a : Word} (h : a.toNat % 4 = 0) : isAligned4 a = true := by simp [isAligned4, h]
theorem isAligned2_of {a : Word} (h : a.toNat % 2 = 0) : isAligned2 a = true := by simp [isAligned2, h]

end MachineChecked.RiscV.Sym
