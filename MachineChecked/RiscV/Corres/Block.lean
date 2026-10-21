/-
  MachineChecked.RiscV.Corres.Block

  Straight-line code on riscv-zkvm: the counterpart of catcrypt-compiler's `steps_block`
  (`RiscvPc64`, rv64 stack), stated over `stepSp1` instead of a second machine.

  An instruction is *straight* when it writes at most one register and falls through to
  `pc + 4`: no memory access, no control transfer, no system call. A block of straight
  instructions loaded at the pc runs, one `stepSp1` per instruction, to the fold of
  `execInstrBr` over it (`stepsSp1_straight`). Its effect is then a term in the initial
  registers, which `simp` evaluates (`getReg_setReg`) and `bv_decide` can reason about.
-/

import MachineChecked.RiscV.Corres
import MachineChecked.RiscV.Sym.Core

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV.Sym

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

/-- A straight instruction advances the pc by 4. -/
theorem pc_execInstrBr_straight {s : MachineState} {i : Instr} (h : isStraight i = true) :
    (execInstrBr s i).pc = s.pc + 4 := by
  cases i <;> simp_all [isStraight, execInstrBr, MachineState.setPC]

/-- A straight instruction leaves the code map alone. -/
theorem code_execInstrBr_straight {s : MachineState} {i : Instr} (h : isStraight i = true) :
    (execInstrBr s i).code = s.code := by
  cases i <;> simp_all [isStraight, execInstrBr]

/-- **A straight-line block.** If the code map holds the straight instructions `prog` from
    the pc on, `prog.length` steps of `stepSp1` run the fold of `execInstrBr` over it. -/
theorem stepsSp1_straight :
    ∀ (prog : List Instr) (s : MachineState),
      (∀ i, (hi : i < prog.length) → s.code (s.pc + BitVec.ofNat 64 (4 * i)) = some prog[i]) →
      prog.all isStraight = true →
      stepsSp1 prog.length s = some (prog.foldl execInstrBr s)
  | [], _, _, _ => rfl
  | i :: prog, s, hcode, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have hfetch : s.code s.pc = some i := by
      have := hcode 0 (by simp)
      simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.getElem_cons_zero]
        using this
    have hstep : stepSp1 s = some (execInstrBr s i) :=
      stepSp1_plain hfetch (isStraight_isMemAccess hall.1)
        (isStraight_ne_ecall hall.1) (isStraight_ne_ebreak hall.1)
    rw [List.length_cons, stepsSp1_succ_of_step hstep, List.foldl_cons]
    refine stepsSp1_straight prog _ ?_ hall.2
    intro j hj
    rw [code_execInstrBr_straight hall.1, pc_execInstrBr_straight hall.1]
    have := hcode (j + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    rw [← this]
    rw [BitVec.add_assoc, show 4 * (j + 1) = 4 + 4 * j by omega, BitVec.ofNat_add]
    rfl

/-! ## Evaluating a block's registers

With literal registers, these two rewrite a read through a chain of writes to the value
written last, or to the initial register; `x0` reads as zero. -/

theorem getReg_setReg_ite (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r = r' ∧ r ≠ .x0 then v else s.getReg r' := by
  by_cases h : r = r'
  · subst h
    by_cases h0 : r = .x0
    · subst h0; rfl
    · rw [if_pos ⟨rfl, h0⟩, MachineState.getReg_setReg_eq h0]
  · rw [if_neg (fun h' => h h'.1), MachineState.getReg_setReg_ne _ _ _ _ h]

theorem getReg_x0' (s : MachineState) : s.getReg .x0 = 0 := rfl

theorem getReg_setMem' (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

theorem pc_setPC' (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl

theorem getReg_setByte' (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by cases r <;> rfl

/-- A straight block advances the pc by four bytes per instruction. -/
theorem pc_foldl_straight :
    ∀ (prog : List Instr) (s : MachineState), prog.all isStraight = true →
      (prog.foldl execInstrBr s).pc = s.pc + BitVec.ofNat 64 (4 * prog.length)
  | [], s, _ => by simp
  | i :: prog, s, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [List.foldl_cons, pc_foldl_straight prog _ hall.2, pc_execInstrBr_straight hall.1,
      BitVec.add_assoc, List.length_cons, show 4 * (prog.length + 1) = 4 + 4 * prog.length by omega,
      BitVec.ofNat_add]
    rfl

/-- A straight block leaves the code map alone. -/
theorem code_foldl_straight :
    ∀ (prog : List Instr) (s : MachineState), prog.all isStraight = true →
      (prog.foldl execInstrBr s).code = s.code
  | [], _, _ => rfl
  | i :: prog, s, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [List.foldl_cons, code_foldl_straight prog _ hall.2, code_execInstrBr_straight hall.1]

/-- The code map holds `prog` at `base`, as a case's `Image` module states it. -/
theorem codeFrom_of_codeAt {base : Word} {prog : List Instr} {s : MachineState}
    (hc : CodeAt base (prog.map some) s) (hpc : s.pc = base) :
    ∀ i, (hi : i < prog.length) → s.code (s.pc + BitVec.ofNat 64 (4 * i)) = some prog[i] := by
  intro i hi
  rw [hpc, hc i (by simpa using hi)]
  simp [hi]

/-! ## One instruction at a time

A correspondence's run, `∃ t, stepsSp1 k s = some t ∧ Q t`, built forward one instruction at a
time: a plain step, a memory step with its `memOkSp1` side condition, and the end. -/

theorem reach_done {Q : MachineState → Prop} {s : MachineState} (h : Q s) :
    ∃ t, stepsSp1 0 s = some t ∧ Q t := ⟨s, rfl, h⟩

theorem reach_plain {Q : MachineState → Prop} {s : MachineState} {i : Instr} {k : Nat}
    (hf : s.code s.pc = some i) (hm : i.isMemAccess = false) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (h : ∃ t, stepsSp1 k (execInstrBr s i) = some t ∧ Q t) :
    ∃ t, stepsSp1 (k + 1) s = some t ∧ Q t := by
  rwa [stepsSp1_succ_of_step (stepSp1_plain hf hm he hb)]

theorem reach_mem {Q : MachineState → Prop} {s : MachineState} {i : Instr} {k : Nat}
    (hf : s.code s.pc = some i) (hm : i.isMemAccess = true) (hc : isCSRS i = false)
    (hok : memOkSp1 s i = true) (h : ∃ t, stepsSp1 k (execInstrBr s i) = some t ∧ Q t) :
    ∃ t, stepsSp1 (k + 1) s = some t ∧ Q t := by
  rwa [stepsSp1_succ_of_step (stepSp1_mem hf hm hc hok)]

namespace Corres

variable {AState : Type} {SR : MachineState → AState → Prop} {P : AState → Prop}
  {fa : AState → AState}

/-- **A correspondence for a straight-line block.** If every related state holds the block
    at its pc, and the fold of `execInstrBr` over the block from a related state is related
    to the abstract result, the block corresponds to `fa` in `prog.length` steps. -/
theorem straight (prog : List Instr) (hall : prog.all isStraight = true)
    (hcode : ∀ m a, SR m a → P a →
      ∀ i, (hi : i < prog.length) → m.code (m.pc + BitVec.ofNat 64 (4 * i)) = some prog[i])
    (hpost : ∀ m a, SR m a → P a → SR (prog.foldl execInstrBr m) (fa a)) :
    Corres SR P fa prog.length := by
  intro m a hSR hP
  exact ⟨_, stepsSp1_straight prog m (hcode m a hSR hP) hall, hpost m a hSR hP⟩

end Corres

end MachineChecked.RiscV
