/-
  MachineChecked.RiscV.Corres.Regs

  The registers of a straight-line block, one named value per instruction.

  Unfolding `prog.foldl execInstrBr m` and reading a register gives a term in the initial
  registers that is a tree: each value is copied into every later instruction that reads it,
  and `simp` re-traverses the copies. Past a hundred instructions that is too slow.

  Here the block's registers are a valuation `Reg → Word` updated once per instruction
  (`stepRegs`), and `getReg_foldl` says the machine's registers after the block are that
  fold, for *pure* instructions (straight, and not reading the pc). `foldl_stepRegs_gen`
  peels one instruction off the fold and names its result `v` with the equation
  `v = value`, so a proof runs the block as

      regs_run

  ending in a valuation that is a chain of `upd`s over named values, with one
  small equation per instruction. Those equations are what `bv_decide` takes.
-/

import MachineChecked.RiscV.Corres.Block

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64

/-- Straight and not reading the pc: the effect is a function of the registers. -/
def isPure (i : Instr) : Bool :=
  isStraight i && match i with
    | .AUIPC .. => false
    | _ => true

/-- The register a pure instruction writes (`x0` for none). -/
def dst : Instr → Reg
  | .ADD rd .. | .SUB rd .. | .SLL rd .. | .SRL rd .. | .SRA rd .. | .AND rd .. | .OR rd ..
  | .XOR rd .. | .SLT rd .. | .SLTU rd .. | .ADDI rd .. | .ANDI rd .. | .ORI rd .. | .XORI rd ..
  | .SLTI rd .. | .SLTIU rd .. | .SLLI rd .. | .SRLI rd .. | .SRAI rd .. | .LUI rd .. | .MV rd ..
  | .LI rd .. | .ADDIW rd .. | .SUBW rd .. | .SRLW rd .. | .SLLIW rd .. | .SRLIW rd ..
  | .MUL rd .. | .MULH rd .. | .MULHSU rd .. | .MULHU rd .. | .DIV rd .. | .DIVU rd ..
  | .REM rd .. | .REMU rd .. => rd
  | _ => .x0

/-- A machine state with registers `ρ`; nothing else about it is read. -/
def ofRegs (ρ : Reg → Word) : MachineState := { regs := ρ, mem := fun _ => 0, pc := 0 }

/-- The value a pure instruction writes, from registers `ρ`. -/
def val (i : Instr) (ρ : Reg → Word) : Word := (execInstrBr (ofRegs ρ) i).getReg (dst i)

/-- A valuation with one register changed. -/
def upd (ρ : Reg → Word) (r : Reg) (v : Word) : Reg → Word := fun r' => if r' = r then v else ρ r'

/-- One instruction on a valuation. -/
def stepRegs (ρ : Reg → Word) (i : Instr) : Reg → Word :=
  if dst i = .x0 then ρ else upd ρ (dst i) (val i ρ)

/-- The registers of a state, as a valuation. -/
def regsOf' (m : MachineState) : Reg → Word := m.getReg

theorem getReg_ofRegs (ρ : Reg → Word) (r : Reg) :
    (ofRegs ρ).getReg r = if r = .x0 then 0 else ρ r := by
  cases r <;> rfl

theorem getReg_ofRegs_getReg (m : MachineState) (r : Reg) : (ofRegs m.getReg).getReg r = m.getReg r := by
  cases r <;> rfl

theorem stepRegs_apply (ρ : Reg → Word) (i : Instr) (r : Reg) :
    stepRegs ρ i r = if r = dst i ∧ dst i ≠ .x0 then val i ρ else ρ r := by
  unfold stepRegs
  by_cases h0 : dst i = .x0
  · simp [h0]
  · simp only [h0, if_false, upd, ne_eq, not_false_eq_true, and_true]

/-- A pure instruction's effect on the registers is `stepRegs`. -/
theorem getReg_execInstrBr_pure {m : MachineState} {i : Instr} (h : isPure i = true) (r : Reg) :
    (execInstrBr m i).getReg r = stepRegs m.getReg i r := by
  rw [stepRegs_apply]
  cases i <;> simp only [isPure, isStraight, Bool.and_eq_true, Bool.false_and, Bool.and_false,
      Bool.false_eq_true] at h <;>
    simp only [execInstrBr, val, dst, getReg_setReg_ite, MachineState.getReg_setPC,
      getReg_ofRegs_getReg] <;>
    (repeat' split) <;> simp_all

/-- **The registers after a pure block** are the fold of `stepRegs`. -/
theorem getReg_foldl :
    ∀ (prog : List Instr) (m : MachineState), prog.all isPure = true →
      ∀ r, (prog.foldl execInstrBr m).getReg r = (prog.foldl stepRegs m.getReg) r
  | [], _, _, _ => rfl
  | i :: prog, m, hall, r => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [List.foldl_cons, List.foldl_cons, getReg_foldl prog _ hall.2]
    have : (execInstrBr m i).getReg = stepRegs m.getReg i :=
      funext (getReg_execInstrBr_pure hall.1)
    rw [this]

/-- Peel one instruction off a fold of `stepRegs`, naming the value it writes. -/
theorem foldl_stepRegs_gen {P : (Reg → Word) → Prop} {ρ : Reg → Word} {i : Instr}
    {rest : List Instr}
    (h : ∀ v, v = val i ρ →
      P (rest.foldl stepRegs (if dst i = .x0 then ρ else upd ρ (dst i) v))) :
    P ((i :: rest).foldl stepRegs ρ) :=
  h _ rfl

/-- Run a literal block on a valuation: peel each instruction off `List.foldl stepRegs`, name
    the value it writes `v` with its equation `hv` in terms of the earlier names, and leave the
    goal at the final valuation. -/
macro "regs_run" : tactic => `(tactic| (
  repeat (
    apply foldl_stepRegs_gen
    intro v hv
    simp only [val, execInstrBr, dst, getReg_setReg_ite, getReg_ofRegs, MachineState.getReg_setPC,
      upd, reduceCtorEq, if_false, if_true, signExtend12, getReg_x0', ne_eq, not_false_eq_true,
      and_true, and_false] at hv
    dsimp only [dst])
  simp only [List.foldl_nil, upd, reduceCtorEq, if_false, if_true]))

end MachineChecked.RiscV
