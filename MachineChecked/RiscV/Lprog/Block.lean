/-
  MachineChecked.RiscV.Lprog.Block

  Straight-line code: the counterpart of catcrypt-compiler's `steps_block` (`RiscvPc64`, rv64
  stack).

  A machine holding a block of *pure* instructions (straight, and not reading the pc) at its pc
  reaches, over `stepSp1`, the fold of `execInstrBr` over the block, at the end of the block
  (`reaches_block`); as a correspondence (`corres_block`), a contract in continuation form. A
  block is a piece of a function, not a function, so it is run over the machine rather than
  lifted: under partial correctness a lifted body cannot hand over to code outside the program
  where it ends.

  The fold's effect is then a term in the initial registers. Unfolding it and reading a
  register gives a tree in which each value is copied into every later instruction that reads
  it, which past a hundred instructions is too slow for `simp`. So the block's registers are
  also given as a valuation `Reg → Word` updated once per instruction (`stepRegs`):
  `getReg_foldl` says the machine's registers after the block are that fold, and the tactic
  `regs_run` runs a literal block on it, naming each instruction's result `v` with one small
  equation `hv`, the facts `bv_decide` takes.
-/

import MachineChecked.RiscV.Lprog.Transfer
import MachineChecked.Ascent.Corres

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog
open MachineChecked.Ascent (Reaches Corres)

theorem opnOk_of_isPure {i : Instr} (h : isPure i = true) : opnOk i = true := by
  simp [opnOk, h]

/-- **A pure block.** A machine holding the pure block `prog` at its pc reaches, over
    `stepSp1`, the fold of `execInstrBr` over the block, at the end of the block, with the
    block still in place. -/
theorem reaches_block {base : Word} {prog : List Instr} (hall : prog.all isPure = true)
    {t : MachineState} (hcode : CodeAt base (prog.map some) t) (hpc : t.pc = base) :
    Reaches stepSp1 (fun t' => Agree t' (prog.foldl execInstrBr t) ∧
      t'.pc = base + BitVec.ofNat 64 (4 * prog.length) ∧ CodeAt base (prog.map some) t') t := by
  have key : ∀ n k (u : MachineState), k + n = prog.length → CodeAt base (prog.map some) u →
      u.pc = base + BitVec.ofNat 64 (4 * k) →
      Reaches stepSp1 (fun t' => t' = (prog.drop k).foldl execInstrBr u) u := by
    intro n
    induction n with
    | zero =>
      intro k u hk _ _
      exact Ascent.Reaches.done (by simp [show k = prog.length by omega])
    | succ n ih =>
      intro k u hk hc hupc
      have hkl : k < prog.length := by omega
      have hpure : isPure prog[k] = true := List.all_eq_true.mp hall _ (List.getElem_mem hkl)
      have hs : isStraight prog[k] = true := by simp [isPure] at hpure; exact hpure.1
      have hop := opnOk_of_isPure hpure
      refine Ascent.Reaches.step (stepSp1_ctl (fetch_at hc hkl hupc) (isStraight_isMemAccess hs)
        (isStraight_ne_ecall hs) (isStraight_ne_ebreak hs)) ?_
      have := ih (k + 1) (execInstrBr u prog[k]) (by omega)
        (codeAt_of_code_eq (code_execInstrBr_opn hop) hc)
        (by rw [pc_execInstrBr_opn hop, hupc, addr_succ])
      rwa [List.drop_eq_getElem_cons hkl, List.foldl_cons]
  refine Ascent.Reaches.mono (key prog.length 0 t (by omega) hcode (by simp [hpc])) ?_
  rintro t' rfl
  simp only [List.drop_zero]
  refine ⟨Agree.refl _, ?_, ?_⟩
  · have : ∀ (is : List Instr) (u : MachineState), is.all isPure = true →
        (is.foldl execInstrBr u).pc = u.pc + BitVec.ofNat 64 (4 * is.length) ∧
          (is.foldl execInstrBr u).code = u.code := by
      intro is
      induction is with
      | nil => intro u _; simp
      | cons i is ih =>
        intro u hall
        simp only [List.all_cons, Bool.and_eq_true] at hall
        obtain ⟨h1, h2⟩ := ih (execInstrBr u i) hall.2
        rw [List.foldl_cons, h1, h2, pc_execInstrBr_opn (opnOk_of_isPure hall.1),
          code_execInstrBr_opn (opnOk_of_isPure hall.1), List.length_cons, BitVec.add_assoc,
          show 4 * (is.length + 1) = 4 + 4 * is.length by omega, BitVec.ofNat_add]
        exact ⟨rfl, rfl⟩
    rw [(this prog t hall).1, hpc]
  · have : ∀ (is : List Instr) (u : MachineState), is.all isPure = true →
        (is.foldl execInstrBr u).code = u.code := by
      intro is
      induction is with
      | nil => intro u _; rfl
      | cons i is ih =>
        intro u hall
        simp only [List.all_cons, Bool.and_eq_true] at hall
        rw [List.foldl_cons, ih _ hall.2, code_execInstrBr_opn (opnOk_of_isPure hall.1)]
    exact codeAt_of_code_eq (this prog t hall) hcode

/-- **A correspondence for a pure block.** If every related state holds the block at its pc,
    and every state agreeing with the fold of `execInstrBr` over the block, at its end and
    with the block in place, is related to the abstract result, the block corresponds to
    `fa`. -/
theorem corres_block {AState : Type} {SR : MachineState → AState → Prop} {P : AState → Prop}
    {fa : AState → AState} (base : Word) (prog : List Instr) (hall : prog.all isPure = true)
    (hcode : ∀ m a, SR m a → P a → CodeAt base (prog.map some) m ∧ m.pc = base)
    (hpost : ∀ m a t, SR m a → P a → Agree t (prog.foldl execInstrBr m) →
      t.pc = base + BitVec.ofNat 64 (4 * prog.length) → CodeAt base (prog.map some) t →
      SR t (fa a)) :
    CorresSp1 SR P fa :=
  Corres.of_reaches (fun _ ha => Accepted.stuck ha) fun m a hSR hP =>
    let ⟨hc, hpc⟩ := hcode m a hSR hP
    Ascent.Reaches.mono (reaches_block hall hc hpc) fun t ⟨hag, htpc, htc⟩ =>
      hpost m a t hSR hP hag htpc htc

/-! ## The registers of a pure block, one named value per instruction -/

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

theorem getReg_ofRegs (ρ : Reg → Word) (r : Reg) :
    (ofRegs ρ).getReg r = if r = .x0 then 0 else ρ r := by
  cases r <;> rfl

theorem getReg_ofRegs_getReg (m : MachineState) (r : Reg) :
    (ofRegs m.getReg).getReg r = m.getReg r := by
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
    simp only [execInstrBr, val, dst, getReg_setReg, MachineState.getReg_setPC,
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
    simp only [val, execInstrBr, dst, getReg_setReg, getReg_ofRegs, MachineState.getReg_setPC,
      upd, reduceCtorEq, if_false, if_true, signExtend12, getReg_x0, ne_eq, not_false_eq_true,
      rv64_mulhu, rv64_mulh, rv64_mulhsu,
      and_true, and_false] at hv
    dsimp only [dst])
  simp only [List.foldl_nil, upd, reduceCtorEq, if_false, if_true]))

end MachineChecked.RiscV.Lprog
