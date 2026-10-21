/-
  MachineChecked.RiscV.Lprog.Block

  Straight-line code through the lift: the counterpart of catcrypt-compiler's `steps_block`
  (`RiscvPc64`, rv64 stack), proved at Lprog and carried down by the lift's simulation.

  A block of *pure* instructions (straight, and not reading the pc) lifts to labels and
  operations only. At Lprog it runs from its first label to its end in a state that stands for
  the fold of `execInstrBr` over it (`reaches_pure`). Carried down (`reaches_block`), a machine
  holding the block at its pc reaches, over `stepSp1`, a state agreeing with that fold, at the
  end of the block; as a correspondence, `corres_block`.

  The fold's effect is then a term in the initial registers. Unfolding it and reading a
  register gives a tree in which each value is copied into every later instruction that reads
  it, which past a hundred instructions is too slow for `simp`. So the block's registers are
  also given as a valuation `Reg → Word` updated once per instruction (`stepRegs`):
  `getReg_foldl` says the machine's registers after the block are that fold, and the tactic
  `regs_run` runs a literal block on it, naming each instruction's result `v` with one small
  equation `hv`, the facts `bv_decide` takes.
-/

import MachineChecked.RiscV.Lprog.Lift
import MachineChecked.Ascent.Corres

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog
open MachineChecked.Ascent (Reaches Corres)

theorem opnOk_of_isPure {i : Instr} (h : isPure i = true) : opnOk i = true := by
  simp [opnOk, h]

theorem memOkSp1_of_isPure {u : MachineState} {i : Instr} (h : isPure i = true) :
    memOkSp1 u i = true := by
  cases i <;> simp_all [isPure, isStraight, memOkSp1, memAccess]

theorem wfI_of_isPure {k len : Nat} {i : Instr} (h : isPure i = true) : wfI k len i = true := by
  cases i <;> simp_all [isPure, isStraight, wfI]

theorem liftI_of_isPure {k : Nat} {i : Instr} (h : isPure i = true) :
    liftI k i = .Lopn (opOf i) := by
  simp [liftI, opnOk_of_isPure h]

/-- **A pure block at Lprog.** From label `k` of a lifted pure block, in a state standing for
    `u`, the run reaches the end of the body in a state standing for the fold of `execInstrBr`
    over the rest of the block. -/
theorem reaches_pure {prog : List Instr} (hall : prog.all isPure = true) :
    ∀ (n k : Nat), k + n = prog.length → ∀ (regs : String → BitVec 64) (m u : MachineState),
      Agree (ofParts regs m) u →
      rvIsa.Reaches (lift prog) (fun s => s.pc = 2 * prog.length ∧
        Agree (ofParts s.regs s.m) ((prog.drop k).foldl execInstrBr u)) ⟨2 * k, regs, m⟩ := by
  intro n
  induction n with
  | zero =>
    intro k hk regs m u hag
    rw [Nat.add_zero] at hk
    subst hk
    exact Ascent.Reaches.done ⟨rfl, by simpa using hag⟩
  | succ n ih =>
    intro k hk regs m u hag
    have hkl : k < prog.length := by omega
    have hpure : isPure prog[k] = true := List.all_eq_true.mp hall _ (List.getElem_mem hkl)
    have hlab : (lift prog)[2 * k]? = some (.Llabel .internal k) := by
      simpa [lift] using getElem?_liftFrom_even 0 prog k hkl
    have hop : (lift prog)[2 * k + 1]? = some (.Lopn (opOf prog[k])) := by
      have := getElem?_liftFrom_odd 0 prog k hkl
      simp only [Nat.zero_add] at this
      rw [lift, this, liftI_of_isPure hpure]
    refine reaches_label hlab (reaches_opn hag hop (opnOk_of_isPure hpure)
      (memOkSp1_of_isPure hpure) fun regs' m' hag' => ?_)
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    have := ih (k + 1) (by omega) regs' m' _ hag'
    rwa [List.drop_eq_getElem_cons hkl, List.foldl_cons]

theorem wf_of_isPure {prog : List Instr} (hall : prog.all isPure = true) : WF prog :=
  fun _ hk => wfI_of_isPure (List.all_eq_true.mp hall _ (List.getElem_mem hk))

/-- **A pure block, through the lift.** A machine holding the pure block `prog` at its pc
    reaches, over `stepSp1`, a state agreeing with the fold of `execInstrBr` over the block,
    at the end of the block, with the block still in place. -/
theorem reaches_block {base : Word} {prog : List Instr} (hall : prog.all isPure = true)
    {t : MachineState} (hcode : CodeAt base (prog.map some) t) (hpc : t.pc = base) :
    Reaches stepSp1 (fun t' => Agree t' (prog.foldl execInstrBr t) ∧
      t'.pc = base + BitVec.ofNat 64 (4 * prog.length) ∧ CodeAt base (prog.map some) t') t := by
  have h := reaches_pure hall prog.length 0 (by omega) (regsOf (fun _ => 0) t) t t
    (agree_ofParts_regsOf _ t)
  refine Ascent.Reaches.mono (reach_of_reaches (wf_of_isPure hall) (sim_entry _ hcode hpc) h) ?_
  rintro t' ⟨s', hs', hpc', hag'⟩
  refine ⟨hs'.agree.symm.trans (by simpa using hag'), ?_, hs'.code⟩
  rcases hs'.pc with ⟨-, h⟩ | ⟨h, -⟩
  · rw [h, hpc', show 2 * prog.length / 2 = prog.length by omega]
  · omega

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
    Corres stepSp1 SR P fa := by
  intro m a hSR hP
  obtain ⟨hc, hpc⟩ := hcode m a hSR hP
  exact Ascent.Reaches.mono (reaches_block hall hc hpc) fun t ⟨hag, htpc, htc⟩ =>
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
