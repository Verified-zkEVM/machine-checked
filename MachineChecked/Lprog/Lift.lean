/-
  MachineChecked.Lprog.Lift

  From decoded RISC-V to Lprog, and back down by simulation.

  `lift prog` turns a function's decoded instructions into an Lprog body: instruction `k`
  becomes `Llabel k` followed by its lifted form (`liftI`). An operation (pure, or a load or
  store) becomes `Lopn`; a conditional branch becomes `Lcond` on a comparison, to the label of
  its target; `jal x0` becomes `Lgoto`; `jalr x0, 0(ra)` becomes `Lret`. Anything else becomes
  `Lsyscall "unlifted"`, which has no step, so a run that succeeds never meets one.

  `Sim base prog s t` relates an Lprog state to a machine state: they agree on registers,
  memory, code and the I/O fields; the machine holds `prog` at `base`; and the counters
  correspond (label or instruction `k` at `base + 4k`, the end of the body past the last
  instruction, a return at the address `ra` gives). Every step of the lifted body is matched by
  zero steps (a label) or one step of `stepSp1` (`sim_step`), so every run is (`sim_run`): the
  forward simulation, and since `stepSp1` is deterministic, every machine run from `t` that
  succeeds for as long is this one.

  `reach_of_corresIsa` carries a correspondence proved at Lprog down to a run over `stepSp1`,
  and `reach_of_reaches`/`reach_of_halts` a run proved at Lprog (`Isa.Reaches`, `Isa.Halts`).
  The rules `reaches_label`, `reaches_opn`, `reaches_cond` and `halts_ret` run a body at Lprog,
  stating what each instruction reads on a machine state the Lprog state stands for. A call
  out of the function stops a run at Lprog; it is taken over the machine, and `sim_return`
  resumes at Lprog after it.
-/

import MachineChecked.Lprog.RiscV

namespace MachineChecked.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym

/-- The label an offset reaches from instruction `k`. -/
def tgt (k : Nat) (off : Word) : Nat := ((k : Int) + off.toInt / 4).toNat

/-- One instruction, lifted. -/
def liftI (k : Nat) (i : Instr) : LinstrR Instr :=
  if opnOk i then .Lopn [] i []
  else match i with
    | .BEQ a b off => .Lcond (.cmp "eq" (.reg (regName a)) (.reg (regName b))) (tgt k (signExtend13 off))
    | .BNE a b off => .Lcond (.cmp "ne" (.reg (regName a)) (.reg (regName b))) (tgt k (signExtend13 off))
    | .BLT a b off => .Lcond (.cmp "lt" (.reg (regName a)) (.reg (regName b))) (tgt k (signExtend13 off))
    | .BGE a b off => .Lcond (.cmp "ge" (.reg (regName a)) (.reg (regName b))) (tgt k (signExtend13 off))
    | .BLTU a b off =>
      .Lcond (.cmp "ltu" (.reg (regName a)) (.reg (regName b))) (tgt k (signExtend13 off))
    | .BGEU a b off =>
      .Lcond (.cmp "geu" (.reg (regName a)) (.reg (regName b))) (tgt k (signExtend13 off))
    | .JAL .x0 off => .Lgoto ("", tgt k (signExtend21 off))
    | .JALR .x0 .x1 off => if off = 0 then .Lret else .Lsyscall "unlifted"
    | _ => .Lsyscall "unlifted"

/-- Instructions from index `k` on, lifted. -/
def liftFrom : Nat → List Instr → Lcmd Instr
  | _, [] => []
  | k, i :: is => .Llabel .internal k :: liftI k i :: liftFrom (k + 1) is

/-- A function, lifted. -/
def lift (prog : List Instr) : Lcmd Instr := liftFrom 0 prog

theorem length_liftFrom : ∀ (k : Nat) (is : List Instr), (liftFrom k is).length = 2 * is.length
  | _, [] => rfl
  | k, _ :: is => by simp only [liftFrom, List.length_cons, length_liftFrom (k + 1) is]; omega

theorem getElem?_liftFrom_even : ∀ (k : Nat) (is : List Instr) (j : Nat), j < is.length →
    (liftFrom k is)[2 * j]? = some (.Llabel .internal (k + j))
  | _, [], _, h => absurd h (by simp)
  | k, i :: is, 0, _ => by simp [liftFrom]
  | k, i :: is, j + 1, h => by
    rw [show 2 * (j + 1) = (2 * j) + 1 + 1 by omega]
    simp only [liftFrom, List.getElem?_cons_succ]
    rw [getElem?_liftFrom_even (k + 1) is j (by simp only [List.length_cons] at h; omega),
      show k + 1 + j = k + (j + 1) by omega]

theorem getElem?_liftFrom_odd : ∀ (k : Nat) (is : List Instr) (j : Nat) (h : j < is.length),
    (liftFrom k is)[2 * j + 1]? = some (liftI (k + j) is[j])
  | _, [], _, h => absurd h (by simp)
  | k, i :: is, 0, _ => by simp [liftFrom]
  | k, i :: is, j + 1, h => by
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega]
    simp only [liftFrom, List.getElem?_cons_succ]
    rw [getElem?_liftFrom_odd (k + 1) is j (by simp only [List.length_cons] at h; omega)]
    simp only [List.getElem_cons_succ]
    congr 2; omega

theorem isLabel_label {Op : Type} (k l : LLabel) :
    isLabel (Op := Op) l (.Llabel .internal k) = (k == l) := rfl

theorem liftI_not_label (k : Nat) (i : Instr) (l : LLabel) : isLabel l (liftI k i) = false := by
  unfold liftI
  split
  · rfl
  · split <;> (try split) <;> rfl

/-- Label `l` sits at index `2 (l - k)` of the instructions lifted from index `k`. -/
theorem labelIdx_liftFrom : ∀ (k : Nat) (is : List Instr) (l : Nat), k ≤ l → l < k + is.length →
    labelIdx (liftFrom k is) l = some (2 * (l - k))
  | _, [], _, h1, h2 => absurd h2 (by simp; omega)
  | k, i :: is, l, h1, h2 => by
    unfold labelIdx
    simp only [liftFrom, List.findIdx?_cons, isLabel_label, liftI_not_label]
    by_cases hkl : k = l
    · subst hkl; simp
    · have := labelIdx_liftFrom (k + 1) is l (by omega) (by simp only [List.length_cons] at h2; omega)
      unfold labelIdx at this
      simp only [beq_iff_eq, hkl, if_false, this, Option.map_some, Bool.false_eq_true]
      congr 1; omega

theorem labelIdx_lift {prog : List Instr} {l : Nat} (h : l < prog.length) :
    labelIdx (lift prog) l = some (2 * l) := by
  have := labelIdx_liftFrom 0 prog l (Nat.zero_le _) (by omega)
  simpa [lift] using this

/-! ## Well-formed functions

A branch or jump must land on an instruction of the function: its offset a multiple of four,
its target in range. -/

/-- The jump from instruction `k` by `off` lands on an instruction of a function of `len`. -/
def jumpOk (k len : Nat) (off : Word) : Bool :=
  off.toInt % 4 == 0 && 0 ≤ (k : Int) + off.toInt / 4 && (k : Int) + off.toInt / 4 < len

/-- One instruction's well-formedness. -/
def wfI (k len : Nat) : Instr → Bool
  | .BEQ _ _ off | .BNE _ _ off | .BLT _ _ off | .BGE _ _ off | .BLTU _ _ off | .BGEU _ _ off =>
    jumpOk k len (signExtend13 off)
  | .JAL .x0 off => jumpOk k len (signExtend21 off)
  | _ => true

/-- Every branch and jump of `prog` lands in `prog`. -/
def WF (prog : List Instr) : Prop := ∀ k (h : k < prog.length), wfI k prog.length prog[k] = true

/-- The address a well-formed jump reaches. -/
theorem jump_addr {base : Word} {k len : Nat} {off : Word} (h : jumpOk k len off = true) :
    base + BitVec.ofNat 64 (4 * k) + off = base + BitVec.ofNat 64 (4 * tgt k off) ∧ tgt k off < len := by
  simp only [jumpOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h4, h0⟩, hlt⟩ := h
  have ht : (tgt k off : Int) = (k : Int) + off.toInt / 4 := by
    unfold tgt; omega
  refine ⟨?_, by unfold tgt; omega⟩
  rw [BitVec.add_assoc]
  congr 1
  rw [← BitVec.ofInt_natCast 64 (4 * k), ← BitVec.ofInt_natCast 64 (4 * tgt k off),
    ← BitVec.ofInt_toInt (x := off), ← BitVec.ofInt_add, BitVec.ofInt_toInt]
  congr 1
  push_cast
  omega

/-! ## Agreement, again -/

theorem Agree.refl (t : MachineState) : Agree t t := ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Agree.trans {t u v : MachineState} (h₁ : Agree t u) (h₂ : Agree u v) : Agree t v :=
  ⟨fun r => (h₁.regs r).trans (h₂.regs r), fun a => (h₁.mem a).trans (h₂.mem a),
    h₁.code.trans h₂.code, h₁.committed.trans h₂.committed, h₁.publicValues.trans h₂.publicValues,
    h₁.privateInput.trans h₂.privateInput, h₁.inputBufBase.trans h₂.inputBufBase⟩

theorem getReg_ofParts (regs : String → BitVec 64) (m : MachineState) (r : Reg) :
    (ofParts regs m).getReg r = if r = .x0 then 0 else regs (regName r) := by
  cases r <;> rfl

/-- A machine state agrees with itself seen through Lprog's register file. -/
theorem agree_ofParts_regsOf (old : String → BitVec 64) (t : MachineState) :
    Agree (ofParts (regsOf old t) t) t := by
  refine ⟨fun r => ?_, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [getReg_ofParts]
  split
  · next h => subst h; rfl
  · simp [regsOf, regOfName_regName]

/-- An operation advances the pc by four. -/
theorem pc_execInstrBr_opn {t : MachineState} {i : Instr} (h : opnOk i = true) :
    (execInstrBr t i).pc = t.pc + 4 := by
  cases i <;> simp_all [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, execInstrBr, pc_setPC']

/-- An operation's code map is unchanged. -/
theorem code_execInstrBr_opn {t : MachineState} {i : Instr} (h : opnOk i = true) :
    (execInstrBr t i).code = t.code := by
  have := (Agree.refl t).execInstrBr h
  cases i <;> simp_all [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, execInstrBr,
    MachineState.setByte, MachineState.setHalfword, MachineState.setWord32]

/-- An operation the SP1 memory check admits steps to `execInstrBr`. -/
theorem stepSp1_opn {t : MachineState} {i : Instr} (hf : t.code t.pc = some i) (h : opnOk i = true)
    (hok : memOkSp1 t i = true) : stepSp1 t = some (execInstrBr t i) := by
  by_cases hp : isPure i = true
  · have hs : isStraight i = true := by simp [isPure] at hp; exact hp.1
    exact stepSp1_plain hf (isStraight_isMemAccess hs) (isStraight_ne_ecall hs) (isStraight_ne_ebreak hs)
  · simp only [opnOk, hp, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact stepSp1_mem hf h.1 h.2 hok

/-! ## The simulation -/

/-- The counters correspond: label or instruction `k` (or the end of the body, `k = len`) at
    `base + 4k`, and a return at the address `ra` gives. -/
def PcRel (base : Word) (len lp : Nat) (t : MachineState) : Prop :=
  (lp ≤ 2 * len ∧ t.pc = base + BitVec.ofNat 64 (4 * (lp / 2))) ∨
  (lp = 2 * len + 1 ∧ t.pc = t.getReg .x1 &&& ~~~1#64)

/-- An Lprog state of the lifted function and a machine state correspond. -/
structure Sim (base : Word) (prog : List Instr) (s : State rvIsa) (t : MachineState) : Prop where
  agree : Agree (ofParts s.regs s.m) t
  code : CodeAt base (prog.map some) t
  pc : PcRel base prog.length s.pc t

theorem agree_setPC (t : MachineState) (v : Word) : Agree t (t.setPC v) :=
  ⟨fun _ => by simp, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem agree_setReg_x0 (t : MachineState) (v : Word) : Agree t (t.setReg .x0 v) :=
  Agree.refl t

/-- A register operand reads what the machine's register holds. -/
theorem regVal_regName {regs : String → BitVec 64} {m t : MachineState} (h : Agree (ofParts regs m) t)
    (r : Reg) : regVal regs (.reg (regName r)) = some (t.getReg r) := by
  rw [← h.regs r, getReg_ofParts]
  cases r <;> rfl

/-- Fall through to the next instruction. -/
theorem sim_next {base : Word} {prog : List Instr} {k : Nat} (hk : k < prog.length)
    {regs : String → BitVec 64} {m : MachineState} {t1 : MachineState}
    (hag : Agree (ofParts regs m) t1) (hcode : CodeAt base (prog.map some) t1)
    (hpc : t1.pc = base + BitVec.ofNat 64 (4 * k) + 4) :
    Sim base prog ⟨2 * k + 2, regs, m⟩ t1 := by
  refine ⟨hag, hcode, Or.inl ⟨by dsimp only; omega, ?_⟩⟩
  dsimp only
  rw [hpc, show (2 * k + 2) / 2 = k + 1 by omega, BitVec.add_assoc,
    show 4 * (k + 1) = 4 * k + 4 by omega, BitVec.ofNat_add]
  rfl

/-- Jump to label `l`. -/
theorem sim_goto {base : Word} {prog : List Instr} {l : Nat} (hl : l < prog.length)
    {regs : String → BitVec 64} {m : MachineState} {t1 : MachineState}
    (hag : Agree (ofParts regs m) t1) (hcode : CodeAt base (prog.map some) t1)
    (hpc : t1.pc = base + BitVec.ofNat 64 (4 * l)) :
    Sim base prog ⟨2 * l, regs, m⟩ t1 :=
  ⟨hag, hcode, Or.inl ⟨by dsimp only; omega, by dsimp only; rw [hpc, show 2 * l / 2 = l by omega]⟩⟩

/-- The fetch at an instruction's address. -/
theorem fetch_sim {base : Word} {prog : List Instr} {t : MachineState} {k : Nat}
    (hcode : CodeAt base (prog.map some) t) (hk : k < prog.length)
    (hpc : t.pc = base + BitVec.ofNat 64 (4 * k)) : t.code t.pc = some prog[k] := by
  rw [hpc, hcode k (by simpa using hk)]
  simp [hk]

/-- A conditional branch, either way. -/
theorem sim_branch {base : Word} {prog : List Instr} {k : Nat} (hk : k < prog.length)
    {regs : String → BitVec 64} {m t : MachineState}
    (hag : Agree (ofParts regs m) t) (hcode : CodeAt base (prog.map some) t)
    (hpc : t.pc = base + BitVec.ofNat 64 (4 * k)) {off : Word} (hj : jumpOk k prog.length off = true)
    (c : Bool) {s1 : State rvIsa}
    (h : (if c then (labelIdx (lift prog) (tgt k off)).map fun j => (⟨j, regs, m⟩ : State rvIsa)
      else some ⟨2 * k + 1 + 1, regs, m⟩) = some s1) :
    Sim base prog s1 (if c then t.setPC (t.pc + off) else t.setPC (t.pc + 4)) := by
  obtain ⟨haddr, hlt⟩ := jump_addr (base := base) hj
  cases c
  · simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h ⊢
    subst h
    exact sim_next hk ((hag.trans (agree_setPC t _))) (codeAt_of_code_eq (by simp) hcode)
      (by simp [pc_setPC', hpc])
  · simp only [if_true, labelIdx_lift hlt, Option.map_some, Option.some.injEq] at h ⊢
    subst h
    exact sim_goto hlt (hag.trans (agree_setPC t _)) (codeAt_of_code_eq (by simp) hcode)
      (by simp only [pc_setPC', hpc, haddr])

/-- A jump, lifted: `jal x0` is a jump to a label, anything else is not lifted. -/
theorem liftI_jal (k : Nat) (rd : Reg) (off : BitVec 21) :
    liftI k (.JAL rd off) =
      if rd = .x0 then .Lgoto ("", tgt k (signExtend21 off)) else .Lsyscall "unlifted" := by
  unfold liftI
  simp only [opnOk, isPure, isStraight, Instr.isMemAccess, Bool.false_and, Bool.false_or,
    Bool.false_eq_true, if_false]
  split <;> simp_all

/-- An indirect jump, lifted: `jalr x0, 0(ra)` is a return, anything else is not lifted. -/
theorem liftI_jalr (k : Nat) (rd rs : Reg) (off : BitVec 12) :
    liftI k (.JALR rd rs off) =
      if rd = .x0 ∧ rs = .x1 ∧ off = 0 then .Lret else .Lsyscall "unlifted" := by
  unfold liftI
  simp only [opnOk, isPure, isStraight, Instr.isMemAccess, Bool.false_and, Bool.false_or,
    Bool.false_eq_true, if_false]
  split <;> simp_all

/-- A conditional branch on a comparison of two registers, either way. -/
theorem sim_cond {base : Word} {prog : List Instr} {k : Nat} (hk : k < prog.length)
    {regs : String → BitVec 64} {m t : MachineState}
    (hag : Agree (ofParts regs m) t) (hcode : CodeAt base (prog.map some) t)
    (hpc : t.pc = base + BitVec.ofNat 64 (4 * k)) {off : BitVec 13}
    (hj : jumpOk k prog.length (signExtend13 off) = true) {i : Instr}
    (hf : t.code t.pc = some i) (hm : i.isMemAccess = false) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    {op : String} {a b : Reg} {c : Bool} (hc : cmpEval op (t.getReg a) (t.getReg b) = some c)
    (hexec : execInstrBr t i = if c then t.setPC (t.pc + signExtend13 off) else t.setPC (t.pc + 4))
    {s1 : State rvIsa}
    (h : ((do
          let va ← regVal regs (LOperand.reg (regName a))
          let vb ← regVal regs (LOperand.reg (regName b))
          cmpEval op va vb).bind fun c =>
        if c = true then
          Option.map (fun j => (⟨j, regs, m⟩ : State rvIsa)) (labelIdx (lift prog) (tgt k (signExtend13 off)))
        else some ⟨2 * k + 1 + 1, regs, m⟩) = some s1) :
    ∃ j t1, stepsSp1 j t = some t1 ∧ Sim base prog s1 t1 := by
  rw [regVal_regName hag a, regVal_regName hag b] at h
  simp only [Option.bind_eq_bind, Option.bind_some, hc] at h
  refine ⟨1, _, by rw [stepsSp1_succ_of_step (stepSp1_plain hf hm he hb)]; rfl, ?_⟩
  rw [hexec]
  exact sim_branch hk hag hcode hpc hj c h

/-- **One step of the lifted function is zero or one step of `stepSp1`.** -/
theorem sim_step {base : Word} {prog : List Instr} (hwf : WF prog) {s s1 : State rvIsa}
    {t : MachineState} (hs : Sim base prog s t) (h : rvIsa.step (lift prog) s = some s1) :
    ∃ j t1, stepsSp1 j t = some t1 ∧ Sim base prog s1 t1 := by
  obtain ⟨hag, hcode, hpc⟩ := hs
  have hlen : (lift prog).length = 2 * prog.length := length_liftFrom 0 prog
  have hnone : ∀ p, 2 * prog.length ≤ p → (lift prog)[p]? = none := fun p hp =>
    List.getElem?_eq_none (by omega)
  rcases hpc with ⟨hle, hpcv⟩ | ⟨hret, -⟩
  case inr =>
    simp only [Isa.step, hret, hnone (2 * prog.length + 1) (by omega)] at h
    cases h
  obtain ⟨k, hk | hk⟩ : ∃ k, s.pc = 2 * k ∨ s.pc = 2 * k + 1 := ⟨s.pc / 2, by omega⟩
  · -- a label
    by_cases hkl : k < prog.length
    · have hins : (lift prog)[s.pc]? = some (.Llabel .internal k) := by
        rw [hk]; simpa [lift] using getElem?_liftFrom_even 0 prog k hkl
      simp only [Isa.step, hins, Option.some.injEq] at h
      subst h
      exact ⟨0, t, rfl, hag, hcode, Or.inl ⟨by dsimp only; omega,
        by dsimp only; rw [hpcv, hk, show (2 * k + 1) / 2 = 2 * k / 2 by omega]⟩⟩
    · simp only [Isa.step, hnone _ (show 2 * prog.length ≤ s.pc by omega)] at h
      cases h
  · -- an instruction
    have hkl : k < prog.length := by omega
    have hpck : t.pc = base + BitVec.ofNat 64 (4 * k) := by
      rw [hpcv, hk, show (2 * k + 1) / 2 = k by omega]
    have hfetch := fetch_sim hcode hkl hpck
    have hins : (lift prog)[s.pc]? = some (liftI k prog[k]) := by
      rw [hk]; simpa [lift] using getElem?_liftFrom_odd 0 prog k hkl
    have hw := hwf k hkl
    generalize prog[k] = i at hfetch hins hw
    simp only [Isa.step, hins] at h
    obtain ⟨pc, regs, m⟩ := s
    simp only at hk hag
    subst hk
    by_cases hop : opnOk i = true
    · -- an operation
      simp only [liftI, hop, if_true, rvIsa, Bool.true_and] at h
      by_cases hok : memOkSp1 (ofParts regs m) i = true
      · simp only [hok, if_true, Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨1, execInstrBr t i, ?_, ?_⟩
        · rw [stepsSp1_succ_of_step (stepSp1_opn hfetch hop ((hag.memOkSp1 i).symm.trans hok ▸ rfl))]
          · rfl
        · exact sim_next hkl
            ((agree_ofParts_regsOf regs _).trans (hag.execInstrBr hop))
            (codeAt_of_code_eq (code_execInstrBr_opn hop) hcode)
            (by rw [pc_execInstrBr_opn hop, hpck])
      · simp [hok] at h
    · cases i
      case BEQ a b off =>
        simp only [liftI, hop, Bool.false_eq_true, if_false] at h
        exact sim_cond hkl hag hcode hpck hw hfetch rfl (by simp) (by simp) (c := t.getReg a == t.getReg b)
          (by simp [cmpEval]) (by simp [execInstrBr]) h
      case BNE a b off =>
        simp only [liftI, hop, Bool.false_eq_true, if_false] at h
        exact sim_cond hkl hag hcode hpck hw hfetch rfl (by simp) (by simp) (c := t.getReg a != t.getReg b)
          (by simp [cmpEval]) (by simp [execInstrBr]) h
      case BLT a b off =>
        simp only [liftI, hop, Bool.false_eq_true, if_false] at h
        exact sim_cond hkl hag hcode hpck hw hfetch rfl (by simp) (by simp) (c := BitVec.slt (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) h
      case BGE a b off =>
        simp only [liftI, hop, Bool.false_eq_true, if_false] at h
        exact sim_cond hkl hag hcode hpck hw hfetch rfl (by simp) (by simp) (c := !BitVec.slt (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) h
      case BLTU a b off =>
        simp only [liftI, hop, Bool.false_eq_true, if_false] at h
        exact sim_cond hkl hag hcode hpck hw hfetch rfl (by simp) (by simp) (c := BitVec.ult (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) h
      case BGEU a b off =>
        simp only [liftI, hop, Bool.false_eq_true, if_false] at h
        exact sim_cond hkl hag hcode hpck hw hfetch rfl (by simp) (by simp) (c := !BitVec.ult (t.getReg a) (t.getReg b))
          (by simp [cmpEval]) (by simp [execInstrBr]) h
      case JAL rd off =>
        rw [liftI_jal] at h
        by_cases hrd : rd = .x0
        · subst hrd
          simp only [if_true] at h
          obtain ⟨haddr, hlt⟩ := jump_addr (base := base) hw
          simp only [labelIdx_lift hlt, Option.map_some, Option.some.injEq] at h
          subst h
          refine ⟨1, _, by rw [stepsSp1_succ_of_step (stepSp1_plain hfetch rfl (by simp) (by simp))]; rfl,
            sim_goto hlt (hag.trans (agree_setPC t _)) (codeAt_of_code_eq (by simp) hcode)
              (by simp only [pc_setPC', hpck, haddr])⟩
        · simp [hrd] at h
      case JALR rd rs off =>
        rw [liftI_jalr] at h
        by_cases hr : rd = .x0 ∧ rs = .x1 ∧ off = 0
        · obtain ⟨rfl, rfl, rfl⟩ := hr
          simp only [and_self, if_true, Option.some.injEq, hlen] at h
          subst h
          refine ⟨1, _, by rw [stepsSp1_succ_of_step (stepSp1_plain hfetch rfl (by simp) (by simp))]; rfl,
            hag.trans (agree_setPC t _), codeAt_of_code_eq (by simp) hcode,
            Or.inr ⟨rfl, by simp [pc_setPC', signExtend12]⟩⟩
        · simp only [if_neg hr] at h
          simp at h
      all_goals first
        | (simp [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS] at hop; done)
        | (simp only [liftI, if_neg hop] at h; simp at h)

/-- **Every run of the lifted function is a run of `stepSp1`.** -/
theorem sim_run {base : Word} {prog : List Instr} (hwf : WF prog) :
    ∀ (n : Nat) (s s' : State rvIsa) (t : MachineState), Sim base prog s t →
      rvIsa.run (lift prog) n s = some s' → ∃ j t', stepsSp1 j t = some t' ∧ Sim base prog s' t' := by
  intro n
  induction n with
  | zero =>
    intro s s' t hs h
    by_cases hh : rvIsa.halted (lift prog) s
    · rw [Isa.run_halt _ _ hh] at h; cases h; exact ⟨0, t, rfl, hs⟩
    · simp [Isa.run, hh] at h
  | succ n ih =>
    intro s s' t hs h
    by_cases hh : rvIsa.halted (lift prog) s
    · rw [Isa.run_halt _ _ hh] at h; cases h; exact ⟨0, t, rfl, hs⟩
    · rw [Isa.run_succ _ _ hh] at h
      cases hstep : rvIsa.step (lift prog) s with
      | none => rw [hstep] at h; cases h
      | some s1 =>
        rw [hstep, Option.bind_some] at h
        obtain ⟨j, t1, hj, hs1⟩ := sim_step hwf hs hstep
        obtain ⟨j', t', hj', hs'⟩ := ih s1 s' t1 hs1 h
        exact ⟨j + j', t', by rw [stepsSp1_add, hj, Option.bind_some, hj'], hs'⟩

/-- The entry: a machine at the first instruction of the function, seen as an Lprog state. -/
theorem sim_entry {base : Word} {prog : List Instr} {t : MachineState} (old : String → BitVec 64)
    (hcode : CodeAt base (prog.map some) t) (hpc : t.pc = base) :
    Sim base prog ⟨0, regsOf old t, t⟩ t :=
  ⟨agree_ofParts_regsOf old t, hcode, Or.inl ⟨Nat.zero_le _, by simp [hpc]⟩⟩

/-- **A correspondence proved at Lprog is a run over `stepSp1`**: from a machine state an Lprog
    state of the lifted function simulates, the machine reaches a state that a halted Lprog
    state related to the abstract result simulates. -/
theorem reach_of_corresIsa {AState : Type} {SR : State rvIsa → AState → Prop} {Pre : AState → Prop}
    {fa : AState → AState} {fuel : Nat} {base : Word} {prog : List Instr} (hwf : WF prog)
    (h : CorresIsa rvIsa (lift prog) SR Pre fa fuel) {s : State rvIsa} {t : MachineState}
    {a : AState} (hs : Sim base prog s t) (hSR : SR s a) (hP : Pre a) :
    Reach (fun t' => ∃ s', Sim base prog s' t' ∧ SR s' (fa a) ∧ rvIsa.halted (lift prog) s') t := by
  obtain ⟨s', hrun, hSR'⟩ := h s a hSR hP
  obtain ⟨j, t', hj, hs'⟩ := sim_run hwf fuel s s' t hs hrun
  exact ⟨j, t', hj, s', hs', hSR', Isa.run_halted _ _ fuel s s' hrun⟩

/-- **Every sequence of steps of the lifted function is a run of `stepSp1`.** -/
theorem sim_steps {base : Word} {prog : List Instr} (hwf : WF prog) :
    ∀ (n : Nat) (s s' : State rvIsa) (t : MachineState), Sim base prog s t →
      rvIsa.steps (lift prog) n s = some s' → ∃ j t', stepsSp1 j t = some t' ∧ Sim base prog s' t' := by
  intro n
  induction n with
  | zero => intro s s' t hs h; cases h; exact ⟨0, t, rfl, hs⟩
  | succ n ih =>
    intro s s' t hs h
    simp only [Isa.steps] at h
    cases hstep : rvIsa.step (lift prog) s with
    | none => rw [hstep] at h; cases h
    | some s1 =>
      rw [hstep, Option.bind_some] at h
      obtain ⟨j, t1, hj, hs1⟩ := sim_step hwf hs hstep
      obtain ⟨j', t', hj', hs'⟩ := ih s1 s' t1 hs1 h
      exact ⟨j + j', t', by rw [stepsSp1_add, hj, Option.bind_some, hj'], hs'⟩

/-- **A run proved at Lprog is a run over `stepSp1`.** -/
theorem reach_of_reaches {base : Word} {prog : List Instr} (hwf : WF prog) {Q : State rvIsa → Prop}
    {s : State rvIsa} {t : MachineState} (hs : Sim base prog s t) (h : rvIsa.Reaches (lift prog) Q s) :
    Reach (fun t' => ∃ s', Sim base prog s' t' ∧ Q s') t := by
  obtain ⟨n, s', hn, hQ⟩ := h
  obtain ⟨j, t', hj, hs'⟩ := sim_steps hwf n s s' t hs hn
  exact ⟨j, t', hj, s', hs', hQ⟩

/-- A run proved to halt at Lprog is a run over `stepSp1`. -/
theorem reach_of_halts {base : Word} {prog : List Instr} (hwf : WF prog) {Q : State rvIsa → Prop}
    {s : State rvIsa} {t : MachineState} (hs : Sim base prog s t) (h : rvIsa.Halts (lift prog) Q s) :
    Reach (fun t' => ∃ s', Sim base prog s' t' ∧ Q s') t :=
  (reach_of_reaches hwf hs h).mono fun _ ⟨s', hs', _, hQ⟩ => ⟨s', hs', hQ⟩

/-- The continuation form: a run proved at Lprog passes `SafeN` back from every state it may
    end in. -/
theorem SafeN.of_reaches {base : Word} {prog : List Instr} (hwf : WF prog) {Q : State rvIsa → Prop}
    {s : State rvIsa} {t : MachineState} (hs : Sim base prog s t) (h : rvIsa.Reaches (lift prog) Q s)
    {G : MachineState → Prop} {n : Nat} {P : Prop}
    (hk : ∀ s' t', Sim base prog s' t' → Q s' → SafeN G n P t') : SafeN G n P t :=
  MachineChecked.RiscV.SafeN.of_reach (reach_of_reaches hwf hs h) fun _ ⟨s', hs', hQ⟩ => hk s' _ hs' hQ

/-! ## Calls

A call `jal ra, off` out of the function is not lifted: a run at Lprog stops at it
(`Reaches`), the call is taken over the machine with the callee's specification, and the run
resumes at Lprog from the instruction after it (`sim_return`), in every state the callee may
return in with the pc at the return address and the code unchanged. -/

/-- The fetch at a call site. -/
theorem fetch_call {base : Word} {prog : List Instr} {s : State rvIsa} {t : MachineState} {k : Nat}
    (hs : Sim base prog s t) (hk : k < prog.length) (hpc : s.pc = 2 * k + 1) :
    t.code t.pc = some prog[k] ∧ t.pc = base + BitVec.ofNat 64 (4 * k) := by
  have hpck : t.pc = base + BitVec.ofNat 64 (4 * k) := by
    rcases hs.pc with ⟨_, h⟩ | ⟨h, _⟩
    · rw [h, hpc, show (2 * k + 1) / 2 = k by omega]
    · omega
  exact ⟨fetch_sim hs.code hk hpck, hpck⟩

/-- **The return from a call**: a machine state at the instruction after the call, with the
    function's code in place, stands for the Lprog state there. -/
theorem sim_return {base : Word} {prog : List Instr} {k : Nat} (hk : k < prog.length)
    (old : String → BitVec 64) {t' : MachineState} (hcode : CodeAt base (prog.map some) t')
    (hpc : t'.pc = base + BitVec.ofNat 64 (4 * k) + 4) :
    Sim base prog ⟨2 * k + 2, regsOf old t', t'⟩ t' :=
  sim_next hk (agree_ofParts_regsOf old t') hcode hpc

/-! ## Running a body at Lprog

Each rule takes a machine state `u` the Lprog state stands for (`Agree (ofParts regs m) u`), so
that what an instruction reads is stated on `u`, and continues from every Lprog state that
stands for the machine state after it. -/

section Rules

variable {body : Lcmd Instr} {Q : State rvIsa → Prop} {pc : Nat} {regs : String → BitVec 64}
  {m u : MachineState}

theorem reaches_label {kd : LabelKind} {l : LLabel} (hb : body[pc]? = some (.Llabel kd l))
    (h : rvIsa.Reaches body Q ⟨pc + 1, regs, m⟩) : rvIsa.Reaches body Q ⟨pc, regs, m⟩ :=
  Isa.Reaches.step (by simp [Isa.step, hb]) h

theorem reaches_opn (hag : Agree (ofParts regs m) u) {i : Instr} (hb : body[pc]? = some (.Lopn [] i []))
    (hop : opnOk i = true) (hok : memOkSp1 u i = true)
    (h : ∀ regs' m', Agree (ofParts regs' m') (execInstrBr u i) → rvIsa.Reaches body Q ⟨pc + 1, regs', m'⟩) :
    rvIsa.Reaches body Q ⟨pc, regs, m⟩ := by
  refine Isa.Reaches.step (s' := ⟨pc + 1, regsOf regs (execInstrBr (ofParts regs m) i),
    execInstrBr (ofParts regs m) i⟩) ?_ (h _ _ ((agree_ofParts_regsOf _ _).trans (hag.execInstrBr hop)))
  simp [Isa.step, hb, hop, hag.memOkSp1 i, hok]

theorem reaches_cond (hag : Agree (ofParts regs m) u) {op : String} {a b : Reg} {l : LLabel}
    (hb : body[pc]? = some (.Lcond (.cmp op (.reg (regName a)) (.reg (regName b))) l)) {c : Bool}
    (hc : cmpEval op (u.getReg a) (u.getReg b) = some c) {j : Nat} (hl : labelIdx body l = some j)
    (ht : c = true → rvIsa.Reaches body Q ⟨j, regs, m⟩) (hf : c = false → rvIsa.Reaches body Q ⟨pc + 1, regs, m⟩) :
    rvIsa.Reaches body Q ⟨pc, regs, m⟩ := by
  cases c
  · refine Isa.Reaches.step ?_ (hf rfl)
    simp [Isa.step, hb, regVal_regName hag, hc]
  · refine Isa.Reaches.step ?_ (ht rfl)
    simp [Isa.step, hb, regVal_regName hag, hc, hl]

theorem reaches_goto {n : String} {l : LLabel} (hb : body[pc]? = some (.Lgoto (n, l))) {j : Nat}
    (hl : labelIdx body l = some j) (h : rvIsa.Reaches body Q ⟨j, regs, m⟩) :
    rvIsa.Reaches body Q ⟨pc, regs, m⟩ :=
  Isa.Reaches.step (by simp [Isa.step, hb, hl]) h

theorem halts_ret (hb : body[pc]? = some .Lret) (hQ : Q ⟨body.length + 1, regs, m⟩) :
    rvIsa.Halts body Q ⟨pc, regs, m⟩ :=
  Isa.Reaches.step (by simp [Isa.step, hb]) (Isa.Halts.halt _ _ (by simp [Isa.halted]) hQ)

end Rules

end MachineChecked.Lprog
