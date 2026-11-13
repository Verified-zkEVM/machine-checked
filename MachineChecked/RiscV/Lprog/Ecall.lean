/-
  MachineChecked.RiscV.Lprog.Ecall

  SP1's `ecall` cannot tell agreeing machine states apart.

  Every reader the dispatch uses (`readWords`, `readBytes`, the accelerator payload and
  validity check, the hint length and window check) sees a state only through what `Agree`
  fixes, and every writer (`setMem`, `setReg`, `writeWords`, `writeBytesAsWords`, the commit
  log, the input stream, the pc) keeps `Agree`.

  ## Main results

  * `sp1Ecall_agree`: from two agreeing states at an `ecall`, both trap or both continue, in
    states that agree.
-/

import MachineChecked.RiscV.Lprog.Instance

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog

/-! ## Writers keep agreement -/

theorem Agree.setPC' {u t : MachineState} (h : Agree u t) (p q : Word) :
    Agree (u.setPC p) (t.setPC q) :=
  ⟨fun r => by simp [h.regs], fun a => by simp [h.mem], by simp [h.code], by simp [h.committed],
    by simp [h.publicValues], by simp [h.privateInput], by simp [h.inputBufBase]⟩

theorem Agree.setMem {u t : MachineState} (h : Agree u t) (a v : Word) :
    Agree (u.setMem a v) (t.setMem a v) :=
  ⟨fun r => by simp [getReg_setMem, h.regs], fun x => by simp [getMem_setMem, h.mem],
    by simp [h.code], by simp [h.committed], by simp [h.publicValues], by simp [h.privateInput],
    by simp [h.inputBufBase]⟩

theorem Agree.setReg {u t : MachineState} (h : Agree u t) (r : Reg) (v : Word) :
    Agree (u.setReg r v) (t.setReg r v) :=
  ⟨fun r' => by simp [getReg_setReg, h.regs], fun x => by simp [h.mem],
    by simp [h.code], by simp [h.committed], by simp [h.publicValues], by simp [h.privateInput],
    by simp [h.inputBufBase]⟩

theorem Agree.writeWords {u t : MachineState} (h : Agree u t) (base : Word) (ws : List Word) :
    Agree (u.writeWords base ws) (t.writeWords base ws) := by
  induction ws generalizing u t base with
  | nil => simpa using h
  | cons w ws ih => simpa using ih (h.setMem base w) (base + 8)

theorem Agree.writeBytesAsWords {u t : MachineState} (h : Agree u t) (base : Word)
    (bs : List (BitVec 8)) : Agree (u.writeBytesAsWords base bs) (t.writeBytesAsWords base bs) := by
  match bs with
  | [] => simpa using h
  | b :: bs =>
    unfold MachineState.writeBytesAsWords
    exact Agree.writeBytesAsWords (h.setMem _ _) _ _
termination_by bs.length
decreasing_by simp [List.length_drop]; omega

theorem Agree.withPrivateInput {u t : MachineState} (h : Agree u t) (l : List (BitVec 8)) :
    Agree { u with privateInput := l } { t with privateInput := l } :=
  ⟨fun r => by have := h.regs r; cases r <;> exact this, h.mem, h.code, h.committed,
    h.publicValues, rfl, h.inputBufBase⟩

theorem Agree.appendPublicValues {u t : MachineState} (h : Agree u t) (l : List (BitVec 8)) :
    Agree (u.appendPublicValues l) (t.appendPublicValues l) :=
  ⟨fun r => by simp [h.regs], fun a => by simp [h.mem], by simp [h.code], by simp [h.committed],
    by simp [h.publicValues], by simp [h.privateInput], by simp [h.inputBufBase]⟩

theorem Agree.sp1Commit {u t : MachineState} (h : Agree u t) : Agree u.sp1Commit t.sp1Commit :=
  ⟨fun r => by have := h.regs r; cases r <;> exact this, h.mem, h.code,
    by simp [MachineState.sp1Commit, h.committed, h.regs], h.publicValues, h.privateInput,
    h.inputBufBase⟩

/-! ## Readers cannot tell agreeing states apart -/

theorem Agree.readWords {u t : MachineState} (h : Agree u t) (base : Word) (n : Nat) :
    u.readWords base n = t.readWords base n := by
  induction n generalizing base with
  | zero => simp
  | succ n ih => simp [h.mem, ih]

theorem Agree.readBytes {u t : MachineState} (h : Agree u t) (base : Word) (n : Nat) :
    u.readBytes base n = t.readBytes base n := by
  induction n generalizing base with
  | zero => simp
  | succ n ih => simp [MachineState.getByte, h.mem, ih]

theorem Agree.sp1AccelWrite {u t : MachineState} (h : Agree u t) (id : Word) :
    u.sp1AccelWrite id = t.sp1AccelWrite id := by
  simp only [MachineState.sp1AccelWrite, h.regs, h.readWords]

theorem Agree.sp1AccelValid {u t : MachineState} (h : Agree u t) (id : Word) :
    u.sp1AccelValid id = t.sp1AccelValid id := by
  simp only [MachineState.sp1AccelValid, h.regs, h.readWords]

theorem Agree.execSp1Accel {u t : MachineState} (h : Agree u t) (id : Word) :
    Agree (u.execSp1Accel id) (t.execSp1Accel id) := by
  simp only [MachineState.execSp1Accel, h.sp1AccelWrite]
  exact h.writeWords _ _

theorem Agree.frontHintLen {u t : MachineState} (h : Agree u t) :
    frontHintLen u = frontHintLen t := by
  simp only [RiscvZkvm.Rv64.frontHintLen, h.privateInput]

theorem Agree.hintWindowOk {u t : MachineState} (h : Agree u t) (ptr : Word) (n : Nat) :
    hintWindowOk u ptr n = hintWindowOk t ptr n := by
  simp only [RiscvZkvm.Rv64.hintWindowOk, noCodeAt, h.code]

/-! ## The dispatch -/

/-- Both trap, or both continue in states that agree. -/
private def Rel (x y : Option MachineState) : Prop :=
  (x = none → y = none) ∧ ∀ w, x = some w → ∃ t', y = some t' ∧ Agree w t'

private theorem Rel.trap : Rel none none := ⟨fun _ => rfl, fun _ hw => nomatch hw⟩

private theorem Rel.cont {a b : MachineState} (h : Agree a b) : Rel (some a) (some b) :=
  ⟨fun hn => (nomatch hn), fun _ hw => by cases hw; exact ⟨b, rfl, h⟩⟩

private theorem Rel.ite {c : Prop} [Decidable c] {a a' b b' : Option MachineState}
    (h1 : c → Rel a b) (h2 : ¬c → Rel a' b') :
    Rel (if c then a else a') (if c then b else b') := by
  by_cases hc : c
  · simpa [hc] using h1 hc
  · simpa [hc] using h2 hc

private theorem hintLen_rel {u t : MachineState} (h : Agree u t) : Agree (hintLen u) (hintLen t) := by
  simp only [hintLen, h.frontHintLen]
  exact (h.setReg _ _).setPC' _ _

private theorem hintRead_rel {u t : MachineState} (h : Agree u t) : Rel (hintRead u) (hintRead t) := by
  simp only [hintRead, h.frontHintLen, h.regs, h.hintWindowOk, h.privateInput]
  split
  · exact .trap
  · repeat' refine Rel.ite (fun _ => ?_) (fun _ => ?_)
    all_goals first
      | exact .trap
      | exact .cont ((((h.writeBytesAsWords _ _).setMem _ _).withPrivateInput _).setPC' _ _)

private theorem step_rel {u t : MachineState} (h : Agree u t)
    (hu : u.code u.pc = some .ECALL) (ht : t.code t.pc = some .ECALL) : Rel (step u) (step t) := by
  simp only [step, hu, ht, h.regs, h.readBytes, h.inputBufBase, h.privateInput,
    MachineState.writeOutput, execInstrBr]
  repeat' refine Rel.ite (fun _ => ?_) (fun _ => ?_)
  all_goals first
    | exact .trap
    | exact .cont (h.setPC' _ _)
    | exact .cont ((h.appendPublicValues _).setPC' _ _)
    | exact .cont (((h.setMem _ _).setMem _ _).setPC' _ _)

/-- SP1's `ecall` respects agreement: from two agreeing states at an `ecall`, both trap or
    both continue, in states that agree. -/
theorem sp1Ecall_agree {u t : MachineState} (h : Agree u t)
    (hu : u.code u.pc = some .ECALL) (ht : t.code t.pc = some .ECALL) :
    (sp1Ecall u = none → sp1Ecall t = none) ∧
      ∀ w, sp1Ecall u = some w → ∃ t', sp1Ecall t = some t' ∧ Agree w t' := by
  have key : Rel (sp1Ecall u) (sp1Ecall t) := by
    simp only [sp1Ecall, h.regs, h.sp1AccelValid]
    repeat' refine Rel.ite (fun _ => ?_) (fun _ => ?_)
    all_goals first
      | exact .trap
      | exact .cont ((h.execSp1Accel _).setPC' _ _)
      | exact .cont (hintLen_rel h)
      | exact hintRead_rel h
      | exact .cont (h.sp1Commit.setPC' _ _)
      | exact .cont (h.setPC' _ _)
      | exact step_rel h hu ht
  exact key

end MachineChecked.RiscV.Lprog
