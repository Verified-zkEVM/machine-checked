/-
  MachineChecked.ARM.Lift.Transfer

  **The lift of AArch64 is correct**: `SafeN` proved at Lprog for a lifted program gives
  `SafeN` over arm64-semantics' `Step`. In progress: this file has the two systems, the
  simulation relation, and how a run of an instruction's operations is steps of the program.

  ## Main definitions

  * `armCtx`, `lsys`, `mstep`: the lifted program and the machine, as systems
  * `ProgOk`, `Loaded`, `Chain`, `Sim`: the simulation

  ## Main results

  * `step_of_fetch`: the machine's step at a fetched instruction
  * `steps_ops`: the operations of an instruction, as steps of the program
-/

import MachineChecked.ARM.Lift.Sound
import Lprog.LinkedSpec
import Lprog.Ascent.Transfer

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build Lprog.Linked
open Lprog.Ascent (Outcome Steps GoesWrong System)
open Arm64 (Instr RegWidth MemWidth AddrMode)

/-! ## The two systems -/

/-- **The context of a lifted AArch64 program**: an external call is not lifted, and goes
    `wrong`. -/
def armCtx : Context armIsa Unit := ⟨fun _ _ _ o => o = .wrong, fun _ _ _ => False⟩

/-- The lifted program, as a system. -/
abbrev lsys (fns : List Fun) : System (State armIsa) Unit := armIsa.system (liftArm fns) armCtx

/-- **AArch64 as arm64-semantics steps it**: a step to a running state. A step to a state
    that is not running (a fault, a halt, an exit) is a trap; nothing is `wrong`. -/
def mstep (prog : Arm64.Program) (t : Arm64.State) : Outcome Arm64.State → Prop
  | .ok t' => Arm64.Step prog t t' ∧ t'.status = .Running
  | .trap => ∃ t', Arm64.Step prog t t' ∧ t'.status ≠ .Running
  | .wrong => False

/-- **The machine's step at an instruction it fetches** is the execution of that
    instruction. -/
theorem step_of_fetch {prog : Arm64.Program} {t t' : Arm64.State} {i : Instr}
    (hrun : t.status = .Running) (hf : prog.fetchMem t.mem t.pc = some i) :
    Arm64.Step prog t t' ↔ t' = prog.evalInst i t := by
  constructor
  · intro h
    cases h with
    | exec _ h_fetch => rw [hf] at h_fetch; cases h_fetch; rfl
    | halt_unmapped _ h_fetch => rw [hf] at h_fetch; cases h_fetch
    | extern _ h_ext => simp [Arm64.Program.fetchMem, h_ext] at hf
    | extern_fault _ h_ext => simp [Arm64.Program.fetchMem, h_ext] at hf
  · rintro rfl
    exact .exec hrun hf

/-! ## Operations as steps -/

section steps

variable {p : Lprog O Reg} {fd : Lfundef O Reg} {fn : Nat}

/-- **The operations of an instruction, as steps of the program**: where they run, the
    program steps past them; where they fault, it steps to a trap. -/
theorem steps_ops (hf : p[fn]? = some fd) {os : List O} {P : Nat}
    (hb : ∀ j (hj : j < os.length), fd.body[P + j]? = some (.Lopn os[j]))
    (rv top : BitVec 64) (rest : List Frame) (regs : Reg → BitVec 64) (m : Arm64.Memory) :
    match run os regs m with
    | some (r', m') => Steps (armIsa.system p armCtx) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ []
        ⟨⟨fn, P + os.length, rv, top⟩ :: rest, r', m'⟩
    | none => ∃ s', Steps (armIsa.system p armCtx) ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩ [] s' ∧
        ¬ armIsa.accept p armCtx s' ∧ armIsa.step p armCtx s' .trap := by
  induction os generalizing P regs m with
  | nil => exact .refl _
  | cons o os ih =>
    have h0 : fd.body[P]? = some (.Lopn o) := hb 0 (by simp)
    have hb' : ∀ j (hj : j < os.length), fd.body[P + 1 + j]? = some (.Lopn os[j]) := by
      intro j hj
      have := hb (j + 1) (by simpa using hj)
      rw [show P + (j + 1) = P + 1 + j by omega] at this
      exact this
    rw [run_cons]
    cases he : o.eval armMem regs m with
    | none =>
      refine ⟨_, .refl _, Lprog.SafeN.not_accept hf h0 (by simp), ?_⟩
      exact (Lprog.SafeN.step_eq (fr := ⟨fn, P, rv, top⟩) hf h0 _).2 (by simp [Isa.stepI, he])
    | some rm =>
      obtain ⟨r1, m1⟩ := rm
      have hs : (armIsa.system p armCtx).step ⟨⟨fn, P, rv, top⟩ :: rest, regs, m⟩
          (.ok (⟨⟨fn, P + 1, rv, top⟩ :: rest, r1, m1⟩, [])) :=
        (Lprog.SafeN.step_eq (fr := ⟨fn, P, rv, top⟩) hf h0 _).2 (by simp [Isa.stepI, he, Frame.at])
      have := ih hb' r1 m1
      simp only [Option.bind_some]
      cases hr : run os r1 m1 with
      | none =>
        rw [hr] at this
        obtain ⟨s', hs', h1, h2⟩ := this
        exact ⟨s', by simpa using Steps.step hs hs', h1, h2⟩
      | some rm' =>
        obtain ⟨r', m'⟩ := rm'
        rw [hr] at this
        have h2 := Steps.step hs this
        rw [show P + 1 + os.length = P + (o :: os).length by simp; omega] at h2
        simpa using h2

end steps

/-! ## No command of an instruction is a label -/

/-- No command is a label. -/
def NoLab (cs : Lcmd O Reg) : Prop := ∀ c ∈ cs, ∀ l, isLabel l c = false

theorem NoLab.nil : NoLab [] := fun _ h => by cases h

theorem NoLab.append {a b : Lcmd O Reg} (ha : NoLab a) (hb : NoLab b) : NoLab (a ++ b) :=
  fun c hc l => (List.mem_append.1 hc).elim (ha c · l) (hb c · l)

theorem NoLab.cons {c : LinstrR O Reg} {cs : Lcmd O Reg} (hc : ∀ l, isLabel l c = false)
    (hcs : NoLab cs) : NoLab (c :: cs) := fun d hd l => by
  rcases List.mem_cons.1 hd with rfl | hd
  · exact hc l
  · exact hcs d hd l

theorem NoLab.opns (os : List O) : NoLab (os.map .Lopn) := fun c hc l => by
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 hc; rfl

theorem noLab_spCheck (cx : Cx) (os : List O) : NoLab (spCheck cx os) := by
  unfold spCheck
  split
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)
  · exact .nil

theorem noLab_toLabel (cx : Cx) (a : BitVec 64) {k : LLabel → Lcmd O Reg} (hk : ∀ l, NoLab (k l)) :
    NoLab (toLabel cx a k) := by
  unfold toLabel
  split
  · exact hk _
  · exact .cons (fun _ => rfl) .nil

theorem noLab_branch (c : Arm64.CondCode) (l : LLabel) : NoLab (branch c l) := by
  cases c <;> simp [branch, NoLab, isLabel]

theorem noLab_jump (e : E) (locals : List (BitVec 64 × LLabel)) (fns : List Nat) :
    NoLab (Linked.jump .t2 e [] locals fns) := by
  unfold Linked.jump
  split
  · split <;> exact .cons (fun _ => rfl) .nil
  · refine .append (.append (.append (.cons (fun _ => rfl) .nil) .nil) ?_) ?_
    · intro c hc l
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc; rfl
    · split <;> exact .cons (fun _ => rfl) .nil

/-- **No command the lift writes for an instruction is a label**, so a label is found at the
    instruction it names. -/
theorem noLab_liftI (cx : Cx) (prev : Option (At (Option Instr))) (i : At (Option Instr)) :
    NoLab (liftI cx prev i) := by
  unfold liftI
  split
  · exact .cons (fun _ => rfl) .nil
  · unfold liftB; split <;> exact .cons (fun _ => rfl) .nil
  · unfold liftBl; split <;> exact .cons (fun _ => rfl) .nil
  · exact noLab_toLabel _ _ fun l => noLab_branch _ l
  · refine noLab_toLabel _ _ fun l => ?_
    unfold liftCbz
    repeat' split
    all_goals first
      | exact .nil
      | exact .cons (fun _ => rfl) .nil
      | exact .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)
  · refine noLab_toLabel _ _ fun l => ?_
    unfold liftTbz
    split
    · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)
    · exact .cons (fun _ => rfl) .nil
  · split
    · exact noLab_jump _ _ _
    · exact .cons (fun _ => rfl) .nil
  · split <;> exact .cons (fun _ => rfl) .nil
  · split <;> exact .cons (fun _ => rfl) .nil
  · exact .cons (fun l => by split <;> rfl) .nil
  · unfold liftOps
    repeat' split
    all_goals first
      | exact .append (.opns _) (noLab_spCheck _ _)
      | exact .cons (fun _ => rfl) .nil

end MachineChecked.ARM.Lift
