/-
  MachineChecked.ARM.Lift.Sound

  The lift of AArch64 against arm64-semantics, an instruction at a time: the operations the
  lift writes for an instruction (`ops`) compute what the machine's execution of it
  (`Arm64.execInstWithSvc`) does.

  `ops_sound` says it of an instruction that does not transfer control: if the registers and
  the memory of Lprog stand for a machine state (`Agree`) and the operations run, then they
  stand for the state the machine steps to, which is not a fault, with the counter on the
  next instruction. The lift faults where the machine's permission check does, so nothing is
  claimed where the operations do not run.

  `Ok` is what the proof asks of the instruction, and is not yet checked by the lift:

  * its registers are ones the decoder gives (`Wf`), its shifts are below the width, and the
    like: properties of what `Arm64.decode` returns;
  * with write-back, the register loaded or stored is not the base, which the architecture
    leaves unpredictable;
  * **the stack pointer is aligned** when it is the base of an access. The machine faults
    there if it is not, and the lift does not: the lift is to check it.

  The kinds of instruction proved are those of `Ok`. Not proved yet: the bit fields, `extr`,
  the reversals and counts, addition with carry and signed division. This is milestone M4 of
  `docs/NativeVerifiers.md`, in progress; the instructions that transfer control and the
  simulation of the program are to come.

  ## Main definitions

  * `Ok`

  ## Main results

  * `ops_sound`
-/

import MachineChecked.ARM.Lift.Sound.Basic
import MachineChecked.ARM.Lift.Sound.AddSub
import MachineChecked.ARM.Lift.Sound.Logical
import MachineChecked.ARM.Lift.Sound.Move
import MachineChecked.ARM.Lift.Sound.Compare
import MachineChecked.ARM.Lift.Sound.Arith
import MachineChecked.ARM.Lift.Sound.Memory

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth AddrMode)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- **What the proof asks of an instruction**, in a machine state. An instruction of a kind
    that is not proved is not `Ok`. -/
def Ok (s : Arm64.State) : Instr → Prop
  | .nop => True
  | .adr _ dst _ => Wf dst
  | .addSubImm _ _ dst rn _ _ => Wf dst ∧ Wf rn
  | .addSubShift w _ dst rn rm _ n => Wf dst ∧ Wf rn ∧ Wf rm ∧ n < w.bits
  | .addSubExt _ _ dst rn rm _ n => Wf dst ∧ Wf rn ∧ Wf rm ∧ n < 64
  | .logicalImm _ _ dst rn _ => Wf dst ∧ Wf rn
  | .logicalShift w _ dst rn rm _ n => Wf dst ∧ Wf rn ∧ Wf rm ∧ n < w.bits
  | .moveWide w _ dst _ hw => Wf dst ∧ (hw = 0 ∨ hw = 16 ∨ (w = .W64 ∧ (hw = 32 ∨ hw = 48)))
  | .condSelect _ _ dst rn rm _ => Wf dst ∧ Wf rn ∧ Wf rm
  | .condCompareReg _ _ rn rm _ _ => Wf rn ∧ Wf rm
  | .condCompareImm _ _ rn _ _ _ => Wf rn
  | .dataProc2 _ op dst rn rm => Wf dst ∧ Wf rn ∧ Wf rm ∧ op ≠ .SDIV
  | .dataProc3 w op dst rn rm ra =>
    Wf dst ∧ Wf rn ∧ Wf rm ∧ Wf ra ∧ (w = .W64 ∨ op = .MADD ∨ op = .MSUB)
  | .ldr w sz _ rt mode => Wf rt ∧ WfMode mode ∧ Arm64.checkAddrSPAligned s mode = true ∧
      (∀ b ∈ writeback mode, rt ≠ b) ∧ (w = .W32 → sz ≠ .X64)
  | .ldrLit w sgn rt _ => Wf rt ∧ (sgn = true → w = .W64)
  | .str _ rt mode => Wf rt ∧ WfMode mode ∧ Arm64.checkAddrSPAligned s mode = true ∧
      (∀ b ∈ writeback mode, rt ≠ b)
  | .ldp _ _ rt1 rt2 mode => Wf rt1 ∧ Wf rt2 ∧ WfMode mode ∧
      Arm64.checkAddrSPAligned s mode = true ∧ (∀ b ∈ writeback mode, rt1 ≠ b ∧ rt2 ≠ b)
  | .stp _ rt1 rt2 mode => Wf rt1 ∧ Wf rt2 ∧ WfMode mode ∧
      Arm64.checkAddrSPAligned s mode = true
  | _ => False

/-- An instruction that writes registers only: the machine is on the next instruction, and
    has not faulted. -/
theorem next_of_data {s' : Arm64.State} {r' : Reg → BitVec 64} {os : List O}
    (h : ∃ R, run os regs m = some (R, m) ∧ Agree R m s') {m' : Arm64.Memory}
    (hrun : run os regs m = some (r', m')) (hst : s'.status = s.status)
    (hpc : s'.pc = s.pc + 4#64) :
    Agree r' m' s' ∧ s'.status = s.status ∧ s'.pc = s.pc + 4#64 := by
  obtain ⟨R, h1, h2⟩ := h
  rw [h1] at hrun
  cases hrun
  exact ⟨h2, hst, hpc⟩

/-- A state with flags set or not is no fault, and on the next instruction. -/
theorem next_flags (s1 : Arm64.State) (o : Option Arm64.PState) (hst : s1.status = s.status)
    (hpc : s1.pc = s.pc) :
    let s2 := (match o with | some ps => s1.setPState ps | none => s1).advancePC
    s2.status = s.status ∧ s2.pc = s.pc + 4#64 := by
  cases o <;> exact ⟨hst, congrArg (· + 4#64) hpc⟩

/-- **The lift of an instruction that does not transfer control is sound.** -/
theorem ops_sound (h : Agree regs m s) (svc : Arm64.State → Arm64.State) {i : Instr}
    (hok : Ok s i) {os : List O} (ho : ops s.pc i = some os) {r' : Reg → BitVec 64}
    {m' : Arm64.Memory} (hrun : run os regs m = some (r', m')) :
    Agree r' m' (Arm64.execInstWithSvc svc i s) ∧
      (Arm64.execInstWithSvc svc i s).status = s.status ∧
      (Arm64.execInstWithSvc svc i s).pc = s.pc + 4#64 := by
  cases i
  case nop =>
    cases ho
    exact next_of_data (nop_sound h) hrun rfl rfl
  case adr page dst off =>
    cases ho
    exact next_of_data (adr_sound h hok page off) hrun rfl rfl
  case addSubImm w op dst rn imm12 shift12 =>
    obtain ⟨hd, hn⟩ := hok
    cases ho
    have := next_flags (s := s) (s.writeReg w dst (Arm64.evalAddSub w op (s.readReg w rn)
      (if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64) none).1)
      (Arm64.evalAddSub w op (s.readReg w rn)
      (if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64) none).2 rfl rfl
    exact next_of_data (addSubImm_sound h w op hd hn imm12 shift12) hrun this.1 this.2
  case addSubShift w op dst rn rm ty n =>
    obtain ⟨hd, hn, hrm, hlt⟩ := hok
    cases ho
    have := next_flags (s := s) (s.writeReg w dst (Arm64.evalAddSub w op (s.readReg w rn)
      (Arm64.shiftVal w (s.readReg w rm) ty n) none).1)
      (Arm64.evalAddSub w op (s.readReg w rn) (Arm64.shiftVal w (s.readReg w rm) ty n) none).2
      rfl rfl
    exact next_of_data (addSubShift_sound h w op hd hn hrm ty hlt) hrun this.1 this.2
  case addSubExt w op dst rn rm ext n =>
    obtain ⟨hd, hn, hrm, hlt⟩ := hok
    cases ho
    have := next_flags (s := s) (s.writeReg w dst (Arm64.evalAddSub w op (s.readReg w rn)
      (Arm64.extendVal w (s.readReg64 rm) ext n) none).1)
      (Arm64.evalAddSub w op (s.readReg w rn) (Arm64.extendVal w (s.readReg64 rm) ext n) none).2
      rfl rfl
    exact next_of_data (addSubExt_sound h w op hd hn hrm ext hlt) hrun this.1 this.2
  case logicalImm w op dst rn mask =>
    obtain ⟨hd, hn⟩ := hok
    obtain ⟨os', ho', hr⟩ := logicalImm_sound h w op hd hn mask
    have := next_flags (s := s) (s.writeReg w dst (Arm64.evalLogical w op (s.readReg w rn)
      mask s.pstate).1) (Arm64.evalLogical w op (s.readReg w rn) mask s.pstate).2 rfl rfl
    cases ho.symm.trans ho'
    exact next_of_data hr hrun this.1 this.2
  case logicalShift w op dst rn rm ty n =>
    obtain ⟨hd, hn, hrm, hlt⟩ := hok
    obtain ⟨os', ho', hr⟩ := logicalShift_sound h w op hd hn hrm ty hlt
    have := next_flags (s := s) (s.writeReg w dst (Arm64.evalLogical w op (s.readReg w rn)
      (Arm64.shiftVal w (s.readReg w rm) ty n) s.pstate).1)
      (Arm64.evalLogical w op (s.readReg w rn) (Arm64.shiftVal w (s.readReg w rm) ty n)
        s.pstate).2 rfl rfl
    cases ho.symm.trans ho'
    exact next_of_data hr hrun this.1 this.2
  case moveWide w op dst imm16 hw =>
    cases ho
    exact next_of_data (moveWide_sound h w op hok.1 imm16 hok.2) hrun rfl rfl
  case condSelect w op dst rn rm c =>
    obtain ⟨hd, hn, hrm⟩ := hok
    cases ho
    exact next_of_data (condSelect_sound h w op hd hn hrm c) hrun rfl rfl
  case condCompareReg w isSub rn rm nzcv c =>
    cases ho
    have e := execCondCompare_eq w isSub false rn rm 0#64 nzcv c s
    exact next_of_data (condCompareReg_sound h w isSub hok.1 hok.2 nzcv c) hrun
      (by rw [e]; rfl) (by rw [e]; rfl)
  case condCompareImm w isSub rn imm5 nzcv c =>
    cases ho
    have e := execCondCompare_eq w isSub true rn .xzr (imm5.zeroExtend 64) nzcv c s
    exact next_of_data (condCompareImm_sound h w isSub hok imm5 nzcv c) hrun
      (by rw [e]; rfl) (by rw [e]; rfl)
  case dataProc2 w op dst rn rm =>
    obtain ⟨hd, hn, hrm, hop⟩ := hok
    cases ho
    by_cases hu : op = .UDIV
    · subst hu
      exact next_of_data (udiv_sound h w hd hn hrm) hrun rfl rfl
    · exact next_of_data (shiftv_sound h w op hd hn hrm ⟨hu, hop⟩) hrun rfl rfl
  case dataProc3 w op dst rn rm ra =>
    obtain ⟨hd, hn, hrm, hra, hw⟩ := hok
    cases ho
    exact next_of_data (dataProc3_sound h w op hd hn hrm hra hw) hrun rfl rfl
  case ldr w sz sgn rt mode =>
    obtain ⟨hrt, hm, hal, hap, hsz⟩ := hok
    cases ho
    exact ldr_sound h w sz sgn hrt hm hal hap hsz hrun
  case ldrLit w sgn rt off =>
    cases ho
    have := ldrLit_sound h w sgn hok.1 off hok.2 hrun
    cases w <;> cases sgn <;> exact this
  case str sz rt mode =>
    obtain ⟨hrt, hm, hal, hap⟩ := hok
    cases ho
    exact str_sound h sz hrt hm hal hap hrun
  case ldp w sgn rt1 rt2 mode =>
    obtain ⟨h1, h2, hm, hal, hap⟩ := hok
    cases ho
    exact ldp_sound h w sgn h1 h2 hm hal hap hrun
  case stp w rt1 rt2 mode =>
    obtain ⟨h1, h2, hm, hal⟩ := hok
    cases ho
    exact stp_sound h w h1 h2 hm hal hrun
  all_goals exact hok.elim

end MachineChecked.ARM.Lift
