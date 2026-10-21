/-
  Cases.Zip2005.BlackBox

  `subtle::black_box::<u8>`: the byte, through a stack slot the optimiser
  cannot see through.

  Proved at Lprog and carried down to `stepSp1` by the lift, like `MemcmpLprog`. The function
  is five instructions: open a 16-byte frame, store the byte at `sp - 1`, load it back
  zero-extended, close the frame, return. At Lprog the body runs to its return in a state
  standing for the machine after the first four (`halts`, with the two memory checks as side
  conditions); `reach_of_halts` turns that into a run over `stepSp1`, and what the
  specification asks of the end state (the frame closed, the byte in `a0`, memory changed only
  in the frame) is read off those four instructions.
-/

import MachineChecked.RiscV.Lprog.Lift
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Image.F_7803a0fc
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005.BlackBox

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV MachineChecked.RiscV.Sym
open MachineChecked.Lprog MachineChecked.RiscV.Lprog

/-- The instructions of `black_box`. -/
def prog : List Instr := F_7803a0fc.prog.filterMap id

theorem prog_map : prog.map some = F_7803a0fc.prog := by decide

theorem wf : WF prog := by unfold WF; decide

/-- The machine after the body, before the return. -/
def body (u : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr u (.ADDI .x2 .x2 0xff0#12))
    (.SB .x2 .x10 0x00f#12)) (.LBU .x10 .x2 0x00f#12)) (.ADDI .x2 .x2 0x010#12)

/-- **`black_box` at Lprog**: from the entry, the run halts at the return, in a state standing
    for `body u0`. -/
theorem halts (u0 : MachineState) (regs : String → BitVec 64) (m : MachineState)
    (hag : Agree (ofParts regs m) u0)
    (hSB : memOkSp1 (execInstrBr u0 (.ADDI .x2 .x2 0xff0#12)) (.SB .x2 .x10 0x00f#12) = true)
    (hLBU : memOkSp1 (execInstrBr (execInstrBr u0 (.ADDI .x2 .x2 0xff0#12))
      (.SB .x2 .x10 0x00f#12)) (.LBU .x10 .x2 0x00f#12) = true) :
    rvIsa.Halts (lift prog)
      (fun s => s.pc = 2 * prog.length + 1 ∧ Agree (ofParts s.regs s.m) (body u0)) ⟨0, regs, m⟩ := by
  apply reaches_label (kd := .internal) (l := 0) (by decide)
  apply reaches_opn hag (i := .ADDI .x2 .x2 0xff0#12) (by decide) rfl rfl
  intro r1 m1 hag1
  apply reaches_label (kd := .internal) (l := 1) (by decide)
  apply reaches_opn hag1 (i := .SB .x2 .x10 0x00f#12) (by decide) rfl hSB
  intro r2 m2 hag2
  apply reaches_label (kd := .internal) (l := 2) (by decide)
  apply reaches_opn hag2 (i := .LBU .x10 .x2 0x00f#12) (by decide) rfl hLBU
  intro r3 m3 hag3
  apply reaches_label (kd := .internal) (l := 3) (by decide)
  apply reaches_opn hag3 (i := .ADDI .x2 .x2 0x010#12) (by decide) rfl rfl
  intro r4 m4 hag4
  apply reaches_label (kd := .internal) (l := 4) (by decide)
  exact halts_ret (by decide) ⟨congrArg (· + 1) (length_liftFrom 0 prog), hag4⟩

end Cases.Zip2005.BlackBox

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV MachineChecked.RiscV.Sym
open MachineChecked.Lprog MachineChecked.RiscV.Lprog

/-- The frame slot the byte goes through, for a 16-byte aligned `sp`. -/
theorem black_box_slot {sp : Word} (h : sp &&& 15#64 = 0#64) :
    alignToDword (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) = sp - 0x8#64 ∧
      byteOffset (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) = 7 := by
  have h1 : alignToDword (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) = sp - 0x8#64 := by
    simp only [alignToDword, signExtend12]; bv_decide (config := { enums := false })
  have h2 : (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) &&& 7#64 = 7#64 := by
    simp only [signExtend12]; bv_decide (config := { enums := false })
  exact ⟨h1, by simp only [byteOffset, h2]; rfl⟩

/-- **`black_box` over `stepSp1`**, in continuation form. -/
theorem black_box_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (ra sp v : Word)
    (hpc : s.pc = 0x7803a0fc#64) (hcode : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp) (ha0 : s.getReg .x10 = v)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2)] s t →
      t.getReg .x10 = BitVec.zeroExtend 64 (BitVec.truncate 8 v) → SafeN G n P t) :
    SafeN G n P s := by
  -- the frame
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hlo := hstk.lo
  have hal : sp &&& 15#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    simp only [BitVec.toNat_ofNat]
    rw [show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    exact hstk.aligned
  obtain ⟨hslot, hoff⟩ := black_box_slot hal
  have hfrm : (sp - 0x10#64).toNat = sp.toNat - 16 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have haddr : (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12).toNat = sp.toNat - 1 := by
    simp only [signExtend12]
    rw [show sp + BitVec.signExtend 64 0xff0#12 + BitVec.signExtend 64 0x00f#12 = sp - 1#64 by
        bv_decide (config := { enums := false }),
      BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]; omega
  have hinMem := hokF.inMem
  have hoffCode := hokF.offCode
  -- the two memory checks
  have hSB : memOkSp1 (execInstrBr s (.ADDI .x2 .x2 0xff0#12)) (.SB .x2 .x10 0x00f#12) = true := by
    apply memOk_SB
    · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg, hsp, reduceCtorEq,
        if_true, ne_eq, not_false_eq_true, and_self]
      apply isValidMemAddrSp1_of_lt; rw [haddr]; omega
    · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg, hsp, reduceCtorEq,
        if_true, ne_eq, not_false_eq_true, and_self]
      apply noCodeAt_of_codeWithin (codeWithin_of_code_eq (by simp) hcw) _ 1 (by decide)
      · rw [haddr]; omega
      · rw [haddr]; omega
  have hLBU : memOkSp1 (execInstrBr (execInstrBr s (.ADDI .x2 .x2 0xff0#12))
      (.SB .x2 .x10 0x00f#12)) (.LBU .x10 .x2 0x00f#12) = true := by
    apply memOk_LBU
    simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg, hsp, reduceCtorEq,
      if_true, ne_eq, not_false_eq_true, and_self, getReg_setByte]
    apply isValidMemAddrSp1_of_lt; rw [haddr]; omega
  -- run at Lprog, carried down
  have hc : CodeAt F_7803a0fc.base (BlackBox.prog.map some) s := BlackBox.prog_map ▸ hcode
  refine SafeN.of_reaches (reach_of_halts BlackBox.wf (sim_entry (fun _ => 0) hc hpc)
    (BlackBox.halts s _ _ (agree_ofParts_regsOf _ s) hSB hLBU)) ?_
  rintro t ⟨s', hs', hpc', hag'⟩
  have hU : Agree t (BlackBox.body s) := hs'.agree.symm.trans hag'
  have hst : ∀ (r : Reg), r ≠ .x2 → r ≠ .x10 → (BlackBox.body s).getReg r = s.getReg r := by
    intro r h2 h10
    simp only [BlackBox.body, execInstrBr, MachineState.getReg_setPC, getReg_setReg, getReg_setByte]
    simp [h2, h10]
  apply hk
  · rcases hs'.pc with ⟨hle, -⟩ | ⟨-, ht⟩
    · rw [hpc'] at hle; omega
    · rw [ht, hU.regs, hst .x1 (by decide) (by decide), hra, hra1]
  · intro r hr
    rw [hU.regs]
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hsp16 : sp + signExtend12 0xff0#12 + signExtend12 0x010#12 = sp := by
        simp only [signExtend12]; bv_decide (config := { enums := false })
      simp only [BlackBox.body, execInstrBr, MachineState.getReg_setPC, getReg_setReg,
        getReg_setByte, hsp, reduceCtorEq, if_true, if_false, ne_eq, not_false_eq_true, and_self,
        false_and]
      exact hsp16
    all_goals exact hst _ (by decide) (by decide)
  · rw [hU.code]; simp [BlackBox.body, execInstrBr]
  · intro a ha
    have hne : a ≠ sp - 0x8#64 := by
      rintro rfl
      apply ha _ (List.mem_singleton.2 rfl)
      constructor <;> · rw [hfrm]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    rw [hU.mem]
    simp only [BlackBox.body, execInstrBr, MachineState.getMem_setPC, MachineState.getMem_setReg,
      MachineState.setByte, getReg_setReg, MachineState.getReg_setPC, getReg_setMem, hsp,
      reduceCtorEq, if_true, ne_eq, not_false_eq_true, and_self]
    rw [hslot, MachineState.getMem_setMem_ne hne]
    simp
  · rw [hU.regs]
    simp only [BlackBox.body, execInstrBr, MachineState.getReg_setPC, getReg_setReg, getReg_setMem,
      hsp, ha0, reduceCtorEq, if_true, if_false, ne_eq, not_false_eq_true, and_self, false_and,
      MachineState.getByte, MachineState.setByte, MachineState.getMem_setPC,
      MachineState.getMem_setReg]
    rw [hslot, hoff, MachineState.getMem_setMem_eq, extractByte_replaceByte _ 7 (by decide)]

end Cases.Zip2005
