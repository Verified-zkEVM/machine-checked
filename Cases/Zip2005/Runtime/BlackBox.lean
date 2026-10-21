/-
  Cases.Zip2005.BlackBox

  `subtle::black_box::<u8>`: the byte, through a stack slot the optimiser
  cannot see through.

  Proved through the ascent (the first zip-2005 function so proved, in place of its
  symbolic-executor proof): a correspondence over `stepSp1` (`MachineChecked.RiscV.Corres.fn`),
  carried into the continuation form `black_box_spec` by the bridge (`SafeN.of_fn`).

  The function is five instructions: open a 16-byte frame, store the byte at `sp - 1`, load it
  back zero-extended, close the frame, return. The correspondence states the run exactly: five
  steps, ending at `ra` with the frame closed, the byte in `a0`, and memory changed only in the
  frame.
-/

import MachineChecked.RiscV.Corres.Block
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Image.F_7803a0fc
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV MachineChecked.RiscV.Sym

/-- What `black_box` assumes at its entry. -/
def BlackBoxPre (ra sp v : Word) (s : MachineState) : Prop :=
  s.pc = 0x7803a0fc#64 ∧ CodeAt F_7803a0fc.base F_7803a0fc.prog s ∧
  CodeWithin Ro.layout.textLo Ro.layout.textHi s ∧
  s.getReg .x1 = ra ∧ ra &&& ~~~1#64 = ra ∧ s.getReg .x2 = sp ∧ StackOk Ro.layout 0x10 sp ∧
  s.getReg .x10 = v

/-- What `black_box` guarantees at its return. -/
def BlackBoxPost (ra sp v : Word) (s t : MachineState) : Prop :=
  t.pc = ra ∧ CalleeSaved s t ∧ t.code = s.code ∧ Unchanged [(sp - 0x10#64, 2)] s t ∧
  t.getReg .x10 = BitVec.zeroExtend 64 (BitVec.truncate 8 v)

/-- The frame slot the byte goes through, for a 16-byte aligned `sp`. -/
theorem black_box_slot {sp : Word} (h : sp &&& 15#64 = 0#64) :
    alignToDword (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) = sp - 0x8#64 ∧
      byteOffset (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) = 7 := by
  have h1 : alignToDword (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) = sp - 0x8#64 := by
    simp only [alignToDword, signExtend12]; bv_decide (config := { enums := false })
  have h2 : (sp + signExtend12 0xff0#12 + signExtend12 0x00f#12) &&& 7#64 = 7#64 := by
    simp only [signExtend12]; bv_decide (config := { enums := false })
  exact ⟨h1, by simp only [byteOffset, h2]; rfl⟩

/-- **`black_box` as a correspondence over `stepSp1`.** -/
theorem black_box_corres (ra sp v : Word) :
    Corres (Phase.SR (BlackBoxPost ra sp v)) (Phase.Pre (BlackBoxPre ra sp v)) Phase.run 5 := by
  apply Corres.fn
  rintro s ⟨hpc, hcode, hcw, hra, hra1, hsp, hstk, ha0⟩
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
    rw [show sp + BitVec.signExtend 64 0xff0#12 + BitVec.signExtend 64 0x00f#12 = sp - 1#64 by bv_decide (config := { enums := false }),
      BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]; omega
  have hinMem := hokF.inMem
  have hoffCode := hokF.offCode
  have hb : F_7803a0fc.base = 0x7803a0fc#64 := rfl
  have fetch : ∀ i (hi : i < F_7803a0fc.prog.length) {ins : Instr}, F_7803a0fc.prog[i]! = some ins →
      ∀ u : MachineState, u.code = s.code → u.pc = 0x7803a0fc#64 + BitVec.ofNat 64 (4 * i) →
        u.code u.pc = some ins := fun i hi ins hprog u hc hpcu =>
    fetch_of_codeAt (codeAt_of_code_eq hc hcode) i hi hprog (hb ▸ hpcu)
  have hsimp : ∀ u : MachineState, u = u := fun _ => rfl
  clear hsimp
  -- addi sp, sp, -16
  refine reach_plain (fetch 0 (by decide) rfl s rfl (by rw [hpc]; rfl)) rfl (by decide) (by decide) ?_
  -- sb a0, 15(sp)
  refine reach_mem (fetch 1 (by decide) rfl _ (by simp [execInstrBr])
    (by simp [execInstrBr, MachineState.setPC, hpc])) rfl rfl ?_ ?_
  · apply memOk_SB
    · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, hsp, reduceCtorEq,
        if_true, ne_eq, not_false_eq_true, and_self]
      apply isValidMemAddrSp1_of_lt; rw [haddr]; omega
    · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, hsp, reduceCtorEq,
        if_true, ne_eq, not_false_eq_true, and_self]
      apply noCodeAt_of_codeWithin (codeWithin_of_code_eq (by simp) hcw) _ 1 (by decide)
      · rw [haddr]; omega
      · rw [haddr]; omega
  -- lbu a0, 15(sp)
  refine reach_mem (fetch 2 (by decide) rfl _ (by simp [execInstrBr])
    (by simp [execInstrBr, MachineState.setPC, hpc])) rfl rfl ?_ ?_
  · apply memOk_LBU
    simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, hsp, reduceCtorEq,
      if_true, ne_eq, not_false_eq_true, and_self, getReg_setByte']
    apply isValidMemAddrSp1_of_lt; rw [haddr]; omega
  -- addi sp, sp, 16
  refine reach_plain (fetch 3 (by decide) rfl _ (by simp [execInstrBr])
    (by simp [execInstrBr, MachineState.setPC, hpc])) rfl (by decide) (by decide) ?_
  -- ret
  refine reach_plain (fetch 4 (by decide) rfl _ (by simp [execInstrBr])
    (by simp [execInstrBr, MachineState.setPC, hpc])) rfl (by decide) (by decide) ?_
  have hst : ∀ (r : Reg), r ≠ .x2 → r ≠ .x10 → r ≠ .x0 →
      (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.ADDI .x2 .x2 0xff0#12))
        (.SB .x2 .x10 0x00f#12)) (.LBU .x10 .x2 0x00f#12)) (.ADDI .x2 .x2 0x010#12))
        (.JALR .x0 .x1 0x000#12)).getReg r = s.getReg r := by
    intro r h2 h10 h0
    simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, getReg_setByte']
    simp [Ne.symm h2, Ne.symm h10, Ne.symm h0]
  refine reach_done ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [execInstrBr, pc_setPC', MachineState.getReg_setPC, getReg_setReg_ite,
      getReg_setByte', hra, reduceCtorEq, false_and, if_false, signExtend12]
    rw [show ra + BitVec.signExtend 64 (0x000#12) = ra by simp]; exact hra1
  · intro r hr
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hsp16 : sp + signExtend12 0xff0#12 + signExtend12 0x010#12 = sp := by
        simp only [signExtend12]; bv_decide (config := { enums := false })
      simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, getReg_setByte', hsp,
        reduceCtorEq, if_true, if_false, ne_eq, not_false_eq_true, and_self, false_and]
      exact hsp16
    all_goals exact hst _ (by decide) (by decide) (by decide)
  · simp
  · intro a ha
    have hne : a ≠ sp - 0x8#64 := by
      rintro rfl
      apply ha _ (List.mem_singleton.2 rfl)
      constructor <;> · rw [hfrm]; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
    simp only [execInstrBr, MachineState.getMem_setPC, MachineState.getMem_setReg, MachineState.setByte,
      getReg_setReg_ite, MachineState.getReg_setPC, getReg_setMem', hsp, reduceCtorEq, if_true, ne_eq,
      not_false_eq_true, and_self]
    rw [hslot, MachineState.getMem_setMem_ne hne]
    simp
  · simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_ite, getReg_setMem', hsp, ha0,
      reduceCtorEq, if_true, if_false, ne_eq, not_false_eq_true, and_self, false_and,
      MachineState.getByte, MachineState.setByte, MachineState.getMem_setPC, MachineState.getMem_setReg]
    rw [hslot, hoff, MachineState.getMem_setMem_eq, extractByte_replaceByte _ 7 (by decide)]

/-- The continuation form, from the correspondence. -/
theorem black_box_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (ra sp v : Word)
    (hpc : s.pc = 0x7803a0fc#64) (hcode : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp) (ha0 : s.getReg .x10 = v)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2)] s t →
      t.getReg .x10 = BitVec.zeroExtend 64 (BitVec.truncate 8 v) → SafeN G n P t) :
    SafeN G n P s :=
  SafeN.of_fn (black_box_corres ra sp v) ⟨hpc, hcode, hcw, hra, hra1, hsp, hstk, ha0⟩
    (fun t ⟨h1, h2, h3, h4, h5⟩ => hk t h1 h2 h3 h4 h5)

end Cases.Zip2005
