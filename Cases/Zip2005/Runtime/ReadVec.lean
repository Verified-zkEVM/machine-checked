/-
  Cases.Zip2005.Runtime.ReadVec

  `read_vec_raw` (`0x7801beb0`), sp1-zkvm's input primitive (phase D2).

  It asks `HINT_LEN` for the front hint's length `n`. With none (`u64::MAX`) it returns
  `{0, 0, 0}`. Otherwise it bump-allocates `cap = (n + 7) & !7` bytes from the pointer at
  `BUMP` (`.data`, loaded as `0x1C00000000`, the end of the TLSF arena), panicking if that
  overflows or passes `1 << 37`; it stores the new bump pointer, `HINT_READ`s the hint into
  the buffer and returns `{ptr, n, cap}` through `a0`.

  `spec` needs only the entry and the code: a trap (a misaligned pointer, a store or hint
  window SP1 rejects) ends the run, which is safe. `Done` gives the exact memory and input
  after a return; `Panic` the state at the call to `core::panicking::panic_fmt` (D5 discharges
  it). Note SP1 always writes a zero-padded last doubleword at `p + 8 (n / 8)`: when `8 ∣ n`
  that is `p + cap`, one doubleword past the reservation (`readMem`).
-/

import Cases.Zip2005.Runtime.Entry
import Cases.Zip2005.Runtime.Alloc.Exec
import MachineChecked.RiscV.Exec.Hint

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.ReadVec

open RiscvZkvm.Rv64
open MachineChecked.RiscV MachineChecked.RiscV.Frame MachineChecked.RiscV.Check MachineChecked.RiscV.Exec
  Cases.Zip2005.Image

variable {G : MachineState → Prop} {k : Nat} {P : Prop}

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7801beb0.base, prog := F_7801beb0.prog }

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 33) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn] at h)

/-- The bump pointer `read_vec_raw` allocates from. -/
def BUMP : Word := 0x78040618#64

/-- The three doublewords of the `{ptr, len, cap}` result. -/
def out3 (m : Word → Word) (o v0 v1 v2 : Word) : Word → Word := fun a =>
  if a = o + 16#64 then v2 else if a = o + 8#64 then v1 else if a = o then v0 else m a

/-- How `read_vec_raw` returns: callee-saved registers and code kept; with no hint (or a
    length of `u64::MAX`), a zero result and nothing consumed. -/
def Done (s0 t : MachineState) : Prop :=
  t.pc = s0.getReg .x1 &&& ~~~1#64 ∧ (∀ q ∈ savedRegs, t.getReg q = s0.getReg q) ∧
  t.code = s0.code ∧
  ((lenW s0 = -1#64 ∧ t.privateInput = s0.privateInput ∧
    t.getMem = out3 s0.getMem (s0.getReg .x10) 0 0 0) ∨
   (∃ n, frontHintLen s0 = some n ∧ BitVec.ofNat 64 n ≠ -1#64 ∧
    (s0.getMem BUMP).toNat + ((BitVec.ofNat 64 n + 7#64) &&& 0xfffffffffffffff8#64).toNat ≤ 2 ^ 37 ∧
    t.privateInput = s0.privateInput.drop (8 + n) ∧
    t.getMem = out3 (readMem (fun a => if a = BUMP then
        s0.getMem BUMP + ((BitVec.ofNat 64 n + 7#64) &&& 0xfffffffffffffff8#64) else s0.getMem a)
      (s0.getMem BUMP) s0.privateInput n) (s0.getReg .x10) (s0.getMem BUMP) (BitVec.ofNat 64 n)
      ((BitVec.ofNat 64 n + 7#64) &&& 0xfffffffffffffff8#64)))

/-- The bump region is exhausted: `read_vec_raw` calls `core::panicking::panic_fmt` (at
    `0x7803de40`) with its arguments in `a0`–`a2`, memory and input untouched. -/
def Panic (s0 t : MachineState) : Prop :=
  t.pc = 0x7803de40#64 ∧ t.code = s0.code ∧ t.getReg .x1 = 0x7801bf3c#64 ∧
  (∀ q ∈ savedRegs, t.getReg q = s0.getReg q) ∧ t.getMem = s0.getMem ∧
  t.privateInput = s0.privateInput ∧ t.getReg .x10 = 0x78001510#64 ∧ t.getReg .x11 = 0x31#64 ∧
  t.getReg .x12 = 0x78001528#64

theorem bound (p c : Word) (h1 : ¬ (p + c).ult p = true)
    (h2 : ¬ (1#64 <<< (37#6).toNat).ult (0 - 0 ||| p + c) = true) : p.toNat + c.toNat ≤ 2 ^ 37 := by
  simp [BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_add] at h1 h2
  have := p.isLt; have := c.isLt
  omega

theorem spec {s0 : MachineState} (hpc : s0.pc = 0x7801beb0#64) (hcode : s0.code = C)
    (hpanic : ∀ t, Panic s0 t → SafeN G k P t)
    (hk : ∀ t, Done s0 t → SafeN G k P t) : SafeN G k P s0 := by
  have hcode0 := hcode
  rw [← setPC_self hpc]
  iterate 3 xstep code
  refine safe_hintLen (fetchLit code (by simp [hcode]) (pc_setPC _ _) rfl (by decide)) (by xregs) ?_
  rw [hintLen_eq]
  simp only [pc_setPC, BitVec.reduceAdd, lenW_setReg, lenW_setPC]
  generalize hv : lenW s0 = v
  xstep code
  · simp only [beq_iff_eq] at hb
    iterate 4 xstep code
    refine hk _ ⟨by simp, fun q hq => ?_, by simp [hcode], .inl ⟨hv.trans hb, by simp, ?_⟩⟩
    · simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> xregs
    · funext a
      simp only [getMem_setMem, MachineState.getMem_setReg, MachineState.getMem_setPC, out3]
  · simp only [beq_iff_eq] at hb
    have hv1 := hb
    iterate 3 xstep code
    xag
    simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
    generalize hp : s0.getMem 0x78040618#64 = p
    iterate 9 xstep code
    all_goals generalize hc : (v + 7#64 &&& 18446744073709551608#64) = cap at *
    · rw [if_pos (by
        have : ∀ x : BitVec 64, (1#64 <<< (37#6).toNat).ult (0 - 1 ||| x) = true := by intro x; bv_decide
        exact this _)]
      iterate 7 xstep code
      xag
      refine hpanic _ ⟨rfl, by simp [hcode], by xregs, fun q hq => ?_, by funext a; simp, by simp,
        by xregs, by xregs, by xregs⟩
      simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> xregs
    · split
      · iterate 7 xstep code
        xag
        refine hpanic _ ⟨rfl, by simp [hcode], by xregs, fun q hq => ?_, by funext a; simp, by simp,
          by xregs, by xregs, by xregs⟩
        simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> xregs
      · rename_i hlim
        iterate 2 xstep code
        xag
        refine safe_hintRead (fetchLit code (by simp [hcode]) (pc_setPC _ _) rfl (by decide))
          (by xregs) fun y hy => ?_
        obtain ⟨n, hn, hvn⟩ : ∃ n, frontHintLen s0 = some n ∧ BitVec.ofNat 64 n = v := by
          unfold lenW at hv
          split at hv
          · exact ⟨_, ‹_›, hv⟩
          · exact absurd hv.symm hv1
        obtain ⟨ypc, ycode, yregs, yin, ymem⟩ := hintRead_eq (by simpa [frontHintLen] using hn) hy
        clear hy
        subst hc hvn hp
        have hcode : y.code = C := by rw [ycode]; simp [hcode]
        rw [← setPC_self (show y.pc = 0x7801bf00#64 by rw [ypc]; rfl)]
        iterate 4 xstep code
        simp only [yregs]
        xregs
        simp only [gm_setReg, gm_setPC, gm_setMem, MachineState.privateInput_setReg,
          MachineState.privateInput_setMem, MachineState.privateInput_setPC] at ymem yin
        simp only [getReg_setReg, MachineState.getReg_setPC, MachineChecked.RiscV.getReg_setMem,
          reduceCtorEq, ne_eq, not_false_eq_true, and_true, if_true, if_false, BitVec.zero_or] at ymem
        refine hk _ ⟨by simp, fun q hq => ?_, by simp [hcode, hcode0], .inr ⟨n, hn, hv1,
          bound _ _ hb hlim, by simp [yin], ?_⟩⟩
        · simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;> (simp only [MachineState.getReg_setPC, MachineChecked.RiscV.getReg_setMem, yregs]; xregs)
        · funext a
          simp only [gm_setMem, gm_setPC, ymem, out3, BUMP]
          rfl

end Cases.Zip2005.Runtime.ReadVec
