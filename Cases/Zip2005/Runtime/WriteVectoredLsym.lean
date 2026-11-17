/-
  Cases.Zip2005.Runtime.WriteVectoredLsym

  `write_vectored` at Lprog again, with `lsym` (`Lprog/Tactic.lean`): the same contracts as
  `WriteVectored.lean`, which steps each instruction by hand over a machine state that agrees
  with the register file. Here `lsym` steps the bodies over the register file: each operation
  computed, a load read back through the stores before it, a memory access's check closed from
  the facts given (`dwordOk`, `noCodeOk`, at the addresses as `simp` writes them), and calls
  and the `WRITE` left to the machine-level rules (`lsafe_call`, `lsafe_tail`, `lsafe_write`)
  at the state it leaves. What is left is what the functions mean: the loop's invariant, the
  frame, and the postconditions.

  The statements are those of `WriteVectored.lean`, so `WriteVectored.spec` carries either
  proof to `stepSp1`.
-/

import Cases.Zip2005.Runtime.WriteVectored
import Cases.Zip2005.Runtime.MemcmpLsym
import LprogRiscV.Lsym

namespace Cases.Zip2005.WriteVectoredLsym

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift Lprog.RiscV
  Lprog.RiscV.Machine Cases.Zip2005.Image Cases.Zip2005.WriteVectored

set_option autoImplicit false

/-- **From the return of the call to the end**: restore, close the frame, return `Ok(len)`. -/
theorem fromCall {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp : Word) (xs : List Word) {lo hi : Nat}
    (hfr : RegionOk lo hi (sp - 0x50#64) 10) (regs : Reg → BitVec 64) (m u : MachineState)
    (hag : Agree (ofParts regs m) u) (h2 : u.getReg .x2 = sp - 32#64) (h9 : u.getReg .x9 = firstLen xs)
    (hs : Saved s0 sp u) (hrv : s0.getReg .x1 = rv) (htop : sp = top)
    (hdone : ∀ r' m', Done s0 sp xs (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨0, 40, rv, top⟩ :: rest, regs, m⟩ := by
  subst htop hrv
  have r2 : regs .x2 = sp - 32#64 := h2 ▸ regs_of_agree hag (by decide)
  have r9 : regs .x9 = firstLen xs := h9 ▸ regs_of_agree hag (by decide)
  have mem : ∀ a, m.getMem a = u.getMem a := hag.mem
  have e9 : sp - 32#64 + 24#64 = sp - 0x50#64 + BitVec.ofNat 64 (8 * 9) := by bv_decide
  have e8 : sp - 32#64 + 16#64 = sp - 0x50#64 + BitVec.ofNat 64 (8 * 8) := by bv_decide
  have e7 : sp - 32#64 + 8#64 = sp - 0x50#64 + BitVec.ofNat 64 (8 * 7) := by bv_decide
  have v9 := e9 ▸ dwordOk hfr (i := 9) (by omega)
  have v8 := e8 ▸ dwordOk hfr (i := 8) (by omega)
  have v7 := e7 ▸ dwordOk hfr (i := 7) (by omega)
  have m9 : m.getMem (sp - 32#64 + 24#64) = s0.getReg .x1 := by rw [mem, e9]; exact hs.ra
  have m8 : m.getMem (sp - 32#64 + 16#64) = s0.getReg .x8 := by rw [mem, e8]; exact hs.fp
  have m7 : m.getMem (sp - 32#64 + 8#64) = s0.getReg .x9 := by rw [mem, e7]; exact hs.s1
  lsym hf0 with [r2, r9, v9, v8, v7, m9]
  apply hdone
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩
  all_goals try simp only [getReg_ofParts, getMem_ofParts]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, m8]
  · simp [lsym_simp, m7]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · have h0 : r ≠ .x0 := by revert hr; revert r; decide
    obtain ⟨h1, h2', h8, h9', h10, h11, -⟩ := kept_ne hr
    simp [lsym_simp, h0, h1, h2', h8, h9', h10, h11, regs_of_agree hag h0, hs.regs r hr]
  · rw [mem]; exact hs.unch a ha
  · exact hag.code.trans hs.code

/-- `Saved` over a register file, kept by one that agrees with it on `kept`. -/
theorem saved_ofParts {s0 m : MachineState} {sp : Word} {regs r' : Reg → BitVec 64}
    (hs : Saved s0 sp (ofParts regs m)) (h : ∀ r ∈ kept, r' r = regs r) : Saved s0 sp (ofParts r' m) :=
  hs.step (fun _ => rfl) rfl fun r hr => by simp [getReg_ofParts, h r hr]

/-- **The loop** over the slices, at its head (pc 14), with `j` slices passed. -/
theorem loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp bufs : Word) (xs : List Word) (n : Nat) {lo hi : Nat}
    (hxl : xs.length = 2 * n) (hok : RegionOk lo hi bufs (2 * n)) (hn : 16 * n < 2 ^ 64)
    (hcall : ∀ r' m', AtCall s0 sp xs (ofParts r' m') → LSafeN fs G N Q ⟨⟨0, 37, rv, top⟩ :: rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : MachineState), n - j = k → j ≤ n →
      regs .x2 = sp - 32#64 → regs .x8 = sp → regs .x11 = bufs + BitVec.ofNat 64 (16 * j) - 16#64 →
      regs .x12 = BitVec.ofNat 64 (16 * (n - j)) →
      firstLen (xs.drop (2 * j)) = firstLen xs → Region bufs xs (ofParts regs m) →
      Saved s0 sp (ofParts regs m) →
      LSafeN fs G N Q ⟨⟨0, 14, rv, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro j regs m hk hj h2 h8 h11 h12 hfl hreg hs
    obtain rfl : j = n := by omega
    -- every slice is empty: the length is zero
    lsym hf0 stop [14, 37] with [h2, h8, h11, h12]
    refine hcall _ _ ⟨?_, ?_, ?_, ?_, saved_ofParts hs fun r hr => ?_⟩
    · simp [getReg_ofParts, lsym_simp, h2]
    · simp [getReg_ofParts, lsym_simp, h8]
    · rw [← hfl, show 2 * j = xs.length by omega, List.drop_length]; simp [getReg_ofParts, lsym_simp, firstLen]
    · simp [getReg_ofParts, lsym_simp]
    · obtain ⟨-, -, -, h9, h10, h11, h12⟩ := kept_ne hr
      simp [lsym_simp, h9, h10, h11, h12]
  | succ k ih =>
    intro j regs m hk hj h2 h8 h11 h12 hfl hreg hs
    have hjn : j < n := by omega
    have vl := dwordOk hok (i := 2 * j + 1) (by omega)
    have vp := addr_ptr bufs j ▸ dwordOk hok (i := 2 * j) (by omega)
    have ml : m.getMem (bufs + BitVec.ofNat 64 (8 * (2 * j + 1))) = xs[2 * j + 1]! :=
      hreg (2 * j + 1) (by omega)
    lsym hf0 stop [14, 37] with [h2, h8, h11, h12, addr_len, addr_next, count_dec hjn, vl, vp, ml]
    · -- the count is not zero
      exact absurd (ofNat_eq_zero (by omega) hc) (by omega)
    · -- an empty slice: round again
      apply ih (j + 1) _ m (by omega) hjn
      · simp [lsym_simp, h2]
      · simp [lsym_simp, h8]
      · simp [lsym_simp]
      · simp [lsym_simp]
      · have hc' : xs[2 * j + 1]! = 0 := by simpa using hc
        rw [← hfl, firstLen_drop (j := j) (by omega), ite_eq_left hc', show 2 * (j + 1) = 2 * j + 2 by omega]
      · exact fun i hi => hreg i hi
      · refine saved_ofParts hs fun r hr => ?_
        obtain ⟨-, -, -, h9, -, h11, h12⟩ := kept_ne hr
        simp [lsym_simp, h9, h11, h12]
    · -- the first non-empty slice: to the call
      refine hcall _ _ ⟨?_, ?_, ?_, ?_, saved_ofParts hs fun r hr => ?_⟩
      · simp [getReg_ofParts, lsym_simp, h2]
      · simp [getReg_ofParts, lsym_simp, h8]
      · have hc' : ¬ xs[2 * j + 1]! = 0 := by simpa using hc
        rw [← hfl, firstLen_drop (j := j) (by omega), ite_eq_right hc']; simp [getReg_ofParts, lsym_simp]
      · simp [getReg_ofParts, lsym_simp]
      · obtain ⟨-, -, -, h9, h10, h11, h12⟩ := kept_ne hr
        simp [lsym_simp, h9, h10, h11, h12]

/-- **From the entry to the call.** -/
theorem toCall {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp bufs : Word) (xs : List Word) (n : Nat) {lo hi lo' hi' : Nat}
    (hxl : xs.length = 2 * n) (hok : RegionOk lo hi bufs (2 * n))
    (hfr : RegionOk lo' hi' (sp - 0x50#64) 10) (hcw : CodeWithin lo' hi' s0)
    (hdis : Disjoint bufs (2 * n) (sp - 0x50#64) 10)
    (regs : Reg → BitVec 64) (m : MachineState) (hag : Agree (ofParts regs m) s0)
    (h2 : s0.getReg .x2 = sp) (h11 : s0.getReg .x11 = bufs) (h12 : s0.getReg .x12 = BitVec.ofNat 64 n)
    (hreg : Region bufs xs s0)
    (hcall : ∀ r' m', AtCall s0 sp xs (ofParts r' m') → LSafeN fs G N Q ⟨⟨0, 37, rv, top⟩ :: rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨0, 0, rv, top⟩ :: rest, regs, m⟩ := by
  have hn : 16 * n < 2 ^ 64 := by have := hok.inMem; unfold SP1_MAX_MEMORY at this; omega
  have r2 : regs .x2 = sp := h2 ▸ regs_of_agree hag (by decide)
  have r11 : regs .x11 = bufs := h11 ▸ regs_of_agree hag (by decide)
  have r12 : regs .x12 = BitVec.ofNat 64 n := h12 ▸ regs_of_agree hag (by decide)
  have r1 : regs .x1 = s0.getReg .x1 := regs_of_agree hag (by decide)
  have r8 : regs .x8 = s0.getReg .x8 := regs_of_agree hag (by decide)
  have r9 : regs .x9 = s0.getReg .x9 := regs_of_agree hag (by decide)
  -- the three cells the prologue saves to, as `simp` writes their addresses
  have a9 : sp + 0xffffffffffffffe0#64 + 24#64 = sp - 0x50#64 + BitVec.ofNat 64 (8 * 9) := by bv_decide
  have a8 : sp + 0xffffffffffffffe0#64 + 16#64 = sp - 0x50#64 + BitVec.ofNat 64 (8 * 8) := by bv_decide
  have a7 : sp + 0xffffffffffffffe0#64 + 8#64 = sp - 0x50#64 + BitVec.ofNat 64 (8 * 7) := by bv_decide
  have ok : ∀ i, i < 10 → isValidDwordAccessSp1 (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) = true ∧
      noCodeAt m (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) 8 = true := fun i hi =>
    ⟨dwordOk hfr hi, by
      have := noCodeOk hfr hcw (i := i) (k := 0) (w := 8) hi (by omega) (by omega) (by omega)
      rw [← noCodeAt_ofParts regs m, show noCodeAt (ofParts regs m) = noCodeAt s0 by
        funext a w; simp only [noCodeAt, hag.code]]
      simpa using this⟩
  have v9 : isValidDwordAccessSp1 (sp + 0xffffffffffffffe0#64 + 24#64) = true ∧
      noCodeAt m (sp + 0xffffffffffffffe0#64 + 24#64) 8 = true := by rw [a9]; exact ok 9 (by omega)
  have v8 : isValidDwordAccessSp1 (sp + 0xffffffffffffffe0#64 + 16#64) = true ∧
      noCodeAt m (sp + 0xffffffffffffffe0#64 + 16#64) 8 = true := by rw [a8]; exact ok 8 (by omega)
  have v7 : isValidDwordAccessSp1 (sp + 0xffffffffffffffe0#64 + 8#64) = true ∧
      noCodeAt m (sp + 0xffffffffffffffe0#64 + 8#64) 8 = true := by rw [a7]; exact ok 7 (by omega)
  lsym hf0 stop [14] with [r2, r11, r12, r1, r8, r9, v9, v8, v7]
  -- the cells written, and every other address unchanged
  have hunch : ∀ r' : Reg → BitVec 64, Unchanged (frame sp) s0 (ofParts r' (((m.setMem (sp + 0xffffffffffffffe0#64 + 24#64) (s0.getReg .x1)).setMem
      (sp + 0xffffffffffffffe0#64 + 16#64) (s0.getReg .x8)).setMem (sp + 0xffffffffffffffe0#64 + 8#64) (s0.getReg .x9))) := by
    intro r' a ha
    have hnot := ha _ (List.mem_singleton_self _)
    have h7 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 7) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
    have h8 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 8) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
    have h9 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 9) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
    rw [a9, a8, a7]
    simp only [getMem_ofParts, getMem_setMem, h7, h8, h9, ite_false]
    exact hag.mem a
  refine loop s0 sp bufs xs n hxl hok hn hcall n 0 _ _ (by omega) (Nat.zero_le _) ?_ ?_ ?_ ?_ (by simp)
    (hreg.of_unchanged (hunch _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rwa [hxl]) ⟨?_, ?_, ?_, hunch _, ?_, fun r hr => ?_⟩
  · simp [lsym_simp]; bv_decide
  · simp [lsym_simp]; bv_decide
  · simp [lsym_simp]; bv_decide
  · simp [lsym_simp, slli4 hn]
  · rw [getMem_ofParts, ← a9]; simp
  · rw [getMem_ofParts, ← a8]; simp
  · rw [getMem_ofParts, ← a7]; simp
  · exact hag.code
  · have h0 : r ≠ .x0 := by revert hr; revert r; decide
    obtain ⟨-, h2', h8', -, -, h11', h12'⟩ := kept_ne hr
    simp [getReg_ofParts, lsym_simp, h0, h2', h8', h11', h12', regs_of_agree hag h0]

/-- **`syscall_write`'s contract at Lprog**, as `WriteVectored.scw_contract`. -/
theorem scw_contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv : Word}
    {rest : List Frame} (u : MachineState) (sp fd : Word) (regs : Reg → BitVec 64) (m : MachineState)
    (hag : Agree (ofParts regs m) u) (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi u)
    (hra : u.getReg .x1 = rv) (hsp : u.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (h10 : u.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (hpost : ∀ r' m', ScwRet u sp (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨2, 0, rv, sp⟩ :: rest, regs, m⟩ := by
  have hfr : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have r2 : regs .x2 = sp := hsp ▸ regs_of_agree hag (by decide)
  have r10 : regs .x10 = fd := h10 ▸ regs_of_agree hag (by decide)
  have ok : ∀ i, i < 6 → isValidDwordAccessSp1 (sp - 0x30#64 + BitVec.ofNat 64 (8 * i)) = true ∧
      noCodeAt m (sp - 0x30#64 + BitVec.ofNat 64 (8 * i)) 8 = true := fun i hi =>
    ⟨dwordOk hfr hi, by
      have := noCodeOk hfr hcw (i := i) (k := 0) (w := 8) hi (by omega) (by omega) (by omega)
      rw [← noCodeAt_ofParts regs m, show noCodeAt (ofParts regs m) = noCodeAt u by
        funext a w; simp only [noCodeAt, hag.code]]
      simpa using this⟩
  have vk : ∀ (a : Word) (i : Nat), i < 6 → a = sp - 0x30#64 + BitVec.ofNat 64 (8 * i) →
      isValidDwordAccessSp1 a = true ∧ noCodeAt m a 8 = true := fun a i hi h => by subst h; exact ok i hi
  have v5 := vk (sp + 0xffffffffffffffd0#64 + 40#64) 5 (by omega) (by bv_decide)
  have v4 := vk (sp + 0xffffffffffffffd0#64 + 32#64) 4 (by omega) (by bv_decide)
  have v3 := vk (sp + 0xffffffffffffffd0#64 + 24#64) 3 (by omega) (by bv_decide)
  have v2 := vk (sp + 0xffffffffffffffd0#64 + 16#64) 2 (by omega) (by bv_decide)
  have v1 := vk (sp + 0xffffffffffffffd0#64 + 8#64) 1 (by omega) (by bv_decide)
  have v0 := vk (sp + 0xffffffffffffffd0#64) 0 (by omega) (by bv_decide)
  -- the prologue, to the `WRITE`
  lsym hf2 with [r2, r10, v5, v4, v3, v2, v1, v0]
  apply lsafe_write hf2 (Agree.refl _) rfl (by simp [getReg_ofParts, lsym_simp])
    (by simp [getReg_ofParts, lsym_simp, r10, hfd])
  intro r' m' hag'
  have er : ∀ r, r ≠ .x0 → r' r = _ := fun r h => regs_of_agree hag' h
  have em : ∀ a, m'.getMem a = _ := hag'.mem
  simp only [getReg_ofParts, getMem_ofParts] at er em
  -- `fd ≠ 13`, the epilogue and the return
  have r1 : regs .x1 = rv := hra ▸ regs_of_agree hag (by decide)
  have back : sp + 0xffffffffffffffd0#64 + 48#64 = sp := by bv_decide
  lsym hf2 with [er, em, r2, r10, hfd, v5.1, v4.1, v3.1, v2.1, v1.1, v0.1, r1, back]
  apply hpost
  refine ⟨fun r hr => ?_, hag'.code.trans hag.code, fun a ha => ?_⟩
  · -- the callee-saved registers: restored, or never written
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [getReg_ofParts, lsym_simp, er, hsp, regs_of_agree hag]
  · -- memory outside the frame: the stores were all in it
    have hnot := ha _ (List.mem_singleton_self _)
    have hc : ∀ (b : Word) (i : Nat), i < 6 → b = sp - 0x30#64 + BitVec.ofNat 64 (8 * i) → a ≠ b :=
      fun b i hi hb h => hnot (h ▸ hb ▸ inRegion_cell' hfr hi)
    simp [em,
      hc (sp + 0xffffffffffffffd0#64 + 40#64) 5 (by omega) (by bv_decide),
      hc (sp + 0xffffffffffffffd0#64 + 32#64) 4 (by omega) (by bv_decide),
      hc (sp + 0xffffffffffffffd0#64 + 24#64) 3 (by omega) (by bv_decide),
      hc (sp + 0xffffffffffffffd0#64 + 16#64) 2 (by omega) (by bv_decide),
      hc (sp + 0xffffffffffffffd0#64 + 8#64) 1 (by omega) (by bv_decide),
      hc (sp + 0xffffffffffffffd0#64) 0 (by omega) (by bv_decide)]
    exact hag.mem a

/-- **`sys_write`'s contract at Lprog**: `syscall_write`'s, through the tail call. -/
theorem sw_contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv : Word}
    {rest : List Frame} (u : MachineState) (sp fd : Word) (regs : Reg → BitVec 64) (m : MachineState)
    (hag : Agree (ofParts regs m) u) (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi u)
    (hra : u.getReg .x1 = rv) (hsp : u.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (h10 : u.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (hpost : ∀ r' m', ScwRet u sp (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨1, 0, rv, sp⟩ :: rest, regs, m⟩ := by
  have r1 : regs .x1 = rv := hra ▸ regs_of_agree hag (by decide)
  have r2 : regs .x2 = sp := hsp ▸ regs_of_agree hag (by decide)
  have r10 : regs .x10 = fd := h10 ▸ regs_of_agree hag (by decide)
  lsym hf1
  apply lsafe_tail hf1 (Agree.refl _) (rs := .x6) (off := 0x40c) (cs := [2]) (by decide)
    (by simp [getReg_ofParts, lsym_simp, r2]) (g := 2) (tf := ⟨"syscall_write", F_7801b3b0.base, scwProg, 0x30⟩) rfl
    (by simp) (by simp [getReg_ofParts, lsym_simp]; decide)
  intro g' fn' hg' hb
  obtain ⟨rfl, rfl⟩ := at_scw hg' hb
  refine scw_contract (ofParts _ m) sp fd _ m (Agree.refl _) (cw_of_code hcw hag.code) ?_ ?_ hstk ?_ hfd
    fun r' m' h => hpost r' m' ⟨fun r hr => ?_, h.code.trans hag.code, fun a ha => (h.unch a ha).trans (hag.mem a)⟩
  · simp [getReg_ofParts, lsym_simp, r1]
  · simp [getReg_ofParts, lsym_simp, r2]
  · simp [getReg_ofParts, lsym_simp, r10]
  · have h0 : r ≠ .x0 := by revert hr; revert r; decide
    have h6 : r ≠ .x6 := by rintro rfl; simp [calleeSavedRegs] at hr
    rw [h.cs r hr]
    simp [getReg_ofParts, lsym_simp, h0, h6, regs_of_agree hag h0]

/-- **`write_vectored`'s contract at Lprog**, as `WriteVectored.contract`. -/
theorem contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp bufs : Word) (xs : List Word) (cnt : Nat)
    (hxl : xs.length = 2 * cnt) (hokx : RegionOk Ro.layout.textLo Ro.layout.textHi bufs (2 * cnt))
    (hstk : StackOk Ro.layout 0x50 sp) (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s0)
    (hdis : Disjoint bufs (2 * cnt) (sp - 0x50#64) 10)
    (regs : Reg → BitVec 64) (m : MachineState) (hag : Agree (ofParts regs m) s0)
    (h2 : s0.getReg .x2 = sp) (h11 : s0.getReg .x11 = bufs) (h12 : s0.getReg .x12 = BitVec.ofNat 64 cnt)
    (hreg : Region bufs xs s0) (hrv : s0.getReg .x1 = rv) (htop : sp = top)
    (hdone : ∀ r' m', Done s0 sp xs (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨0, 0, rv, top⟩ :: rest, regs, m⟩ := by
  have hfr : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hstk.frame 10 (by decide)
  refine toCall s0 sp bufs xs cnt hxl hokx hfr hcw hdis regs m hag h2 h11 h12 hreg ?_
  intro rA mA hat
  -- the call: `auipc ra`, then `jalr ra` into `sys_write`
  lsym hf0 with [hat.x2]
  apply lsafe_call hf0 (Agree.refl _) (ret := F_7803c684.base + BitVec.ofNat 64 (4 * 19) + 4) (rs := .x1)
    (off := 0x8d8) (cs := [1]) (by decide) (g := 1)
    (tf := ⟨"sys_write", F_7801bfa4.base, swProg, 0⟩) rfl (by simp) (by simp [getReg_ofParts, lsym_simp]; decide)
  intro g' fn' hg' hb rC mC hagC
  obtain ⟨rfl, rfl⟩ := at_sw hg' hb
  -- the state at `sys_write`'s entry, outside `ra`: the state at the call
  have hB : ∀ (v w p : Word) (r : Reg), r ≠ .x1 →
      (((ofParts (updReg rA .x1 v) mA).setReg .x1 w).setPC p).getReg r = (ofParts rA mA).getReg r := by
    intro v w p r h1; simp [getReg_setReg, getReg_ofParts, lsym_simp, h1]
  have hsp : ∀ v, (ofParts (updReg rA .x1 v) mA).getReg .x2 = sp - 32#64 := fun v => by
    simpa [getReg_setReg] using (hB v 0 0 .x2 (by decide)).trans hat.x2
  rw [hsp]
  refine sw_contract (rv := F_7803c684.base + BitVec.ofNat 64 (4 * 19) + 4) _ (sp - 32#64) 2#64 rC mC hagC
    (cw_of_code hcw hat.saved.code) (by simp [getReg_setReg]) ((hB _ _ _ _ (by decide)).trans hat.x2)
    (stack_sub hstk) ((hB _ _ _ _ (by decide)).trans hat.x10) (by decide) ?_
  intro rD mD hret
  -- back from the call
  have hs : Saved s0 sp (ofParts rD mD) :=
    saved_after_call hfr hat.saved (fun r hr => hB _ _ _ r hr) (fun a => by simp) rfl hret
  exact fromCall s0 sp xs hfr rD mD (ofParts rD mD) (Agree.refl _)
    ((hret.cs .x2 (by decide)).trans ((hB _ _ _ _ (by decide)).trans hat.x2))
    ((hret.cs .x9 (by decide)).trans ((hB _ _ _ _ (by decide)).trans hat.x9)) hs hrv htop hdone

end Cases.Zip2005.WriteVectoredLsym
