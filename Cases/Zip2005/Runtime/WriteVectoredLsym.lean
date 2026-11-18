/-
  Cases.Zip2005.Runtime.WriteVectoredLsym

  `write_vectored` at Lprog again, with `lsym` (`Lprog/Tactic.lean`): the same contract as
  `WriteVectored.lean`, which steps each instruction by hand. The callees are stated as
  contracts over the register file (`Isa.Contract`): `syscall_write`'s is proved over a
  machine state and turned into one (`contract_of_agree`), `sys_write`'s is proved by `lsym`
  with its tail call stepped through `syscall_write`'s (`sw_spec`), and `write_vectored`'s call
  is stepped through `sys_write`'s. No call is stepped by a rule by hand; the system call is
  (`lsafe_write`).

  Addresses are in one normal form, a base plus a constant (`lsym_addr`): a fact about a cell
  of a region, normalised by `simp only [lsym_addr]`, is about the address `lsym` computes, so
  no proof bridges two spellings of an address. What is left is what the functions mean: the
  loop's invariant, the frame, and the postconditions.

  The statement of `contract` is `WriteVectored.contract`'s, so `WriteVectored.spec` carries
  either proof to `stepSp1`.
-/

import Cases.Zip2005.Runtime.WriteVectored
import Cases.Zip2005.Runtime.MemcmpLsym
import LprogRiscV.Lsym

namespace Cases.Zip2005.WriteVectoredLsym

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift Lprog.RiscV
  Lprog.RiscV.Machine Cases.Zip2005.Image Cases.Zip2005.WriteVectored

set_option autoImplicit false

/-- **`syscall_write`, to a descriptor other than 13, by `lsym`**, stated over a machine state
    as `WriteVectored.scw_contract` is. -/
theorem scw_lsym {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv : Word}
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
  have v5 := ok 5 (by omega); have v4 := ok 4 (by omega); have v3 := ok 3 (by omega)
  have v2 := ok 2 (by omega); have v1 := ok 1 (by omega); have v0 := ok 0 (by omega)
  simp only [lsym_addr] at v5 v4 v3 v2 v1 v0
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
  lsym hf2 with [er, em, r2, r10, hfd, v5.1, v4.1, v3.1, v2.1, v1.1, v0.1, r1]
  apply hpost
  refine ⟨fun r hr => ?_, hag'.code.trans hag.code, fun a ha => ?_⟩
  · -- the callee-saved registers: restored, or never written
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [getReg_ofParts, lsym_simp, er, hsp, regs_of_agree hag]
  · -- memory outside the frame: the stores were all in it
    have hnot := ha _ (List.mem_singleton_self _)
    have hc : ∀ i, i < 6 → a ≠ sp - 0x30#64 + BitVec.ofNat 64 (8 * i) :=
      fun i hi h => hnot (h ▸ inRegion_cell' hfr hi)
    have c5 := hc 5 (by omega); have c4 := hc 4 (by omega); have c3 := hc 3 (by omega)
    have c2 := hc 2 (by omega); have c1 := hc 1 (by omega); have c0 := hc 0 (by omega)
    simp only [lsym_addr] at c5 c4 c3 c2 c1 c0
    simp [em, c5, c4, c3, c2, c1, c0]
    exact hag.mem a

/-- What `syscall_write` needs at its entry `u`. -/
def ScwPre (ret top : Word) (u : MachineState) : Prop :=
  CodeWithin Ro.layout.textLo Ro.layout.textHi u ∧ u.getReg .x1 = ret ∧ u.getReg .x2 = top ∧
    StackOk Ro.layout 0x30 top ∧ u.getReg .x10 ≠ 13#64

/-- **`syscall_write`'s contract over the register file**: `scw_lsym`, proved over a machine
    state, as it is (`contract_of_agree`). -/
theorem scw_spec : rvIsa.Contract (liftProg fs) sp1Ctx 2
    (fun ret top regs m => ScwPre ret top (ofParts regs m))
    (fun _ top regs m r' m' => ScwRet (ofParts regs m) top (ofParts r' m')) :=
  contract_of_agree (Pre := ScwPre) (Post := fun _ top u v => ScwRet u top v)
    fun _ _ _ _ top _ u regs m hag ⟨hcw, hra, hsp, hstk, h10⟩ hk =>
      scw_lsym u top _ regs m hag hcw hra hsp hstk rfl h10 hk

/-- **`sys_write`'s contract over the register file**, through `syscall_write`'s, by `lsym`:
    the tail call is stepped through `scw_spec`. -/
theorem sw_spec : rvIsa.Contract (liftProg fs) sp1Ctx 1
    (fun ret top regs m => ScwPre ret top (ofParts regs m))
    (fun _ top regs m r' m' => ScwRet (ofParts regs m) top (ofParts r' m')) := by
  intro G N Q ret top rest regs m ⟨hcw, hra, hsp, hstk, h10⟩ hk
  simp only [getReg_ofParts, reduceCtorEq, ite_false, codeWithin_ofParts] at hra hsp h10 hcw
  lsym hf1 with [ScwPre, hra, hsp, h10, hstk, hcw] using [scw_spec]
  -- `syscall_write` returns to `sys_write`'s caller; `x6`, which `sys_write` wrote, is no
  -- callee-saved register
  apply hk
  refine ⟨fun r hr => (hret.cs r hr).trans ?_, hret.code, hret.unch⟩
  have h6 : r ≠ .x6 := by rintro rfl; simp [calleeSavedRegs] at hr
  simp [getReg_ofParts, lsym_simp, h6]

/-! ## `write_vectored` -/

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
  -- the saved cells, at the addresses `lsym` computes (`lsym_addr`)
  have v9 := dwordOk hfr (i := 9) (by omega); have v8 := dwordOk hfr (i := 8) (by omega)
  have v7 := dwordOk hfr (i := 7) (by omega)
  have m9 := hs.ra; have m8 := hs.fp; have m7 := hs.s1
  simp only [lsym_addr, ← mem] at v9 v8 v7 m9 m8 m7
  lsym hf0 with [r2, r9, v9, v8, v7, m9]
  apply hdone
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, m8]
  · simp [lsym_simp, m7]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · have h0 : r ≠ .x0 := by revert hr; revert r; decide
    obtain ⟨h1, h2', h8, h9', h10, h11, -⟩ := kept_ne hr
    simp [lsym_simp, h0, h1, h2', h8, h9', h10, h11, regs_of_agree hag h0, hs.regs r hr]
  · simp only [getMem_ofParts, mem]; exact hs.unch a ha
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
    -- slice `j`'s pointer and length, at the addresses `lsym` computes (`lsym_addr`)
    have vl := dwordOk hok (i := 2 * j + 1) (by omega); have vp := dwordOk hok (i := 2 * j) (by omega)
    have ml := hreg (2 * j + 1) (by omega)
    simp only [lsym_addr, getMem_ofParts] at vl vp ml
    lsym hf0 stop [14, 37] with [h2, h8, h11, h12, count_dec hjn, vl, vp, ml]
    · -- the count is not zero
      exact absurd (ofNat_eq_zero (by omega) hc) (by omega)
    · -- an empty slice: round again
      apply ih (j + 1) _ m (by omega) hjn
      · simp [lsym_simp, h2]
      · simp [lsym_simp, h8]
      · simp [lsym_simp, lsym_addr]
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

/-- The prologue's three stores are in the frame: every address outside it is unchanged. -/
theorem unch_prologue {s0 m : MachineState} {sp : Word} {lo hi : Nat} {regs : Reg → BitVec 64}
    (hfr : RegionOk lo hi (sp - 0x50#64) 10) (hmem : ∀ a, (ofParts regs m).getMem a = s0.getMem a)
    (v9 v8 v7 : Word) (r' : Reg → BitVec 64) :
    Unchanged (frame sp) s0 (ofParts r' (((m.setMem (sp + 0xfffffffffffffff8#64) v9).setMem
      (sp + 0xfffffffffffffff0#64) v8).setMem (sp + 0xffffffffffffffe8#64) v7)) := by
  intro a ha
  have hnot := ha _ (List.mem_singleton_self _)
  have h7 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 7) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
  have h8 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 8) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
  have h9 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 9) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
  simp only [lsym_addr] at h7 h8 h9
  simp [h7, h8, h9]
  exact hmem a

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
  have ok : ∀ i, i < 10 → isValidDwordAccessSp1 (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) = true ∧
      noCodeAt m (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) 8 = true := fun i hi =>
    ⟨dwordOk hfr hi, by
      have := noCodeOk hfr hcw (i := i) (k := 0) (w := 8) hi (by omega) (by omega) (by omega)
      rw [← noCodeAt_ofParts regs m, show noCodeAt (ofParts regs m) = noCodeAt s0 by
        funext a w; simp only [noCodeAt, hag.code]]
      simpa using this⟩
  -- the three cells the prologue saves to, at the addresses `lsym` computes (`lsym_addr`)
  have v9 := ok 9 (by omega); have v8 := ok 8 (by omega); have v7 := ok 7 (by omega)
  simp only [lsym_addr] at v9 v8 v7
  lsym hf0 stop [14] with [r2, r11, r12, r1, r8, r9, v9, v8, v7]
  have hu := unch_prologue hfr hag.mem (s0.getReg .x1) (s0.getReg .x8) (s0.getReg .x9)
  refine loop s0 sp bufs xs n hxl hok hn hcall n 0 _ _ (by omega) (Nat.zero_le _) ?_ ?_ ?_ ?_ (by simp)
    (hreg.of_unchanged (hu _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rwa [hxl]) ⟨?_, ?_, ?_, hu _, ?_, fun r hr => ?_⟩
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, lsym_addr]
  · simp [lsym_simp, lsym_addr]
  · simp [lsym_simp, lsym_addr]
  · exact hag.code
  · have h0 : r ≠ .x0 := by revert hr; revert r; decide
    obtain ⟨-, h2', h8', -, -, h11', h12'⟩ := kept_ne hr
    simp [lsym_simp, h0, h2', h8', h11', h12', regs_of_agree hag h0]

theorem scwRet_top {u v : MachineState} {a b : Word} (h : ScwRet u a v) (e : a = b) : ScwRet u b v :=
  e ▸ h

/-- **`write_vectored`'s contract at Lprog**, as `WriteVectored.contract`; the call of
    `sys_write` is stepped through its contract (`sw_spec`). -/
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
  -- the call: `auipc ra`, then `jalr ra`, through `sys_write`'s contract
  have a2 := hat.x2; have a10 := hat.x10
  have hcwA : CodeWithin Ro.layout.textLo Ro.layout.textHi mA := cw_of_code hcw hat.saved.code
  have hstkA := stack_sub hstk
  simp only [getReg_ofParts, reduceCtorEq, ite_false, lsym_addr] at a2 a10 hstkA
  lsym hf0 stop [40] with [ScwPre, a2, a10, hcwA, hstkA] using [sw_spec]
  -- back from the call
  have a9 := hat.x9
  simp only [getReg_ofParts, reduceCtorEq, ite_false] at a9
  exact fromCall s0 sp xs hfr r' m' (ofParts r' m') (Agree.refl _)
    ((hret.cs .x2 (by decide)).trans (by simp [lsym_simp, a2]))
    ((hret.cs .x9 (by decide)).trans (by simp [lsym_simp, a9]))
    (saved_after_call (uB := ofParts (updReg (updReg rA .x1 _) rvIsa.link _) mA) hfr hat.saved
      (fun r hr => by simp [lsym_simp, hr]) (fun _ => rfl) rfl (scwRet_top hret (by simp [lsym_simp])))
    hrv htop hdone

end Cases.Zip2005.WriteVectoredLsym
