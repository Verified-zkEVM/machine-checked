/-
  Examples.Sp1Runtime.RiscV.WriteVectored

  `write_vectored` of an SP1 guest's standard error, with `lsym`: its contract at Lprog, and
  the same statement over riscv-zkvm's machine (`spec`), through `SafeN.of_contract`. The code
  is rustc's, in `Examples/elf/k_u128.elf`: `write_vectored` (`F104`) finds the first slice that is not
  empty and calls `sys_write` (`F24`), which tail-calls `syscall_write` (`F11`), which makes
  the system call.

  The callees are stated as contracts over the register file (`Isa.Contract`):
  `syscall_write`'s is proved over a machine state and turned into one (`contract_of_agree`),
  `sys_write`'s is proved by `lsym` with its tail call stepped through `syscall_write`'s
  (`sw_spec`), and `write_vectored`'s call is stepped through `sys_write`'s. No call is stepped
  by a rule by hand; the system call is (`lsafe_write`).

  Addresses are in one normal form, a base plus a constant (`lsym_addr`): a fact about a cell
  of a region, normalised by `simp only [lsym_addr]`, is about the address `lsym` computes, so
  no proof bridges two spellings of an address. What is left is what the functions mean: the
  loop's invariant, the frame, and the postconditions.

  The statements are over any layout `L` of the image: the window its code lies in, and the
  top of its stack.
-/

import Examples.Sp1Runtime.RiscV.Image.F11
import Examples.Sp1Runtime.RiscV.Image.F24
import Examples.Sp1Runtime.RiscV.Image.F104
import MachineChecked.RiscV.Lift.Rules
import MachineChecked.RiscV.Sym
import MachineChecked.RiscV.Sym.Write
import LprogRiscV.Lsym

namespace Examples.Sp1Runtime.RiscV.WriteVectored

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift Lprog.RiscV
  Lprog.RiscV.Machine Examples.Sp1Runtime.RiscV.Image

variable {L : Layout}

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by
  have h : ∀ w ∈ words, w.2.1 % 4 = 0 := by decide +kernel
  intro f hf
  obtain ⟨⟨name, base, ws⟩, hw, rfl⟩ := List.mem_map.mp hf
  have hb : base % 4 = 0 := h _ hw
  simp only [BitVec.toNat_ofNat]; omega

/-- The length of the first non-empty slice of a list of `IoSlice`s (pointer, length), or `0`. -/
def firstLen : List Word → Word
  | _ :: l :: rest => if l = 0 then firstLen rest else l
  | _ => 0

/-- The callee-saved registers `write_vectored` does not touch. -/
def kept : List Reg := [.x3, .x4, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The frame below `sp` (ten doublewords: the function's four and `sys_write`'s six). -/
abbrev frame (sp : Word) : List (Word × Nat) := [(sp - 0x50#64, 10)]

/-- What a machine state `u` keeps of the entry state `s0` while `write_vectored` runs: `ra`,
    `s0` and `s1` saved in the frame, memory outside the frame and the code unchanged, and the
    callee-saved registers it does not touch. -/
structure Saved (s0 : MachineState) (sp : Word) (u : MachineState) : Prop where
  ra : u.getMem (sp - 0x50#64 + BitVec.ofNat 64 (8 * 9)) = s0.getReg .x1
  fp : u.getMem (sp - 0x50#64 + BitVec.ofNat 64 (8 * 8)) = s0.getReg .x8
  s1 : u.getMem (sp - 0x50#64 + BitVec.ofNat 64 (8 * 7)) = s0.getReg .x9
  unch : Unchanged (frame sp) s0 u
  code : u.code = s0.code
  regs : ∀ r ∈ kept, u.getReg r = s0.getReg r

theorem Saved.of_agree {s0 u v : MachineState} {sp : Word} (hag : Agree v u) (h : Saved s0 sp u) :
    Saved s0 sp v :=
  ⟨(hag.mem _).trans h.ra, (hag.mem _).trans h.fp, (hag.mem _).trans h.s1,
    fun a ha => (hag.mem a).trans (h.unch a ha), hag.code.trans h.code,
    fun r hr => (hag.regs r).trans (h.regs r hr)⟩

/-- An instruction that writes only a register outside `kept` keeps `Saved`. -/
theorem Saved.step {s0 u u' : MachineState} {sp : Word} (h : Saved s0 sp u)
    (hm : ∀ a, u'.getMem a = u.getMem a) (hc : u'.code = u.code)
    (hr : ∀ r ∈ kept, u'.getReg r = u.getReg r) : Saved s0 sp u' :=
  ⟨(hm _).trans h.ra, (hm _).trans h.fp, (hm _).trans h.s1, fun a ha => (hm a).trans (h.unch a ha),
    hc.trans h.code, fun r hr' => (hr r hr').trans (h.regs r hr')⟩

/-- The state at the call: `sys_write`'s arguments set, `s1` holding the length. -/
structure AtCall (s0 : MachineState) (sp : Word) (xs : List Word) (u : MachineState) : Prop where
  x2 : u.getReg .x2 = sp - 32#64
  x8 : u.getReg .x8 = sp
  x9 : u.getReg .x9 = firstLen xs
  x10 : u.getReg .x10 = 2#64
  saved : Saved s0 sp u

theorem AtCall.of_agree {s0 u v : MachineState} {sp : Word} {xs : List Word} (hag : Agree v u)
    (h : AtCall s0 sp xs u) : AtCall s0 sp xs v :=
  ⟨(hag.regs _).trans h.x2, (hag.regs _).trans h.x8, (hag.regs _).trans h.x9,
    (hag.regs _).trans h.x10, h.saved.of_agree hag⟩

theorem firstLen_drop {xs : List Word} {j : Nat} (h : 2 * j + 2 ≤ xs.length) :
    firstLen (xs.drop (2 * j)) =
      if xs[2 * j + 1]! = 0 then firstLen (xs.drop (2 * j + 2)) else xs[2 * j + 1]! := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    getElem!_pos xs (2 * j + 1) (by omega)]
  simp only [firstLen]

theorem count_dec {n j : Nat} (h : j < n) :
    BitVec.ofNat 64 (16 * (n - j)) + 0xfffffffffffffff0#64 = BitVec.ofNat 64 (16 * (n - (j + 1))) := by
  have e : (0xfffffffffffffff0#64 : Word) = -16#64 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, show 16 * (n - j) = 16 * (n - (j + 1)) + 16 by omega,
    BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_eq_zero {x : Nat} (hx : x < 2 ^ 64) (h : BitVec.ofNat 64 x = 0#64) : x = 0 := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this

theorem kept_ne {r : Reg} (hr : r ∈ kept) :
    r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 := by
  simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem cw_of_code {lo hi : Nat} {u v : MachineState} (h : CodeWithin lo hi u) (hc : v.code = u.code) :
    CodeWithin lo hi v := fun a ha => h a (by rwa [hc] at ha)

theorem a9 (sp : Word) : sp + signExtend12 4064#12 + signExtend12 24#12 = sp - 80#64 + 72#64 := by
  simp only [signExtend12]; bv_decide
theorem inRegion_cell {lo hi : Nat} {b : Word} (h : RegionOk lo hi b 10) {i : Nat} (hi : i < 10) :
    InRegion (b + BitVec.ofNat 64 (8 * i)) b 10 := by
  have := toNat_cell h (i := i) (k := 0) hi (by omega)
  simp only [Nat.add_zero] at this
  unfold InRegion; omega

/-- The end of a run of `write_vectored` from `s0`, as an Lprog state. -/
structure Done (s0 : MachineState) (sp : Word) (xs : List Word) (u : MachineState) : Prop where
  x1 : u.getReg .x1 = s0.getReg .x1
  x2 : u.getReg .x2 = sp
  x8 : u.getReg .x8 = s0.getReg .x8
  x9 : u.getReg .x9 = s0.getReg .x9
  x10 : u.getReg .x10 = 0#64
  x11 : u.getReg .x11 = firstLen xs
  regs : ∀ r ∈ kept, u.getReg r = s0.getReg r
  unch : Unchanged (frame sp) s0 u
  code : u.code = s0.code

theorem agree_symm {t u : MachineState} (h : Agree t u) : Agree u t :=
  ⟨fun r => (h.regs r).symm, fun a => (h.mem a).symm, h.code.symm, h.committed.symm,
    h.publicValues.symm, h.privateInput.symm, h.inputBufBase.symm⟩

theorem Done.of_agree {s0 u v : MachineState} {sp : Word} {xs : List Word} (hag : Agree v u)
    (h : Done s0 sp xs u) : Done s0 sp xs v :=
  ⟨(hag.regs _).trans h.x1, (hag.regs _).trans h.x2, (hag.regs _).trans h.x8,
    (hag.regs _).trans h.x9, (hag.regs _).trans h.x10, (hag.regs _).trans h.x11,
    fun r hr => (hag.regs r).trans (h.regs r hr), fun a ha => (hag.mem a).trans (h.unch a ha),
    hag.code.trans h.code⟩

theorem stack_sub {sp : Word} (h : StackOk L 0x50 sp) : StackOk L 0x30 (sp - 32#64) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (sp - 32#64).toNat = sp.toNat - 32 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e]; omega⟩

theorem callee_frame (sp : Word) : sp - 32#64 - 0x30#64 = sp - 0x50#64 := by bv_decide

/-- A cell of the function's own part of the frame lies outside `sys_write`'s. -/
theorem own_out {lo hi : Nat} {sp : Word} (h : RegionOk lo hi (sp - 0x50#64) 10) {i : Nat} (hi6 : 6 ≤ i)
    (hi : i < 10) : ¬ InRegion (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) (sp - 0x50#64) 6 := by
  have := toNat_cell h (i := i) (k := 0) hi (by omega)
  simp only [Nat.add_zero] at this
  unfold InRegion; omega

theorem out_of_out {a b : Word} (h : ¬ InRegion a b 10) : ¬ InRegion a b 6 := by
  unfold InRegion at *; omega

/-- What `syscall_write` keeps of the state `u` at its call, in a state `v` it returns in. -/
structure ScwRet (u : MachineState) (sp : Word) (v : MachineState) : Prop where
  cs : CalleeSaved u v
  code : v.code = u.code
  unch : Unchanged [(sp - 0x30#64, 6)] u v

theorem inRegion_cell' {lo hi : Nat} {b : Word} {n : Nat} (h : RegionOk lo hi b n) {i : Nat} (hi : i < n) :
    InRegion (b + BitVec.ofNat 64 (8 * i)) b n := by
  have := toNat_cell h (i := i) (k := 0) hi (by omega)
  simp only [Nat.add_zero] at this
  unfold InRegion; omega

/-- What `write_vectored` keeps of the entry state through the call of `sys_write`. -/
theorem saved_after_call {s0 uA uB : MachineState} {sp : Word} {lo hi : Nat}
    (hfr : RegionOk lo hi (sp - 0x50#64) 10) (hsA : Saved s0 sp uA)
    (hBA : ∀ r, r ≠ .x1 → uB.getReg r = uA.getReg r) (hBm : ∀ a, uB.getMem a = uA.getMem a)
    (hBc : uB.code = uA.code) {v : MachineState} (hret : ScwRet uB (sp - 32#64) v) :
    Saved s0 sp v := by
  have hu := hret.unch
  rw [callee_frame] at hu
  have hm : ∀ i, 6 ≤ i → i < 10 → v.getMem (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) =
      uA.getMem (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) := fun i h6 h10 => by
    rw [hu _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact own_out hfr h6 h10),
      hBm]
  refine ⟨(hm 9 (by omega) (by omega)).trans hsA.ra, (hm 8 (by omega) (by omega)).trans hsA.fp,
    (hm 7 (by omega) (by omega)).trans hsA.s1, fun a ha => ?_, hret.code.trans (hBc.trans hsA.code),
    fun r hr => ?_⟩
  · have hnot := ha _ (List.mem_singleton_self _)
    rw [hu _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact out_of_out hnot), hBm]
    exact hsA.unch a ha
  · rw [hret.cs r (by revert hr; revert r; decide), hBA r (by revert hr; revert r; decide)]
    exact hsA.regs r hr

set_option autoImplicit false

/-- **`syscall_write`, to a descriptor other than 13, by `lsym`**, stated over a machine state
    not over a register file. -/
theorem scw_lsym {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv : Word}
    {rest : List Frame} (u : MachineState) (sp fd : Word) (regs : Reg → BitVec 64) (m : MachineState)
    (hag : Agree (ofParts regs m) u) (hcw : CodeWithin L.textLo L.textHi u)
    (hra : u.getReg .x1 = rv) (hsp : u.getReg .x2 = sp) (hstk : StackOk L 0x30 sp)
    (h10 : u.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (hpost : ∀ r' m', ScwRet u sp (ofParts r' m') → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨11, 0, rv, sp⟩ :: rest, regs, m⟩ := by
  have hfr : RegionOk L.textLo L.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
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
  lsym f11_eq with [r2, r10, v5, v4, v3, v2, v1, v0]
  apply lsafe_write f11_eq (Agree.refl _) rfl (by simp [getReg_ofParts, lsym_simp])
    (by simp [getReg_ofParts, lsym_simp, r10, hfd])
  intro r' m' hag'
  have er : ∀ r, r ≠ .x0 → r' r = _ := fun r h => regs_of_agree hag' h
  have em : ∀ a, m'.getMem a = _ := hag'.mem
  simp only [getReg_ofParts, getMem_ofParts] at er em
  -- `fd ≠ 13`, the epilogue and the return
  have r1 : regs .x1 = rv := hra ▸ regs_of_agree hag (by decide)
  lsym f11_eq with [er, em, r2, r10, hfd, v5.1, v4.1, v3.1, v2.1, v1.1, v0.1, r1]
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
def ScwPre (L : Layout) (ret top : Word) (u : MachineState) : Prop :=
  CodeWithin L.textLo L.textHi u ∧ u.getReg .x1 = ret ∧ u.getReg .x2 = top ∧
    StackOk L 0x30 top ∧ u.getReg .x10 ≠ 13#64

/-- **`syscall_write`'s contract over the register file**: `scw_lsym`, proved over a machine
    state, as it is (`contract_of_agree`). -/
theorem scw_spec : rvIsa.Contract (liftProg fns) sp1Ctx 11
    (fun ret top regs m => ScwPre L ret top (ofParts regs m))
    (fun _ top regs m r' m' => ScwRet (ofParts regs m) top (ofParts r' m')) :=
  contract_of_agree (Pre := ScwPre L) (Post := fun _ top u v => ScwRet u top v)
    fun _ _ _ _ top _ u regs m hag ⟨hcw, hra, hsp, hstk, h10⟩ hk =>
      scw_lsym u top _ regs m hag hcw hra hsp hstk rfl h10 hk

/-- **`sys_write`'s contract over the register file**, through `syscall_write`'s, by `lsym`:
    the tail call is stepped through `scw_spec`. -/
theorem sw_spec : rvIsa.Contract (liftProg fns) sp1Ctx 24
    (fun ret top regs m => ScwPre L ret top (ofParts regs m))
    (fun _ top regs m r' m' => ScwRet (ofParts regs m) top (ofParts r' m')) := by
  intro G N Q ret top rest regs m ⟨hcw, hra, hsp, hstk, h10⟩ hk
  simp only [getReg_ofParts, reduceCtorEq, ite_false, codeWithin_ofParts] at hra hsp h10 hcw
  lsym f24_eq with [ScwPre, hra, hsp, h10, hstk, hcw] using [scw_spec (L := L)]
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
    (hdone : ∀ r' m', Done s0 sp xs (ofParts r' m') → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨104, 40, rv, top⟩ :: rest, regs, m⟩ := by
  subst htop hrv
  have r2 : regs .x2 = sp - 32#64 := h2 ▸ regs_of_agree hag (by decide)
  have r9 : regs .x9 = firstLen xs := h9 ▸ regs_of_agree hag (by decide)
  have mem : ∀ a, m.getMem a = u.getMem a := hag.mem
  -- the saved cells, at the addresses `lsym` computes (`lsym_addr`)
  have v9 := dwordOk hfr (i := 9) (by omega); have v8 := dwordOk hfr (i := 8) (by omega)
  have v7 := dwordOk hfr (i := 7) (by omega)
  have m9 := hs.ra; have m8 := hs.fp; have m7 := hs.s1
  simp only [lsym_addr, ← mem] at v9 v8 v7 m9 m8 m7
  lsym f104_eq with [r2, r9, v9, v8, v7, m9]
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
    (hcall : ∀ r' m', AtCall s0 sp xs (ofParts r' m') → LSafeN fns G N Q ⟨⟨104, 37, rv, top⟩ :: rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : MachineState), n - j = k → j ≤ n →
      regs .x2 = sp - 32#64 → regs .x8 = sp → regs .x11 = bufs + BitVec.ofNat 64 (16 * j) - 16#64 →
      regs .x12 = BitVec.ofNat 64 (16 * (n - j)) →
      firstLen (xs.drop (2 * j)) = firstLen xs → Region bufs xs (ofParts regs m) →
      Saved s0 sp (ofParts regs m) →
      LSafeN fns G N Q ⟨⟨104, 14, rv, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro j regs m hk hj h2 h8 h11 h12 hfl hreg hs
    obtain rfl : j = n := by omega
    -- every slice is empty: the length is zero
    lsym f104_eq stop [14, 37] with [h2, h8, h11, h12]
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
    lsym f104_eq stop [14, 37] with [h2, h8, h11, h12, count_dec hjn, vl, vp, ml]
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
    (hcall : ∀ r' m', AtCall s0 sp xs (ofParts r' m') → LSafeN fns G N Q ⟨⟨104, 37, rv, top⟩ :: rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨104, 0, rv, top⟩ :: rest, regs, m⟩ := by
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
  lsym f104_eq stop [14] with [r2, r11, r12, r1, r8, r9, v9, v8, v7]
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

/-- **`write_vectored`'s contract at Lprog**; the call of
    `sys_write` is stepped through its contract (`sw_spec`). -/
theorem contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp bufs : Word) (xs : List Word) (cnt : Nat)
    (hxl : xs.length = 2 * cnt) (hokx : RegionOk L.textLo L.textHi bufs (2 * cnt))
    (hstk : StackOk L 0x50 sp) (hcw : CodeWithin L.textLo L.textHi s0)
    (hdis : Disjoint bufs (2 * cnt) (sp - 0x50#64) 10)
    (regs : Reg → BitVec 64) (m : MachineState) (hag : Agree (ofParts regs m) s0)
    (h2 : s0.getReg .x2 = sp) (h11 : s0.getReg .x11 = bufs) (h12 : s0.getReg .x12 = BitVec.ofNat 64 cnt)
    (hreg : Region bufs xs s0) (hrv : s0.getReg .x1 = rv) (htop : sp = top)
    (hdone : ∀ r' m', Done s0 sp xs (ofParts r' m') → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨104, 0, rv, top⟩ :: rest, regs, m⟩ := by
  have hfr : RegionOk L.textLo L.textHi (sp - 0x50#64) 10 := hstk.frame 10 (by decide)
  refine toCall s0 sp bufs xs cnt hxl hokx hfr hcw hdis regs m hag h2 h11 h12 hreg ?_
  intro rA mA hat
  -- the call: `auipc ra`, then `jalr ra`, through `sys_write`'s contract
  have a2 := hat.x2; have a10 := hat.x10
  have hcwA : CodeWithin L.textLo L.textHi mA := cw_of_code hcw hat.saved.code
  have hstkA := stack_sub hstk
  simp only [getReg_ofParts, reduceCtorEq, ite_false, lsym_addr] at a2 a10 hstkA
  lsym f104_eq stop [40] with [ScwPre, a2, a10, hcwA, hstkA] using [sw_spec (L := L)]
  -- back from the call
  have a9 := hat.x9
  simp only [getReg_ofParts, reduceCtorEq, ite_false] at a9
  exact fromCall s0 sp xs hfr r' m' (ofParts r' m') (Agree.refl _)
    ((hret.cs .x2 (by decide)).trans (by simp [lsym_simp, a2]))
    ((hret.cs .x9 (by decide)).trans (by simp [lsym_simp, a9]))
    (saved_after_call (uB := ofParts (updReg (updReg rA .x1 _) rvIsa.link _) mA) hfr hat.saved
      (fun r hr => by simp [lsym_simp, hr]) (fun _ => rfl) rfl (scwRet_top hret (by simp [lsym_simp])))
    hrv htop hdone

/-- **`write_vectored(self, bufs)` over `stepSp1`**: it writes the first non-empty slice to
    stderr and returns `Ok(len)`, `0` in `x10` and that slice's length in `x11` (`0` if every
    slice is empty), with the callee-saved registers restored, the code untouched and memory
    changed only in the frame below `sp`. -/
theorem spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp bufs : Word)
    (xs : List Word) (cnt : Nat)
    (hpc : s.pc = 0x7800c060#64) (hcode : ∀ f ∈ fns, CodeAt f.base (f.prog.map some) s)
    (hcw : CodeWithin L.textLo L.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk L 0x50 sp)
    (hb : s.getReg .x11 = bufs) (hc : s.getReg .x12 = BitVec.ofNat 64 cnt)
    (hx : Region bufs xs s) (hxl : xs.length = 2 * cnt)
    (hokx : RegionOk L.textLo L.textHi bufs (2 * cnt))
    (hdis : Disjoint bufs (2 * cnt) (sp - 0x50#64) 10)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged (frame sp) s t →
      t.getReg .x10 = 0#64 → t.getReg .x11 = firstLen xs → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨fn, hg, hb'⟩ : ∃ fn, fns[104]? = some fn ∧ fn.base = 0x7800c060#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_contract hok (g := 104) hg (hpc.trans hb'.symm) hcode (Post := Done s sp xs)
    (fun _ _ hpost => contract s sp bufs xs cnt hxl hokx hstk hcw hdis _ _ (agree_ofParts_regsOf s)
      hsp hb hc hx rfl hsp.symm hpost) ?_
  intro t r' m' hag hpc' hdV
  have hd := Done.of_agree (agree_symm hag) hdV
  apply hk
  · rw [hpc', hra, hra1]
  · intro r hr
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hd.x2.trans hsp.symm
    · exact hd.regs _ (by decide)
    · exact hd.regs _ (by decide)
    · exact hd.x8
    · exact hd.x9
    all_goals exact hd.regs _ (by decide)
  · exact hd.code
  · exact hd.unch
  · exact hd.x10
  · exact hd.x11

end Examples.Sp1Runtime.RiscV.WriteVectored
