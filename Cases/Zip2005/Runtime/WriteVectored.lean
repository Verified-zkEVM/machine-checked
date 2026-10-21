/-
  Cases.Zip2005.Runtime.WriteVectored

  `<Stderr as io::Write>::write_vectored(self, bufs)`, proved at Lprog: a function with a loop
  and a call.

  It saves `ra`, `s0` and `s1`, walks the `IoSlice`s at `bufs` (pairs of a pointer and a
  length) to the first that is not empty, and calls `sys_write(2, ptr, len)` on it (on
  nothing if all are empty). It returns `Ok(len)`: `0` in `x10` and `len` in `x11`.

  The run is proved at Lprog in two pieces, each through `Reaches`: from the entry to the call
  (`toCall`, with the loop `loop`), and from the return to the end (`fromCall`). The call
  itself is taken over the machine with `sys_write_spec` from the table, and `sim_return`
  resumes at Lprog after it. `spec` puts the three together.
-/

import MachineChecked.Lprog.Lift
import Cases.Zip2005.Runtime.Trivial
import Cases.Zip2005.Image.F_7803c684

namespace Cases.Zip2005.WriteVectored

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog
  Cases.Zip2005.Image

set_option autoImplicit false

/-- The instructions of `write_vectored`. -/
def prog : List Instr := F_7803c684.prog.filterMap id

theorem prog_map : prog.map some = F_7803c684.prog := by decide

theorem wf : WF prog := by unfold WF; decide

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

theorem addr_len (x : Word) (j : Nat) :
    x + BitVec.ofNat 64 (16 * j) - 16#64 + 24#64 = x + BitVec.ofNat 64 (8 * (2 * j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem addr_next (x : Word) (j : Nat) :
    x + BitVec.ofNat 64 (16 * j) - 16#64 + 16#64 = x + BitVec.ofNat 64 (16 * (j + 1)) - 16#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem addr_ptr (x : Word) (j : Nat) :
    x + BitVec.ofNat 64 (16 * (j + 1)) - 16#64 = x + BitVec.ofNat 64 (8 * (2 * j)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem count_dec {n j : Nat} (h : j < n) :
    BitVec.ofNat 64 (16 * (n - j)) + 0xfffffffffffffff0#64 = BitVec.ofNat 64 (16 * (n - (j + 1))) := by
  have e : (0xfffffffffffffff0#64 : Word) = -16#64 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, show 16 * (n - j) = 16 * (n - (j + 1)) + 16 by omega,
    BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_eq_zero {x : Nat} (hx : x < 2 ^ 64) (h : BitVec.ofNat 64 x = 0#64) : x = 0 := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this

/-- Reaching the call: the run stops at the `auipc` that starts it, instruction 18. -/
abbrev ToCall (s0 : MachineState) (sp : Word) (xs : List Word) (st : State rvIsa) : Prop :=
  st.pc = 2 * 18 + 1 ∧ AtCall s0 sp xs (ofParts st.regs st.m)

theorem kept_ne {r : Reg} (hr : r ∈ kept) :
    r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 := by
  simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- From label 16 to the call: `a0 := 2`, `a2 := s1`. -/
theorem tail (s0 : MachineState) (sp : Word) (xs : List Word) (regs : String → BitVec 64)
    (m u : MachineState) (hag : Agree (ofParts regs m) u) (h2 : u.getReg .x2 = sp - 32#64)
    (h8 : u.getReg .x8 = sp) (h9 : u.getReg .x9 = firstLen xs) (hs : Saved s0 sp u) :
    rvIsa.Reaches (lift prog) (ToCall s0 sp xs) ⟨32, regs, m⟩ := by
  apply reaches_label (kd := .internal) (l := 16) (by decide)
  apply reaches_opn hag (i := .ADDI .x10 .x0 2) (by decide) rfl rfl
  intro r1 m1 hag1
  apply reaches_label (kd := .internal) (l := 17) (by decide)
  apply reaches_opn hag1 (i := .ADDI .x12 .x9 0) (by decide) rfl rfl
  intro r2 m2 hag2
  apply reaches_label (kd := .internal) (l := 18) (by decide)
  refine Isa.Reaches.done ⟨rfl, AtCall.of_agree hag2 ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [execInstrBr, getReg_setReg_ite, h2]
  · simp [execInstrBr, getReg_setReg_ite, h8]
  · simp [execInstrBr, getReg_setReg_ite, h9]
  · simp [execInstrBr, getReg_setReg_ite, signExtend12, getReg_x0']
  · refine hs.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => ?_
    obtain ⟨-, -, -, -, h10, -, h12⟩ := kept_ne hr
    simp [execInstrBr, getReg_setReg_ite, Ne.symm h10, Ne.symm h12]

theorem se_24 : signExtend12 (0x018 : BitVec 12) = 24#64 := by decide
theorem se_16 : signExtend12 (0x010 : BitVec 12) = 16#64 := by decide
theorem se_m16 : signExtend12 (0xff0 : BitVec 12) = 0xfffffffffffffff0#64 := by decide
theorem se_0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
theorem se_24' : signExtend12 24#12 = 24#64 := by decide
theorem se_16' : signExtend12 16#12 = 16#64 := by decide
theorem se_m16' : signExtend12 4080#12 = 0xfffffffffffffff0#64 := by decide

set_option maxHeartbeats 4000000 in
/-- **The loop** over the slices, at its head (label 7), with `j` slices passed. -/
theorem loop (s0 : MachineState) (sp bufs : Word) (xs : List Word) (n : Nat) {lo hi : Nat}
    (hxl : xs.length = 2 * n) (hok : RegionOk lo hi bufs (2 * n)) (hn : 16 * n < 2 ^ 64) :
    ∀ k j (regs : String → BitVec 64) (m u : MachineState), n - j = k → j ≤ n →
      Agree (ofParts regs m) u → u.getReg .x2 = sp - 32#64 → u.getReg .x8 = sp →
      u.getReg .x11 = bufs + BitVec.ofNat 64 (16 * j) - 16#64 →
      u.getReg .x12 = BitVec.ofNat 64 (16 * (n - j)) →
      firstLen (xs.drop (2 * j)) = firstLen xs → Region bufs xs u → Saved s0 sp u →
      rvIsa.Reaches (lift prog) (ToCall s0 sp xs) ⟨14, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro j regs m u hk hj hag h2 h8 h11 h12 hfl hreg hs
    obtain rfl : j = n := by omega
    -- every slice is empty: the length is zero
    apply reaches_label (kd := .internal) (l := 7) (by decide)
    apply reaches_cond hag (op := "eq") (a := .x12) (b := .x0) (l := 14) (by decide)
      (c := u.getReg .x12 == u.getReg .x0) (by simp [cmpEval]) (j := 28) (by decide)
    · intro _
      apply reaches_label (kd := .internal) (l := 14) (by decide)
      apply reaches_opn hag (i := .ADDI .x9 .x0 0) (by decide) rfl rfl
      intro r1 m1 hag1
      apply reaches_label (kd := .internal) (l := 15) (by decide)
      apply reaches_opn hag1 (i := .ADDI .x11 .x0 1) (by decide) rfl rfl
      intro r2 m2 hag2
      refine tail s0 sp xs r2 m2 _ hag2 (by simp [execInstrBr, getReg_setReg_ite, h2])
        (by simp [execInstrBr, getReg_setReg_ite, h8]) ?_ ?_
      · rw [← hfl, show 2 * j = xs.length by omega, List.drop_length]
        simp [execInstrBr, getReg_setReg_ite, getReg_x0', signExtend12, firstLen]
      · have hs1 : Saved s0 sp (execInstrBr u (.ADDI .x9 .x0 0)) :=
          hs.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => by
            obtain ⟨-, -, -, h9, -, -, -⟩ := kept_ne hr
            simp [execInstrBr, getReg_setReg_ite, Ne.symm h9]
        exact hs1.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => by
          obtain ⟨-, -, -, -, -, h11, -⟩ := kept_ne hr
          simp [execInstrBr, getReg_setReg_ite, Ne.symm h11]
    · intro hc
      simp [h12, getReg_x0'] at hc
  | succ k ih =>
    intro j regs m u hk hj hag h2 h8 h11 h12 hfl hreg hs
    have hjn : j < n := by omega
    apply reaches_label (kd := .internal) (l := 7) (by decide)
    apply reaches_cond hag (op := "eq") (a := .x12) (b := .x0) (l := 14) (by decide)
      (c := u.getReg .x12 == u.getReg .x0) (by simp [cmpEval]) (j := 28) (by decide)
    · intro hc
      simp only [h12, getReg_x0', beq_iff_eq] at hc
      have := ofNat_eq_zero (by omega) hc
      omega
    intro _
    -- slice `j`: load its length, step the pointer and the count
    apply reaches_label (kd := .internal) (l := 8) (by decide)
    apply reaches_opn hag (i := .LD .x9 .x11 0x018) (by decide) rfl
      (memOk_LD (by rw [h11, se_24, addr_len]; exact dwordOk hok (by omega)))
    intro r1 m1 hag1
    apply reaches_label (kd := .internal) (l := 9) (by decide)
    apply reaches_opn hag1 (i := .ADDI .x11 .x11 0x010) (by decide) rfl rfl
    intro r2 m2 hag2
    apply reaches_label (kd := .internal) (l := 10) (by decide)
    apply reaches_opn hag2 (i := .ADDI .x12 .x12 0xff0) (by decide) rfl rfl
    intro r3 m3 hag3
    generalize hu3 : execInstrBr (execInstrBr (execInstrBr u (.LD .x9 .x11 0x018))
      (.ADDI .x11 .x11 0x010)) (.ADDI .x12 .x12 0xff0) = u3 at hag3
    have e : ∀ r, u3.getReg r = if .x12 = r then BitVec.ofNat 64 (16 * (n - (j + 1)))
        else if .x11 = r then bufs + BitVec.ofNat 64 (16 * (j + 1)) - 16#64
        else if .x9 = r then xs[2 * j + 1]! else u.getReg r := by
      intro r; subst hu3
      simp [execInstrBr, getReg_setReg_ite, h11, h12, se_24', se_16', se_m16', addr_next, count_dec hjn,
        hreg (2 * j + 1) (by omega), addr_len]
    have em : ∀ a, u3.getMem a = u.getMem a := by intro a; subst hu3; simp [execInstrBr]
    have ec : u3.code = u.code := by subst hu3; simp [execInstrBr]
    have hs3 : Saved s0 sp u3 := hs.step em ec fun r hr => by
      obtain ⟨-, -, -, h9, -, h11, h12⟩ := kept_ne hr
      rw [e]; simp [Ne.symm h9, Ne.symm h11, Ne.symm h12]
    have hreg3 : Region bufs xs u3 := fun i hi => (em _).trans (hreg i hi)
    clear hu3
    apply reaches_label (kd := .internal) (l := 11) (by decide)
    apply reaches_cond hag3 (op := "eq") (a := .x9) (b := .x0) (l := 7) (by decide)
      (c := u3.getReg .x9 == u3.getReg .x0) (by simp [cmpEval]) (j := 14) (by decide)
    · -- an empty slice: round again
      intro hc
      simp only [e, getReg_x0', beq_iff_eq, reduceCtorEq, if_false, if_true] at hc
      refine ih (j + 1) r3 m3 u3 (by omega) hjn hag3 (by simp [e, h2]) (by simp [e, h8])
        (by simp [e]) (by simp [e]) ?_ hreg3 hs3
      rw [← hfl, firstLen_drop (j := j) (by omega), if_pos hc, show 2 * (j + 1) = 2 * j + 2 by omega]
    · -- the first non-empty slice: load its pointer and go to the call
      intro hc
      simp only [e, getReg_x0', beq_eq_false_iff_ne, ne_eq, reduceCtorEq, if_false, if_true] at hc
      apply reaches_label (kd := .internal) (l := 12) (by decide)
      apply reaches_opn hag3 (i := .LD .x11 .x11 0) (by decide) rfl
        (memOk_LD (by
          rw [e]; simp only [reduceCtorEq, if_false, if_true]
          rw [se_0, BitVec.add_zero, addr_ptr]
          exact dwordOk hok (by omega)))
      intro r4 m4 hag4
      apply reaches_label (kd := .internal) (l := 13) (by decide)
      apply reaches_goto (n := "") (l := 16) (by decide) (j := 32) (by decide)
      refine tail s0 sp xs r4 m4 _ hag4 (by simp [execInstrBr, getReg_setReg_ite, e, h2])
        (by simp [execInstrBr, getReg_setReg_ite, e, h8]) ?_ ?_
      · rw [← hfl, firstLen_drop (j := j) (by omega), if_neg hc]
        simp [execInstrBr, getReg_setReg_ite, e]
      · refine hs3.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => ?_
        obtain ⟨-, -, -, -, -, h11, -⟩ := kept_ne hr
        simp [execInstrBr, getReg_setReg_ite, Ne.symm h11]

theorem cw_of_code {lo hi : Nat} {u v : MachineState} (h : CodeWithin lo hi u) (hc : v.code = u.code) :
    CodeWithin lo hi v := fun a ha => h a (by rwa [hc] at ha)

/-- A doubleword store into cell `i` of a well-placed region passes the SP1 check. -/
theorem sdOk {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n) {u : MachineState}
    (hcw : CodeWithin lo hi u) {i : Nat} (hi : i < n) {rs1 rs2 : Reg} {off : BitVec 12}
    (ha : u.getReg rs1 + signExtend12 off = base + BitVec.ofNat 64 (8 * i)) :
    memOkSp1 u (.SD rs1 rs2 off) = true :=
  memOk_SD (by rw [ha]; exact dwordOk h hi)
    (by rw [ha]; simpa using noCodeOk h hcw (k := 0) hi (by omega) (by omega) (by omega))

/-! Addresses in the form `simp` leaves them. -/

theorem a9 (sp : Word) : sp + signExtend12 4064#12 + signExtend12 24#12 = sp - 80#64 + 72#64 := by
  simp only [signExtend12]; bv_decide
theorem a8 (sp : Word) : sp + signExtend12 4064#12 + signExtend12 16#12 = sp - 80#64 + 64#64 := by
  simp only [signExtend12]; bv_decide
theorem a7 (sp : Word) : sp + signExtend12 4064#12 + signExtend12 8#12 = sp - 80#64 + 56#64 := by
  simp only [signExtend12]; bv_decide
theorem sp_32 (sp : Word) : sp + signExtend12 4064#12 = sp - 32#64 := by
  simp only [signExtend12]; bv_decide
theorem sp_back (sp : Word) : sp - 32#64 + signExtend12 32#12 = sp := by
  simp only [signExtend12]; bv_decide
theorem bufs_m16 (b : Word) : b + signExtend12 4080#12 = b - 16#64 := by
  simp only [signExtend12]; bv_decide

theorem cell_ne {base : Word} {i j : Nat} (hi : i < 10) (hj : j < 10) (h : i ≠ j) :
    base + BitVec.ofNat 64 (8 * i) ≠ base + BitVec.ofNat 64 (8 * j) := by
  intro e
  rw [BitVec.add_comm base, BitVec.add_comm base] at e
  have e' := congrArg (· - base) e
  simp only [BitVec.add_sub_cancel] at e'
  have := congrArg BitVec.toNat e'
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem slli4 {n : Nat} (hn : 16 * n < 2 ^ 64) :
    BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * (n - 0)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem inRegion_cell {lo hi : Nat} {b : Word} (h : RegionOk lo hi b 10) {i : Nat} (hi : i < 10) :
    InRegion (b + BitVec.ofNat 64 (8 * i)) b 10 := by
  have := toNat_cell h (i := i) (k := 0) hi (by omega)
  simp only [Nat.add_zero] at this
  unfold InRegion; omega

set_option maxHeartbeats 4000000 in
/-- **From the entry to the call.** -/
theorem toCall (s0 : MachineState) (sp bufs : Word) (xs : List Word) (n : Nat) {lo hi lo' hi' : Nat}
    (hxl : xs.length = 2 * n) (hok : RegionOk lo hi bufs (2 * n))
    (hfr : RegionOk lo' hi' (sp - 0x50#64) 10) (hcw : CodeWithin lo' hi' s0)
    (hdis : Disjoint bufs (2 * n) (sp - 0x50#64) 10)
    (regs : String → BitVec 64) (m : MachineState) (hag : Agree (ofParts regs m) s0)
    (h2 : s0.getReg .x2 = sp) (h11 : s0.getReg .x11 = bufs) (h12 : s0.getReg .x12 = BitVec.ofNat 64 n)
    (hreg : Region bufs xs s0) :
    rvIsa.Reaches (lift prog) (ToCall s0 sp xs) ⟨0, regs, m⟩ := by
  have hn : 16 * n < 2 ^ 64 := by have := hok.inMem; unfold SP1_MAX_MEMORY at this; omega
  -- the frame and the saves
  apply reaches_label (kd := .internal) (l := 0) (by decide)
  apply reaches_opn hag (i := .ADDI .x2 .x2 0xfe0) (by decide) rfl rfl
  intro r1 m1 hag1
  have c1 : (execInstrBr s0 (.ADDI .x2 .x2 0xfe0)).code = s0.code := by simp [execInstrBr]
  apply reaches_label (kd := .internal) (l := 1) (by decide)
  apply reaches_opn hag1 (i := .SD .x2 .x1 0x018) (by decide) rfl
    (sdOk hfr (cw_of_code hcw c1) (i := 9) (by omega)
      (by simp [execInstrBr, getReg_setReg_ite, h2, a9]))
  intro r2 m2 hag2
  apply reaches_label (kd := .internal) (l := 2) (by decide)
  apply reaches_opn hag2 (i := .SD .x2 .x8 0x010) (by decide) rfl
    (sdOk hfr (cw_of_code hcw (by simp [execInstrBr])) (i := 8) (by omega)
      (by simp [execInstrBr, getReg_setReg_ite, getReg_setMem', h2, a8]))
  intro r3 m3 hag3
  apply reaches_label (kd := .internal) (l := 3) (by decide)
  apply reaches_opn hag3 (i := .SD .x2 .x9 0x008) (by decide) rfl
    (sdOk hfr (cw_of_code hcw (by simp [execInstrBr])) (i := 7) (by omega)
      (by simp [execInstrBr, getReg_setReg_ite, getReg_setMem', h2, a7]))
  intro r4 m4 hag4
  apply reaches_label (kd := .internal) (l := 4) (by decide)
  apply reaches_opn hag4 (i := .ADDI .x8 .x2 0x020) (by decide) rfl rfl
  intro r5 m5 hag5
  apply reaches_label (kd := .internal) (l := 5) (by decide)
  apply reaches_opn hag5 (i := .ADDI .x11 .x11 0xff0) (by decide) rfl rfl
  intro r6 m6 hag6
  apply reaches_label (kd := .internal) (l := 6) (by decide)
  apply reaches_opn hag6 (i := .SLLI .x12 .x12 4) (by decide) rfl rfl
  intro r7 m7 hag7
  generalize hu : execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr
    (execInstrBr s0 (.ADDI .x2 .x2 0xfe0)) (.SD .x2 .x1 0x018)) (.SD .x2 .x8 0x010))
    (.SD .x2 .x9 0x008)) (.ADDI .x8 .x2 0x020)) (.ADDI .x11 .x11 0xff0)) (.SLLI .x12 .x12 4) = u
    at hag7
  have hne : ∀ i j, i < 10 → j < 10 → i ≠ j →
      sp - 0x50#64 + BitVec.ofNat 64 (8 * i) ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * j) :=
    fun i j hi hj h => cell_ne hi hj h
  have em : ∀ a, u.getMem a =
      if a = sp - 0x50#64 + BitVec.ofNat 64 (8 * 7) then s0.getReg .x9
      else if a = sp - 0x50#64 + BitVec.ofNat 64 (8 * 8) then s0.getReg .x8
      else if a = sp - 0x50#64 + BitVec.ofNat 64 (8 * 9) then s0.getReg .x1 else s0.getMem a := by
    intro a; subst hu
    simp [execInstrBr, getMem_setMem_ite, getReg_setMem', getReg_setReg_ite, h2, a9, a8, a7]
  have e : ∀ r, u.getReg r = if .x12 = r then BitVec.ofNat 64 (16 * (n - 0))
      else if .x11 = r then bufs + BitVec.ofNat 64 (16 * 0) - 16#64
      else if .x8 = r then sp else if .x2 = r then sp - 32#64 else s0.getReg r := by
    intro r; subst hu
    simp [execInstrBr, getReg_setMem', getReg_setReg_ite, h2, h11, h12, sp_32, sp_back, bufs_m16,
      slli4 hn]
  have ec : u.code = s0.code := by subst hu; simp [execInstrBr]
  have hunch : Unchanged (frame sp) s0 u := by
    intro a ha
    have hnot := ha _ (List.mem_singleton_self _)
    rw [em]
    have h7 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 7) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
    have h8 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 8) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
    have h9 : a ≠ sp - 0x50#64 + BitVec.ofNat 64 (8 * 9) := fun h => hnot (h ▸ inRegion_cell hfr (by omega))
    simp [h7, h8, h9]
  have hs : Saved s0 sp u := by
    refine ⟨?_, ?_, ?_, hunch, ec, fun r hr => ?_⟩
    · rw [em]; simp [hne 9 7 (by omega) (by omega) (by omega), hne 9 8 (by omega) (by omega) (by omega)]
    · rw [em]; simp [hne 8 7 (by omega) (by omega) (by omega)]
    · rw [em]; simp
    · obtain ⟨-, h2', h8', -, -, h11', h12'⟩ := kept_ne hr
      rw [e]; simp [Ne.symm h2', Ne.symm h8', Ne.symm h11', Ne.symm h12']
  clear hu
  exact loop s0 sp bufs xs n hxl hok hn n 0 r7 m7 u (by omega) (Nat.zero_le _) hag7
    (by simp [e]) (by simp [e]) (by simp [e]) (by simp [e]) (by simp)
    (hreg.of_unchanged hunch (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rwa [hxl]))
    hs

theorem b9 (sp : Word) : sp - 32#64 + signExtend12 24#12 = sp - 80#64 + 72#64 := by
  simp only [signExtend12]; bv_decide
theorem b8 (sp : Word) : sp - 32#64 + signExtend12 16#12 = sp - 80#64 + 64#64 := by
  simp only [signExtend12]; bv_decide
theorem b7 (sp : Word) : sp - 32#64 + signExtend12 8#12 = sp - 80#64 + 56#64 := by
  simp only [signExtend12]; bv_decide

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

set_option maxHeartbeats 4000000 in
/-- **From the return of the call to the end.** -/
theorem fromCall (s0 : MachineState) (sp : Word) (xs : List Word) {lo hi : Nat}
    (hfr : RegionOk lo hi (sp - 0x50#64) 10) (regs : String → BitVec 64) (m u : MachineState)
    (hag : Agree (ofParts regs m) u) (h2 : u.getReg .x2 = sp - 32#64) (h9 : u.getReg .x9 = firstLen xs)
    (hs : Saved s0 sp u) :
    rvIsa.Halts (lift prog)
      (fun st => st.pc = 2 * prog.length + 1 ∧ Done s0 sp xs (ofParts st.regs st.m)) ⟨40, regs, m⟩ := by
  apply reaches_label (kd := .internal) (l := 20) (by decide)
  apply reaches_opn hag (i := .ADDI .x10 .x0 0) (by decide) rfl rfl
  intro r1 m1 hag1
  apply reaches_label (kd := .internal) (l := 21) (by decide)
  apply reaches_opn hag1 (i := .ADDI .x11 .x9 0) (by decide) rfl rfl
  intro r2 m2 hag2
  apply reaches_label (kd := .internal) (l := 22) (by decide)
  apply reaches_opn hag2 (i := .LD .x1 .x2 0x018) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg_ite, h2, b9] using dwordOk hfr (i := 9) (by omega)))
  intro r3 m3 hag3
  apply reaches_label (kd := .internal) (l := 23) (by decide)
  apply reaches_opn hag3 (i := .LD .x8 .x2 0x010) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg_ite, h2, b8] using dwordOk hfr (i := 8) (by omega)))
  intro r4 m4 hag4
  apply reaches_label (kd := .internal) (l := 24) (by decide)
  apply reaches_opn hag4 (i := .LD .x9 .x2 0x008) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg_ite, h2, b7] using dwordOk hfr (i := 7) (by omega)))
  intro r5 m5 hag5
  apply reaches_label (kd := .internal) (l := 25) (by decide)
  apply reaches_opn hag5 (i := .ADDI .x2 .x2 0x020) (by decide) rfl rfl
  intro r6 m6 hag6
  apply reaches_label (kd := .internal) (l := 26) (by decide)
  apply halts_ret (by decide)
  have hra := hs.ra; have hfp := hs.fp; have hs1 := hs.s1
  simp only [Nat.reduceMul] at hra hfp hs1
  refine ⟨by dsimp only; decide, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩⟩ <;>
    simp only [Agree.regs hag6, Agree.mem hag6, Agree.code hag6]
  · simp [execInstrBr, getReg_setReg_ite, h2, b9, hra]
  · simp [execInstrBr, getReg_setReg_ite, h2, sp_back]
  · simp [execInstrBr, getReg_setReg_ite, h2, b8, hfp]
  · simp [execInstrBr, getReg_setReg_ite, h2, b7, hs1]
  · simp [execInstrBr, getReg_setReg_ite, signExtend12, getReg_x0']
  · simp [execInstrBr, getReg_setReg_ite, h9, signExtend12]
  · obtain ⟨h1, h2', h8, h9', h10, h11, -⟩ := kept_ne hr
    simp [execInstrBr, getReg_setReg_ite, Ne.symm h1, Ne.symm h2', Ne.symm h8, Ne.symm h9', Ne.symm h10,
      Ne.symm h11]
    exact hs.regs r hr
  · simp [execInstrBr]; exact hs.unch a ha
  · simp [execInstrBr]; exact hs.code

theorem agree_symm {t u : MachineState} (h : Agree t u) : Agree u t :=
  ⟨fun r => (h.regs r).symm, fun a => (h.mem a).symm, h.code.symm, h.committed.symm,
    h.publicValues.symm, h.privateInput.symm, h.inputBufBase.symm⟩

theorem Done.of_agree {s0 u v : MachineState} {sp : Word} {xs : List Word} (hag : Agree v u)
    (h : Done s0 sp xs u) : Done s0 sp xs v :=
  ⟨(hag.regs _).trans h.x1, (hag.regs _).trans h.x2, (hag.regs _).trans h.x8,
    (hag.regs _).trans h.x9, (hag.regs _).trans h.x10, (hag.regs _).trans h.x11,
    fun r hr => (hag.regs r).trans (h.regs r hr), fun a ha => (hag.mem a).trans (h.unch a ha),
    hag.code.trans h.code⟩

theorem stack_sub {sp : Word} (h : StackOk Ro.layout 0x50 sp) : StackOk Ro.layout 0x30 (sp - 32#64) := by
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

set_option maxHeartbeats 4000000 in
/-- **`write_vectored(self, bufs)` over `stepSp1`**: it writes the first non-empty slice to
    stderr and returns `Ok(len)`, `0` in `x10` and that slice's length in `x11` (`0` if every
    slice is empty), with the callee-saved registers restored, the code untouched and memory
    changed only in the frame below `sp`. -/
theorem spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp bufs : Word)
    (xs : List Word) (cnt : Nat)
    (hpc : s.pc = 0x7803c684#64) (hcode : CodeAt F_7803c684.base F_7803c684.prog s)
    (hcodeS : CodeAt F_7801bfa4.base F_7801bfa4.prog s) (hcodeW : CodeAt F_7801b3b0.base F_7801b3b0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (hb : s.getReg .x11 = bufs) (hc : s.getReg .x12 = BitVec.ofNat 64 cnt)
    (hx : Region bufs xs s) (hxl : xs.length = 2 * cnt)
    (hokx : RegionOk Ro.layout.textLo Ro.layout.textHi bufs (2 * cnt))
    (hdis : Disjoint bufs (2 * cnt) (sp - 0x50#64) 10)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged (frame sp) s t →
      t.getReg .x10 = 0#64 → t.getReg .x11 = firstLen xs → SafeN G n P t) :
    SafeN G n P s := by
  have hfr : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hstk.frame 10 (by decide)
  have hc' : CodeAt F_7803c684.base (prog.map some) s := prog_map ▸ hcode
  -- from the entry to the call, at Lprog
  refine SafeN.of_reaches wf (sim_entry (fun _ => 0) hc' (by rw [hpc]; rfl))
    (toCall s sp bufs xs cnt hxl hokx hfr hcw hdis _ _ (agree_ofParts_regsOf _ s) hsp hb hc hx) ?_
  rintro sA tA hsA ⟨hpcA, hatV⟩
  have hsim0code : CodeAt F_7803c684.base (prog.map some) tA := hsA.code
  have hat := AtCall.of_agree (agree_symm hsA.agree) hatV
  have htc : tA.code = s.code := hat.saved.code
  obtain ⟨hfA, hpcA'⟩ := fetch_call hsA (k := 18) (by decide) hpcA
  -- the call, over the machine: `auipc ra` and `jalr ra`, then `sys_write`
  have hf18 : tA.code tA.pc = some (.AUIPC .x1 0xfffe0) := by rw [hfA]; rfl
  have hpcv : tA.pc = 0x7803c6cc#64 := by rw [hpcA']; rfl
  generalize ht1 : execInstrBr tA (.AUIPC .x1 0xfffe0) = t1
  have hs1 : stepSp1 tA = some t1 := ht1 ▸ stepSp1_plain hf18 rfl (by decide) (by decide)
  have h1pc : t1.pc = 0x7803c6d0#64 := by subst ht1; simp [execInstrBr, hpcv, pc_setPC']
  have h1c : t1.code = tA.code := by subst ht1; simp [execInstrBr]
  have hf19 : t1.code t1.pc = some (.JALR .x1 .x1 0x8d8) := by
    rw [h1c, h1pc]
    have := hsA.code 19 (by decide)
    rw [show F_7803c684.base + BitVec.ofNat 64 (4 * 19) = 0x7803c6d0#64 by decide] at this
    rw [this]; decide
  generalize ht2 : execInstrBr t1 (.JALR .x1 .x1 0x8d8) = t2
  have hs2 : stepSp1 t1 = some t2 := ht2 ▸ stepSp1_plain hf19 rfl (by decide) (by decide)
  have e1 : ∀ r, t1.getReg r = if .x1 = r then 0x7803c6cc#64 + 0xfffffffffffe0000#64 else tA.getReg r := by
    intro r; subst ht1; simp [execInstrBr, getReg_setReg_ite, hpcv]
  have e2 : ∀ r, t2.getReg r = if .x1 = r then 0x7803c6d4#64 else tA.getReg r := by
    intro r; subst ht2; simp [execInstrBr, getReg_setReg_ite, h1pc, e1]
    split <;> rfl
  have h2pc : t2.pc = 0x7801bfa4#64 := by
    subst ht2; simp [execInstrBr, pc_setPC', e1, signExtend12]
  have h2m : ∀ a, t2.getMem a = tA.getMem a := by
    intro a; subst ht2 ht1; simp [execInstrBr]
  have h2c : t2.code = s.code := by subst ht2; simp [execInstrBr, h1c, htc]
  refine SafeN.steps (k := 2) (by rw [stepsSp1_succ_of_step hs1, stepsSp1_succ_of_step hs2]; rfl) ?_
  have hsA : Saved s sp tA := hat.saved
  refine sys_write_spec t2 0x7803c6d4#64 (sp - 32#64) 2#64 h2pc (codeAt_of_code_eq h2c hcodeS)
    (codeAt_of_code_eq h2c hcodeW) (cw_of_code hcw h2c) (by rw [e2]; rfl) (by decide)
    (by rw [e2]; simpa using hat.x2) (stack_sub hstk) (by rw [e2]; simpa using hat.x10) (by decide) ?_
  intro t3 h3pc h3cs h3c h3u
  rw [callee_frame] at h3u
  -- back at Lprog, after the call
  have h3x : ∀ r ∈ calleeSavedRegs, t3.getReg r = tA.getReg r := fun r hr => by
    rw [h3cs r hr, e2]
    have : Reg.x1 ≠ r := by
      intro h; subst h; revert hr; decide
    simp [this]
  have hs3 : Saved s sp t3 := by
    have hm : ∀ i, 6 ≤ i → i < 10 → t3.getMem (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) =
        tA.getMem (sp - 0x50#64 + BitVec.ofNat 64 (8 * i)) := fun i h6 h10 => by
      rw [h3u _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact own_out hfr h6 h10),
        h2m]
    refine ⟨(hm 9 (by omega) (by omega)).trans hsA.ra, (hm 8 (by omega) (by omega)).trans hsA.fp,
      (hm 7 (by omega) (by omega)).trans hsA.s1, fun a ha => ?_, h3c.trans h2c, fun r hr => ?_⟩
    · have hnot := ha _ (List.mem_singleton_self _)
      rw [h3u _ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact out_of_out hnot), h2m]
      exact hsA.unch a ha
    · rw [h3x r (by revert hr; revert r; decide)]; exact hsA.regs r hr
  have hsim3 := sim_return (base := F_7803c684.base) (prog := prog) (k := 19) (by decide) (fun _ => 0)
    (codeAt_of_code_eq (h3c.trans (h2c.trans htc.symm)) hsim0code) (by rw [h3pc]; decide)
  refine SafeN.of_reaches wf hsim3 (fromCall s sp xs hfr _ _ t3 (agree_ofParts_regsOf _ t3)
    (by rw [h3x .x2 (by decide)]; exact hat.x2) (by rw [h3x .x9 (by decide)]; exact hat.x9) hs3) ?_
  rintro s' t' hs' ⟨-, hpc', hdV⟩
  have hd := Done.of_agree (agree_symm hs'.agree) hdV
  apply hk
  · rcases hs'.pc with ⟨hle, _⟩ | ⟨_, ht⟩
    · rw [hpc'] at hle; omega
    · rw [ht, hd.x1, hra, hra1]
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

end Cases.Zip2005.WriteVectored
