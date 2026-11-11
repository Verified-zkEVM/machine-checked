/-
  Cases.Zip2005.Runtime.WriteVectored

  `<Stderr as io::Write>::write_vectored(self, bufs)`, proved at Lprog: a function with a loop
  and a call.

  It saves `ra`, `s0` and `s1`, walks the `IoSlice`s at `bufs` (pairs of a pointer and a
  length) to the first that is not empty, and calls `sys_write(2, ptr, len)` on it (on
  nothing if all are empty). It returns `Ok(len)`: `0` in `x10` and `len` in `x11`.

  The function is proved at Lprog, in a program of three functions: `write_vectored`,
  `sys_write` (two instructions: a tail call) and `syscall_write`. The call is an Lprog call
  (`Lcall`), which uses `sys_write`'s contract at Lprog (`sw_contract`), which tail-calls
  `syscall_write`'s (`scw_contract`); nothing is run over the machine by hand. The body runs
  from the entry to the call (`toCall`, with the loop `loop`), through the call, and from the
  return to the end (`fromCall`). `spec` carries the contract to `stepSp1` with the transfer
  theorem (`SafeN.of_contract`), and keeps the statement it had when the call was taken over
  the machine.
-/

import MachineChecked.RiscV.Lprog.Rules
import Cases.Zip2005.Runtime.Trivial
import Cases.Zip2005.Image.F_7803c684

namespace Cases.Zip2005.WriteVectored

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog MachineChecked.RiscV.Lprog
  Cases.Zip2005.Image

set_option autoImplicit false

/-- The instructions of `write_vectored`. -/
def prog : List Instr := F_7803c684.prog.filterMap id

theorem prog_map : prog.map some = F_7803c684.prog := by decide

/-- The instructions of `sys_write`. -/
def swProg : List Instr := F_7801bfa4.prog.filterMap id

theorem swProg_map : swProg.map some = F_7801bfa4.prog := by decide

/-- The instructions of `syscall_write`. -/
def scwProg : List Instr := F_7801b3b0.prog.filterMap id

theorem scwProg_map : scwProg.map some = F_7801b3b0.prog := by decide

/-- The program: `write_vectored`, `sys_write` and `syscall_write`. -/
def fs : List Fn :=
  [⟨"write_vectored", F_7803c684.base, prog, 0x20⟩, ⟨"sys_write", F_7801bfa4.base, swProg, 0⟩,
    ⟨"syscall_write", F_7801b3b0.base, scwProg, 0x30⟩]

theorem hok : ProgOk fs := by decide

theorem hf0 : (liftProg fs)[0]? = some (liftFn fs ⟨"write_vectored", F_7803c684.base, prog, 0x20⟩) := rfl
theorem hf1 : (liftProg fs)[1]? = some (liftFn fs ⟨"sys_write", F_7801bfa4.base, swProg, 0⟩) := rfl
theorem hf2 : (liftProg fs)[2]? = some (liftFn fs ⟨"syscall_write", F_7801b3b0.base, scwProg, 0x30⟩) := rfl

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

theorem kept_ne {r : Reg} (hr : r ∈ kept) :
    r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x8 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 := by
  simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- From label 16 to the call: `a0 := 2`, `a2 := s1`. -/
theorem tail {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp : Word) (xs : List Word)
    (hcall : ∀ r' m', AtCall s0 sp xs (ofParts r' m') → LSafeN fs G N Q ⟨⟨0, 37, rv, top⟩ :: rest, r', m'⟩)
    (regs : Reg → BitVec 64)
    (m u : MachineState) (hag : Agree (ofParts regs m) u) (h2 : u.getReg .x2 = sp - 32#64)
    (h8 : u.getReg .x8 = sp) (h9 : u.getReg .x9 = firstLen xs) (hs : Saved s0 sp u) :
    LSafeN fs G N Q ⟨⟨0, 32, rv, top⟩ :: rest, regs, m⟩ := by
  apply SafeN.label hf0 (kd := .internal) (l := 16) (by decide)
  apply lsafe_opn hf0 hag (i := .ADDI .x10 .x0 2) (by decide) rfl rfl
  intro r1 m1 hag1
  apply SafeN.label hf0 (kd := .internal) (l := 17) (by decide)
  apply lsafe_opn hf0 hag1 (i := .ADDI .x12 .x9 0) (by decide) rfl rfl
  intro r2 m2 hag2
  apply SafeN.label hf0 (kd := .internal) (l := 18) (by decide)
  refine hcall _ _ (AtCall.of_agree hag2 ⟨?_, ?_, ?_, ?_, ?_⟩)
  · simp [execInstrBr, getReg_setReg, h2]
  · simp [execInstrBr, getReg_setReg, h8]
  · simp [execInstrBr, getReg_setReg, h9]
  · simp [execInstrBr, getReg_setReg, signExtend12, getReg_x0]
  · refine hs.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => ?_
    obtain ⟨-, -, -, -, h10, -, h12⟩ := kept_ne hr
    simp [execInstrBr, getReg_setReg, h10, h12]

theorem se_24 : signExtend12 (0x018 : BitVec 12) = 24#64 := by decide
theorem se_16 : signExtend12 (0x010 : BitVec 12) = 16#64 := by decide
theorem se_m16 : signExtend12 (0xff0 : BitVec 12) = 0xfffffffffffffff0#64 := by decide
theorem se_0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
theorem se_24' : signExtend12 24#12 = 24#64 := by decide
theorem se_16' : signExtend12 16#12 = 16#64 := by decide
theorem se_m16' : signExtend12 4080#12 = 0xfffffffffffffff0#64 := by decide

set_option maxHeartbeats 4000000 in
/-- **The loop** over the slices, at its head (label 7), with `j` slices passed. -/
theorem loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp bufs : Word) (xs : List Word) (n : Nat) {lo hi : Nat}
    (hxl : xs.length = 2 * n) (hok : RegionOk lo hi bufs (2 * n)) (hn : 16 * n < 2 ^ 64)
    (hcall : ∀ r' m', AtCall s0 sp xs (ofParts r' m') → LSafeN fs G N Q ⟨⟨0, 37, rv, top⟩ :: rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m u : MachineState), n - j = k → j ≤ n →
      Agree (ofParts regs m) u → u.getReg .x2 = sp - 32#64 → u.getReg .x8 = sp →
      u.getReg .x11 = bufs + BitVec.ofNat 64 (16 * j) - 16#64 →
      u.getReg .x12 = BitVec.ofNat 64 (16 * (n - j)) →
      firstLen (xs.drop (2 * j)) = firstLen xs → Region bufs xs u → Saved s0 sp u →
      LSafeN fs G N Q ⟨⟨0, 14, rv, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro j regs m u hk hj hag h2 h8 h11 h12 hfl hreg hs
    obtain rfl : j = n := by omega
    -- every slice is empty: the length is zero
    apply SafeN.label hf0 (kd := .internal) (l := 7) (by decide)
    apply lsafe_cond hf0 hag (op := "eq") (a := .x12) (b := .x0) (l := 14) (by decide)
      (c := u.getReg .x12 == u.getReg .x0) (by simp [cmpEval]) (j := 28) (by decide)
    · intro _
      apply SafeN.label hf0 (kd := .internal) (l := 14) (by decide)
      apply lsafe_opn hf0 hag (i := .ADDI .x9 .x0 0) (by decide) rfl rfl
      intro r1 m1 hag1
      apply SafeN.label hf0 (kd := .internal) (l := 15) (by decide)
      apply lsafe_opn hf0 hag1 (i := .ADDI .x11 .x0 1) (by decide) rfl rfl
      intro r2 m2 hag2
      refine tail s0 sp xs hcall r2 m2 _ hag2 (by simp [execInstrBr, getReg_setReg, h2])
        (by simp [execInstrBr, getReg_setReg, h8]) ?_ ?_
      · rw [← hfl, show 2 * j = xs.length by omega, List.drop_length]
        simp [execInstrBr, getReg_setReg, getReg_x0, signExtend12, firstLen]
      · have hs1 : Saved s0 sp (execInstrBr u (.ADDI .x9 .x0 0)) :=
          hs.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => by
            obtain ⟨-, -, -, h9, -, -, -⟩ := kept_ne hr
            simp [execInstrBr, getReg_setReg, h9]
        exact hs1.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => by
          obtain ⟨-, -, -, -, -, h11, -⟩ := kept_ne hr
          simp [execInstrBr, getReg_setReg, h11]
    · intro hc
      simp [h12, getReg_x0] at hc
  | succ k ih =>
    intro j regs m u hk hj hag h2 h8 h11 h12 hfl hreg hs
    have hjn : j < n := by omega
    apply SafeN.label hf0 (kd := .internal) (l := 7) (by decide)
    apply lsafe_cond hf0 hag (op := "eq") (a := .x12) (b := .x0) (l := 14) (by decide)
      (c := u.getReg .x12 == u.getReg .x0) (by simp [cmpEval]) (j := 28) (by decide)
    · intro hc
      simp only [h12, getReg_x0, beq_iff_eq] at hc
      have := ofNat_eq_zero (by omega) hc
      omega
    intro _
    -- slice `j`: load its length, step the pointer and the count
    apply SafeN.label hf0 (kd := .internal) (l := 8) (by decide)
    apply lsafe_opn hf0 hag (i := .LD .x9 .x11 0x018) (by decide) rfl
      (memOk_LD (by rw [h11, se_24, addr_len]; exact dwordOk hok (by omega)))
    intro r1 m1 hag1
    apply SafeN.label hf0 (kd := .internal) (l := 9) (by decide)
    apply lsafe_opn hf0 hag1 (i := .ADDI .x11 .x11 0x010) (by decide) rfl rfl
    intro r2 m2 hag2
    apply SafeN.label hf0 (kd := .internal) (l := 10) (by decide)
    apply lsafe_opn hf0 hag2 (i := .ADDI .x12 .x12 0xff0) (by decide) rfl rfl
    intro r3 m3 hag3
    generalize hu3 : execInstrBr (execInstrBr (execInstrBr u (.LD .x9 .x11 0x018))
      (.ADDI .x11 .x11 0x010)) (.ADDI .x12 .x12 0xff0) = u3 at hag3
    have e : ∀ r, u3.getReg r = if r = .x12 then BitVec.ofNat 64 (16 * (n - (j + 1)))
        else if r = .x11 then bufs + BitVec.ofNat 64 (16 * (j + 1)) - 16#64
        else if r = .x9 then xs[2 * j + 1]! else u.getReg r := by
      intro r; subst hu3
      simp [execInstrBr, getReg_setReg, h11, h12, se_24', se_16', se_m16', addr_next, count_dec hjn,
        hreg (2 * j + 1) (by omega), addr_len]
    have em : ∀ a, u3.getMem a = u.getMem a := by intro a; subst hu3; simp [execInstrBr]
    have ec : u3.code = u.code := by subst hu3; simp [execInstrBr]
    have hs3 : Saved s0 sp u3 := hs.step em ec fun r hr => by
      obtain ⟨-, -, -, h9, -, h11, h12⟩ := kept_ne hr
      rw [e]; simp [h9, h11, h12]
    have hreg3 : Region bufs xs u3 := fun i hi => (em _).trans (hreg i hi)
    clear hu3
    apply SafeN.label hf0 (kd := .internal) (l := 11) (by decide)
    apply lsafe_cond hf0 hag3 (op := "eq") (a := .x9) (b := .x0) (l := 7) (by decide)
      (c := u3.getReg .x9 == u3.getReg .x0) (by simp [cmpEval]) (j := 14) (by decide)
    · -- an empty slice: round again
      intro hc
      simp only [e, getReg_x0, beq_iff_eq, reduceCtorEq, if_false, if_true] at hc
      refine ih (j + 1) r3 m3 u3 (by omega) hjn hag3 (by simp [e, h2]) (by simp [e, h8])
        (by simp [e]) (by simp [e]) ?_ hreg3 hs3
      rw [← hfl, firstLen_drop (j := j) (by omega), if_pos hc, show 2 * (j + 1) = 2 * j + 2 by omega]
    · -- the first non-empty slice: load its pointer and go to the call
      intro hc
      simp only [e, getReg_x0, beq_eq_false_iff_ne, ne_eq, reduceCtorEq, if_false, if_true] at hc
      apply SafeN.label hf0 (kd := .internal) (l := 12) (by decide)
      apply lsafe_opn hf0 hag3 (i := .LD .x11 .x11 0) (by decide) rfl
        (memOk_LD (by
          rw [e]; simp only [reduceCtorEq, if_false, if_true]
          rw [se_0, BitVec.add_zero, addr_ptr]
          exact dwordOk hok (by omega)))
      intro r4 m4 hag4
      apply SafeN.label hf0 (kd := .internal) (l := 13) (by decide)
      apply SafeN.goto hf0 (l := 16) (by decide) (j := 32) (by decide)
      refine tail s0 sp xs hcall r4 m4 _ hag4 (by simp [execInstrBr, getReg_setReg, e, h2])
        (by simp [execInstrBr, getReg_setReg, e, h8]) ?_ ?_
      · rw [← hfl, firstLen_drop (j := j) (by omega), if_neg hc]
        simp [execInstrBr, getReg_setReg, e]
      · refine hs3.step (fun a => by simp [execInstrBr]) (by simp [execInstrBr]) fun r hr => ?_
        obtain ⟨-, -, -, -, -, h11, -⟩ := kept_ne hr
        simp [execInstrBr, getReg_setReg, h11]

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
  -- the frame and the saves
  apply SafeN.label hf0 (kd := .internal) (l := 0) (by decide)
  apply lsafe_opn hf0 hag (i := .ADDI .x2 .x2 0xfe0) (by decide) rfl rfl
  intro r1 m1 hag1
  have c1 : (execInstrBr s0 (.ADDI .x2 .x2 0xfe0)).code = s0.code := by simp [execInstrBr]
  apply SafeN.label hf0 (kd := .internal) (l := 1) (by decide)
  apply lsafe_opn hf0 hag1 (i := .SD .x2 .x1 0x018) (by decide) rfl
    (sdOk hfr (cw_of_code hcw c1) (i := 9) (by omega)
      (by simp [execInstrBr, getReg_setReg, h2, a9]))
  intro r2 m2 hag2
  apply SafeN.label hf0 (kd := .internal) (l := 2) (by decide)
  apply lsafe_opn hf0 hag2 (i := .SD .x2 .x8 0x010) (by decide) rfl
    (sdOk hfr (cw_of_code hcw (by simp [execInstrBr])) (i := 8) (by omega)
      (by simp [execInstrBr, getReg_setReg, getReg_setMem, h2, a8]))
  intro r3 m3 hag3
  apply SafeN.label hf0 (kd := .internal) (l := 3) (by decide)
  apply lsafe_opn hf0 hag3 (i := .SD .x2 .x9 0x008) (by decide) rfl
    (sdOk hfr (cw_of_code hcw (by simp [execInstrBr])) (i := 7) (by omega)
      (by simp [execInstrBr, getReg_setReg, getReg_setMem, h2, a7]))
  intro r4 m4 hag4
  apply SafeN.label hf0 (kd := .internal) (l := 4) (by decide)
  apply lsafe_opn hf0 hag4 (i := .ADDI .x8 .x2 0x020) (by decide) rfl rfl
  intro r5 m5 hag5
  apply SafeN.label hf0 (kd := .internal) (l := 5) (by decide)
  apply lsafe_opn hf0 hag5 (i := .ADDI .x11 .x11 0xff0) (by decide) rfl rfl
  intro r6 m6 hag6
  apply SafeN.label hf0 (kd := .internal) (l := 6) (by decide)
  apply lsafe_opn hf0 hag6 (i := .SLLI .x12 .x12 4) (by decide) rfl rfl
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
    simp [execInstrBr, getMem_setMem, getReg_setMem, getReg_setReg, h2, a9, a8, a7]
  have e : ∀ r, u.getReg r = if r = .x12 then BitVec.ofNat 64 (16 * (n - 0))
      else if r = .x11 then bufs + BitVec.ofNat 64 (16 * 0) - 16#64
      else if r = .x8 then sp else if r = .x2 then sp - 32#64 else s0.getReg r := by
    intro r; subst hu
    simp [execInstrBr, getReg_setMem, getReg_setReg, h2, h11, h12, sp_32, sp_back, bufs_m16,
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
      rw [e]; simp [h2', h8', h11', h12']
  clear hu
  exact loop s0 sp bufs xs n hxl hok hn hcall n 0 r7 m7 u (by omega) (Nat.zero_le _) hag7
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
theorem fromCall {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv top : Word}
    {rest : List Frame} (s0 : MachineState) (sp : Word) (xs : List Word) {lo hi : Nat}
    (hfr : RegionOk lo hi (sp - 0x50#64) 10) (regs : Reg → BitVec 64) (m u : MachineState)
    (hag : Agree (ofParts regs m) u) (h2 : u.getReg .x2 = sp - 32#64) (h9 : u.getReg .x9 = firstLen xs)
    (hs : Saved s0 sp u) (hrv : s0.getReg .x1 = rv) (htop : sp = top)
    (hdone : ∀ r' m', Done s0 sp xs (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨0, 40, rv, top⟩ :: rest, regs, m⟩ := by
  apply SafeN.label hf0 (kd := .internal) (l := 20) (by decide)
  apply lsafe_opn hf0 hag (i := .ADDI .x10 .x0 0) (by decide) rfl rfl
  intro r1 m1 hag1
  apply SafeN.label hf0 (kd := .internal) (l := 21) (by decide)
  apply lsafe_opn hf0 hag1 (i := .ADDI .x11 .x9 0) (by decide) rfl rfl
  intro r2 m2 hag2
  apply SafeN.label hf0 (kd := .internal) (l := 22) (by decide)
  apply lsafe_opn hf0 hag2 (i := .LD .x1 .x2 0x018) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, h2, b9] using dwordOk hfr (i := 9) (by omega)))
  intro r3 m3 hag3
  apply SafeN.label hf0 (kd := .internal) (l := 23) (by decide)
  apply lsafe_opn hf0 hag3 (i := .LD .x8 .x2 0x010) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, h2, b8] using dwordOk hfr (i := 8) (by omega)))
  intro r4 m4 hag4
  apply SafeN.label hf0 (kd := .internal) (l := 24) (by decide)
  apply lsafe_opn hf0 hag4 (i := .LD .x9 .x2 0x008) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, h2, b7] using dwordOk hfr (i := 7) (by omega)))
  intro r5 m5 hag5
  apply SafeN.label hf0 (kd := .internal) (l := 25) (by decide)
  apply lsafe_opn hf0 hag5 (i := .ADDI .x2 .x2 0x020) (by decide) rfl rfl
  intro r6 m6 hag6
  apply SafeN.label hf0 (kd := .internal) (l := 26) (by decide)
  have hra := hs.ra; have hfp := hs.fp; have hs1 := hs.s1
  simp only [Nat.reduceMul] at hra hfp hs1
  suffices hD : Done s0 sp xs (ofParts r6 m6) from
    lsafe_ret hf0 hag6 (by decide) (by rw [← hag6.regs]; exact hD.x1.trans hrv)
      (by rw [← hag6.regs]; exact hD.x2.trans htop) (hdone _ _ hD)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩ <;>
    simp only [Agree.regs hag6, Agree.mem hag6, Agree.code hag6]
  · simp [execInstrBr, getReg_setReg, h2, b9, hra]
  · simp [execInstrBr, getReg_setReg, h2, sp_back]
  · simp [execInstrBr, getReg_setReg, h2, b8, hfp]
  · simp [execInstrBr, getReg_setReg, h2, b7, hs1]
  · simp [execInstrBr, getReg_setReg, signExtend12, getReg_x0]
  · simp [execInstrBr, getReg_setReg, h9, signExtend12]
  · obtain ⟨h1, h2', h8, h9', h10, h11, -⟩ := kept_ne hr
    simp [execInstrBr, getReg_setReg, h1, h2', h8, h9', h10,
      h11]
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

/-! ## `syscall_write`, to a descriptor other than 13 -/

/-- What `syscall_write` keeps of the state `u` at its call, in a state `v` it returns in. -/
structure ScwRet (u : MachineState) (sp : Word) (v : MachineState) : Prop where
  cs : CalleeSaved u v
  code : v.code = u.code
  unch : Unchanged [(sp - 0x30#64, 6)] u v

theorem w5 (sp : Word) : sp + signExtend12 4048#12 + signExtend12 40#12 = sp - 48#64 + 40#64 := by
  simp only [signExtend12]; bv_decide
theorem w4 (sp : Word) : sp + signExtend12 4048#12 + signExtend12 32#12 = sp - 48#64 + 32#64 := by
  simp only [signExtend12]; bv_decide
theorem w3 (sp : Word) : sp + signExtend12 4048#12 + signExtend12 24#12 = sp - 48#64 + 24#64 := by
  simp only [signExtend12]; bv_decide
theorem w2 (sp : Word) : sp + signExtend12 4048#12 + signExtend12 16#12 = sp - 48#64 + 16#64 := by
  simp only [signExtend12]; bv_decide
theorem w1 (sp : Word) : sp + signExtend12 4048#12 + signExtend12 8#12 = sp - 48#64 + 8#64 := by
  simp only [signExtend12]; bv_decide
theorem w0 (sp : Word) : sp + signExtend12 4048#12 + signExtend12 0#12 = sp - 48#64 := by
  simp only [signExtend12]; bv_decide
theorem w_sp (sp : Word) : sp + signExtend12 4048#12 = sp - 48#64 := by
  simp only [signExtend12]; bv_decide
theorem w_back (sp : Word) : sp - 48#64 + signExtend12 48#12 = sp := by
  simp only [signExtend12]; bv_decide
theorem ld5 (sp : Word) : sp - 48#64 + signExtend12 40#12 = sp - 48#64 + 40#64 := by
  simp only [signExtend12]; bv_decide
theorem ld4 (sp : Word) : sp - 48#64 + signExtend12 32#12 = sp - 48#64 + 32#64 := by
  simp only [signExtend12]; bv_decide
theorem ld3 (sp : Word) : sp - 48#64 + signExtend12 24#12 = sp - 48#64 + 24#64 := by
  simp only [signExtend12]; bv_decide
theorem ld2 (sp : Word) : sp - 48#64 + signExtend12 16#12 = sp - 48#64 + 16#64 := by
  simp only [signExtend12]; bv_decide
theorem ld1 (sp : Word) : sp - 48#64 + signExtend12 8#12 = sp - 48#64 + 8#64 := by
  simp only [signExtend12]; bv_decide
theorem ld0 (sp : Word) : sp - 48#64 + signExtend12 0#12 = sp - 48#64 := by
  simp only [signExtend12]; bv_decide

theorem se2 : signExtend12 2#12 = 2#64 := by decide
theorem se0 : signExtend12 0#12 = 0#64 := by decide
theorem se13 : signExtend12 13#12 = 13#64 := by decide

theorem inRegion_cell' {lo hi : Nat} {b : Word} {n : Nat} (h : RegionOk lo hi b n) {i : Nat} (hi : i < n) :
    InRegion (b + BitVec.ofNat 64 (8 * i)) b n := by
  have := toNat_cell h (i := i) (k := 0) hi (by omega)
  simp only [Nat.add_zero] at this
  unfold InRegion; omega

theorem cell6_ne {base : Word} {i j : Nat} (hi : i < 6) (hj : j < 6) (h : i ≠ j) :
    base + BitVec.ofNat 64 (8 * i) ≠ base + BitVec.ofNat 64 (8 * j) :=
  cell_ne (by omega) (by omega) h

set_option maxHeartbeats 8000000 in
/-- **`syscall_write`'s contract at Lprog**, to a descriptor other than 13: it writes, and
    returns with the callee-saved registers restored, the code untouched and memory changed
    only in its frame. -/
theorem scw_contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv : Word}
    {rest : List Frame} (u : MachineState) (sp fd : Word) (regs : Reg → BitVec 64) (m : MachineState)
    (hag : Agree (ofParts regs m) u) (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi u)
    (hra : u.getReg .x1 = rv) (hsp : u.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (h10 : u.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (hpost : ∀ r' m', ScwRet u sp (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨2, 0, rv, sp⟩ :: rest, regs, m⟩ := by
  have hfr : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hfr' : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 48#64) 6 := hfr
  -- the prologue: open the frame, save `ra`, `s0`, `s1`, `s2`, `s3`, `s4`
  apply SafeN.label hf2 (kd := .internal) (l := 0) (by decide)
  apply lsafe_opn hf2 hag (i := .ADDI .x2 .x2 0xfd0) (by decide) rfl rfl
  intro r1 m1 hag1
  apply SafeN.label hf2 (kd := .internal) (l := 1) (by decide)
  apply lsafe_opn hf2 hag1 (i := .SD .x2 .x1 0x028) (by decide) rfl
    (sdOk hfr' (cw_of_code hcw (by simp [execInstrBr])) (i := 5) (by omega)
      (by simp [execInstrBr, getReg_setReg, hsp, w5]))
  intro r2 m2 hag2
  apply SafeN.label hf2 (kd := .internal) (l := 2) (by decide)
  apply lsafe_opn hf2 hag2 (i := .SD .x2 .x8 0x020) (by decide) rfl
    (sdOk hfr' (cw_of_code hcw (by simp [execInstrBr])) (i := 4) (by omega)
      (by simp [execInstrBr, getReg_setReg, getReg_setMem, hsp, w4]))
  intro r3 m3 hag3
  apply SafeN.label hf2 (kd := .internal) (l := 3) (by decide)
  apply lsafe_opn hf2 hag3 (i := .SD .x2 .x9 0x018) (by decide) rfl
    (sdOk hfr' (cw_of_code hcw (by simp [execInstrBr])) (i := 3) (by omega)
      (by simp [execInstrBr, getReg_setReg, getReg_setMem, hsp, w3]))
  intro r4 m4 hag4
  apply SafeN.label hf2 (kd := .internal) (l := 4) (by decide)
  apply lsafe_opn hf2 hag4 (i := .SD .x2 .x18 0x010) (by decide) rfl
    (sdOk hfr' (cw_of_code hcw (by simp [execInstrBr])) (i := 2) (by omega)
      (by simp [execInstrBr, getReg_setReg, getReg_setMem, hsp, w2]))
  intro r5 m5 hag5
  apply SafeN.label hf2 (kd := .internal) (l := 5) (by decide)
  apply lsafe_opn hf2 hag5 (i := .SD .x2 .x19 0x008) (by decide) rfl
    (sdOk hfr' (cw_of_code hcw (by simp [execInstrBr])) (i := 1) (by omega)
      (by simp [execInstrBr, getReg_setReg, getReg_setMem, hsp, w1]))
  intro r6 m6 hag6
  apply SafeN.label hf2 (kd := .internal) (l := 6) (by decide)
  apply lsafe_opn hf2 hag6 (i := .SD .x2 .x20 0x000) (by decide) rfl
    (sdOk hfr' (cw_of_code hcw (by simp [execInstrBr])) (i := 0) (by omega)
      (by simp [execInstrBr, getReg_setReg, getReg_setMem, hsp, w0]))
  intro r7 m7 hag7
  apply SafeN.label hf2 (kd := .internal) (l := 7) (by decide)
  apply lsafe_opn hf2 hag7 (i := .ADDI .x8 .x12 0x000) (by decide) rfl rfl
  intro r8 m8 hag8
  apply SafeN.label hf2 (kd := .internal) (l := 8) (by decide)
  apply lsafe_opn hf2 hag8 (i := .ADDI .x5 .x0 0x002) (by decide) rfl rfl
  intro r9 m9 hag9
  generalize hu : execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr
    (execInstrBr (execInstrBr (execInstrBr u (.ADDI .x2 .x2 0xfd0)) (.SD .x2 .x1 0x028))
    (.SD .x2 .x8 0x020)) (.SD .x2 .x9 0x018)) (.SD .x2 .x18 0x010)) (.SD .x2 .x19 0x008))
    (.SD .x2 .x20 0x000)) (.ADDI .x8 .x12 0x000)) (.ADDI .x5 .x0 0x002) = u9 at hag9
  have e9 : ∀ r, u9.getReg r = if r = .x5 then 2#64 else if r = .x8 then u.getReg .x12
      else if r = .x2 then sp - 48#64 else u.getReg r := by
    intro r; subst hu
    simp [execInstrBr, getReg_setMem, getReg_setReg, hsp, w_sp, se0, se2, getReg_x0]
  have em9 : ∀ a, u9.getMem a =
      if a = sp - 48#64 then u.getReg .x20 else if a = sp - 48#64 + 8#64 then u.getReg .x19
      else if a = sp - 48#64 + 16#64 then u.getReg .x18 else if a = sp - 48#64 + 24#64 then u.getReg .x9
      else if a = sp - 48#64 + 32#64 then u.getReg .x8 else if a = sp - 48#64 + 40#64 then u.getReg .x1
      else u.getMem a := by
    intro a; subst hu
    simp [execInstrBr, getMem_setMem, getReg_setMem, getReg_setReg, hsp, w5, w4, w3, w2, w1, w0]
  have ec9 : u9.code = u.code := by subst hu; simp [execInstrBr]
  clear hu
  -- the `WRITE`
  apply SafeN.label hf2 (kd := .internal) (l := 9) (by decide)
  apply lsafe_write hf2 hag9 (by decide) (by rw [e9]; rfl) (by rw [e9]; simpa [h10] using hfd)
  intro r10 m10 hag10
  apply SafeN.label hf2 (kd := .internal) (l := 10) (by decide)
  apply lsafe_opn hf2 hag10 (i := .ADDI .x12 .x0 0x00d) (by decide) rfl rfl
  intro r11 m11 hag11
  -- `fd ≠ 13`: to the epilogue
  apply SafeN.label hf2 (kd := .internal) (l := 11) (by decide)
  apply lsafe_cond hf2 hag11 (op := "ne") (a := .x10) (b := .x12) (l := 62) (by decide) (c := true)
    (by simp [cmpEval, execInstrBr, getReg_setReg, e9, h10, se13, getReg_x0, hfd])
    (j := 124) (by decide) (fun _ => ?_) (fun h => by cases h)
  generalize hu : execInstrBr u9 (.ADDI .x12 .x0 0x00d) = u11 at hag11
  have e11 : ∀ r, u11.getReg r = if r = .x12 then 13#64 else u9.getReg r := by
    intro r; subst hu; simp [execInstrBr, getReg_setReg, se13, getReg_x0]
  have em11 : ∀ a, u11.getMem a = u9.getMem a := by intro a; subst hu; simp [execInstrBr]
  have ec11 : u11.code = u.code := by subst hu; simp [execInstrBr, ec9]
  clear hu
  have hne : ∀ i j, i < 6 → j < 6 → i ≠ j →
      sp - 0x30#64 + BitVec.ofNat 64 (8 * i) ≠ sp - 0x30#64 + BitVec.ofNat 64 (8 * j) :=
    fun i j hi hj h => cell6_ne hi hj h
  -- the epilogue: restore, close the frame, return
  apply SafeN.label hf2 (kd := .internal) (l := 62) (by decide)
  apply lsafe_opn hf2 hag11 (i := .LD .x1 .x2 0x028) (by decide) rfl
    (memOk_LD (by simpa [e11, e9, ld5] using dwordOk hfr' (i := 5) (by omega)))
  intro r12 m12 hag12
  apply SafeN.label hf2 (kd := .internal) (l := 63) (by decide)
  apply lsafe_opn hf2 hag12 (i := .LD .x8 .x2 0x020) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, e11, e9, ld4] using dwordOk hfr' (i := 4) (by omega)))
  intro r13 m13 hag13
  apply SafeN.label hf2 (kd := .internal) (l := 64) (by decide)
  apply lsafe_opn hf2 hag13 (i := .LD .x9 .x2 0x018) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, e11, e9, ld3] using dwordOk hfr' (i := 3) (by omega)))
  intro r14 m14 hag14
  apply SafeN.label hf2 (kd := .internal) (l := 65) (by decide)
  apply lsafe_opn hf2 hag14 (i := .LD .x18 .x2 0x010) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, e11, e9, ld2] using dwordOk hfr' (i := 2) (by omega)))
  intro r15 m15 hag15
  apply SafeN.label hf2 (kd := .internal) (l := 66) (by decide)
  apply lsafe_opn hf2 hag15 (i := .LD .x19 .x2 0x008) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, e11, e9, ld1] using dwordOk hfr' (i := 1) (by omega)))
  intro r16 m16 hag16
  apply SafeN.label hf2 (kd := .internal) (l := 67) (by decide)
  apply lsafe_opn hf2 hag16 (i := .LD .x20 .x2 0x000) (by decide) rfl
    (memOk_LD (by simpa [execInstrBr, getReg_setReg, e11, e9, ld0] using dwordOk hfr' (i := 0) (by omega)))
  intro r17 m17 hag17
  apply SafeN.label hf2 (kd := .internal) (l := 68) (by decide)
  apply lsafe_opn hf2 hag17 (i := .ADDI .x2 .x2 0x030) (by decide) rfl rfl
  intro r18 m18 hag18
  generalize hu : execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr
    (execInstrBr u11 (.LD .x1 .x2 0x028)) (.LD .x8 .x2 0x020)) (.LD .x9 .x2 0x018))
    (.LD .x18 .x2 0x010)) (.LD .x19 .x2 0x008)) (.LD .x20 .x2 0x000)) (.ADDI .x2 .x2 0x030) = u18
    at hag18
  have hnz : ∀ i j, i < 6 → j < 6 → i ≠ j →
      sp - 48#64 + BitVec.ofNat 64 (8 * i) ≠ sp - 48#64 + BitVec.ofNat 64 (8 * j) := hne
  have e18 : ∀ r, u18.getReg r = if r = .x2 then sp else if r = .x20 then u.getReg .x20
      else if r = .x19 then u.getReg .x19 else if r = .x18 then u.getReg .x18
      else if r = .x9 then u.getReg .x9 else if r = .x8 then u.getReg .x8
      else if r = .x1 then u.getReg .x1 else u11.getReg r := by
    intro r; subst hu
    have n50 := hnz 5 0 (by omega) (by omega) (by omega)
    have n51 := hnz 5 1 (by omega) (by omega) (by omega)
    have n52 := hnz 5 2 (by omega) (by omega) (by omega)
    have n53 := hnz 5 3 (by omega) (by omega) (by omega)
    have n54 := hnz 5 4 (by omega) (by omega) (by omega)
    have n40 := hnz 4 0 (by omega) (by omega) (by omega)
    have n41 := hnz 4 1 (by omega) (by omega) (by omega)
    have n42 := hnz 4 2 (by omega) (by omega) (by omega)
    have n43 := hnz 4 3 (by omega) (by omega) (by omega)
    have n30 := hnz 3 0 (by omega) (by omega) (by omega)
    have n31 := hnz 3 1 (by omega) (by omega) (by omega)
    have n32 := hnz 3 2 (by omega) (by omega) (by omega)
    have n20 := hnz 2 0 (by omega) (by omega) (by omega)
    have n21 := hnz 2 1 (by omega) (by omega) (by omega)
    have n10 := hnz 1 0 (by omega) (by omega) (by omega)
    simp only [Nat.reduceMul, BitVec.add_zero] at n50 n51 n52 n53 n54 n40 n41 n42 n43 n30 n31 n32 n20 n21 n10
    simp [execInstrBr, getReg_setReg, em11, em9, e11, e9, ld5, ld4, ld3, ld2, ld1, ld0, w_back,
      n50, n51, n52, n53, n54, n40, n41, n42, n43, n30, n31, n32, n20, n21, n10]
  have em18 : ∀ a, u18.getMem a = u9.getMem a := by intro a; subst hu; simp [execInstrBr, em11]
  have ec18 : u18.code = u.code := by subst hu; simp [execInstrBr, ec11]
  clear hu
  apply SafeN.label hf2 (kd := .internal) (l := 69) (by decide)
  refine lsafe_ret hf2 hag18 (by decide) (by rw [e18]; simpa using hra) (by rw [e18]; simp) (hpost _ _ ?_)
  refine ⟨fun r hr => ?_, ?_, fun a ha => ?_⟩
  · rw [hag18.regs, e18]
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [e11, e9, hsp]
  · rw [hag18.code, ec18]
  · have hnot := ha _ (List.mem_singleton_self _)
    rw [hag18.mem, em18, em9]
    have hc : ∀ i, i < 6 → a ≠ sp - 0x30#64 + BitVec.ofNat 64 (8 * i) :=
      fun i hi h => hnot (h ▸ inRegion_cell' hfr hi)
    have c0 := hc 0 (by omega); have c1 := hc 1 (by omega); have c2 := hc 2 (by omega)
    have c3 := hc 3 (by omega); have c4 := hc 4 (by omega); have c5 := hc 5 (by omega)
    simp only [Nat.reduceMul, BitVec.add_zero] at c0 c1 c2 c3 c4 c5
    simp [c0, c1, c2, c3, c4, c5]

theorem ScwRet.of_setReg {u v : MachineState} {sp : Word} {r : Reg} (hr : r ∉ calleeSavedRegs)
    {w : Word} (h : ScwRet (u.setReg r w) sp v) : ScwRet u sp v :=
  ⟨fun r' hr' => by
    rw [h.cs r' hr', getReg_setReg]
    have : r' ≠ r := fun e => hr (e ▸ hr')
    simp [this],
   h.code.trans (by cases r <;> rfl), fun a ha => (h.unch a ha).trans (by simp)⟩

/-! ## `sys_write`: a tail call of `syscall_write` -/

/-- The only function of the program at `syscall_write`'s address is `syscall_write`. -/
theorem at_scw {g : Nat} {fn : Fn} (hg : fs[g]? = some fn) (hb : fn.base = F_7801b3b0.base) :
    g = 2 ∧ fn = ⟨"syscall_write", F_7801b3b0.base, scwProg, 0x30⟩ := by
  match g, hg with
  | 0, h => simp only [fs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact absurd hb (by decide)
  | 1, h => simp only [fs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
            subst h; exact absurd hb (by decide)
  | 2, h => simp only [fs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
            exact ⟨rfl, h.symm⟩
  | _ + 3, h => simp [fs] at h

/-- The only function of the program at `sys_write`'s address is `sys_write`. -/
theorem at_sw {g : Nat} {fn : Fn} (hg : fs[g]? = some fn) (hb : fn.base = F_7801bfa4.base) :
    g = 1 ∧ fn = ⟨"sys_write", F_7801bfa4.base, swProg, 0⟩ := by
  match g, hg with
  | 0, h => simp only [fs, List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact absurd hb (by decide)
  | 1, h => simp only [fs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
            exact ⟨rfl, h.symm⟩
  | 2, h => simp only [fs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
            subst h; exact absurd hb (by decide)
  | _ + 3, h => simp [fs] at h

/-- **`sys_write`'s contract at Lprog**, to a descriptor other than 13: `syscall_write`'s. -/
theorem sw_contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {rv : Word}
    {rest : List Frame} (u : MachineState) (sp fd : Word) (regs : Reg → BitVec 64) (m : MachineState)
    (hag : Agree (ofParts regs m) u) (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi u)
    (hra : u.getReg .x1 = rv) (hsp : u.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (h10 : u.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (hpost : ∀ r' m', ScwRet u sp (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨1, 0, rv, sp⟩ :: rest, regs, m⟩ := by
  apply SafeN.label hf1 (kd := .internal) (l := 0) (by decide)
  apply lsafe_auipc hf1 hag (rd := .x6)
    (v := F_7801bfa4.base + BitVec.ofNat 64 (4 * 0) + auipcOff 0xfffff#20) (by decide)
  intro r1 m1 hag1
  apply SafeN.label hf1 (kd := .internal) (l := 1) (by decide)
  apply lsafe_tail hf1 hag1 (rs := .x6) (off := 0x40c) (by decide)
    (by simp [getReg_setReg, hsp]) (g := 2) (tf := ⟨"syscall_write", F_7801b3b0.base, scwProg, 0x30⟩) rfl
    (by rw [getReg_setReg, if_pos ⟨rfl, by decide⟩]; decide)
  intro g' fn' hg' hb
  obtain ⟨rfl, rfl⟩ := at_scw hg' hb
  exact scw_contract _ sp fd r1 m1 hag1 (cw_of_code hcw (by cases u; rfl))
    (by simp [getReg_setReg, hra]) (by simp [getReg_setReg, hsp]) hstk (by simp [getReg_setReg, h10]) hfd
    fun r' m' h => hpost r' m' (h.of_setReg (by decide))

/-! ## `write_vectored` -/

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

set_option maxHeartbeats 4000000 in
/-- **`write_vectored`'s contract at Lprog**, with the call of `sys_write` an Lprog call that
    uses `sys_write`'s contract. -/
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
  apply lsafe_auipc hf0 (Agree.refl _) (rd := .x1)
    (v := F_7803c684.base + BitVec.ofNat 64 (4 * 18) + auipcOff 0xfffe0#20) (by decide)
  intro rB mB hagB
  apply SafeN.label hf0 (kd := .internal) (l := 19) (by decide)
  apply lsafe_call hf0 hagB (ret := F_7803c684.base + BitVec.ofNat 64 (4 * 19) + 4) (rs := .x1)
    (off := 0x8d8) (by decide) (g := 1) (tf := ⟨"sys_write", F_7801bfa4.base, swProg, 0⟩) rfl
    (by rw [getReg_setReg, if_pos ⟨rfl, by decide⟩]; decide)
  intro g' fn' hg' hb rC mC hagC
  obtain ⟨rfl, rfl⟩ := at_sw hg' hb
  have hA : ∀ r, r ≠ .x1 →
      (((ofParts rA mA).setReg .x1 (F_7803c684.base + BitVec.ofNat 64 (4 * 18) + auipcOff 0xfffe0#20)).setReg
        .x1 (F_7803c684.base + BitVec.ofNat 64 (4 * 19) + 4)).getReg r = (ofParts rA mA).getReg r := by
    intro r hr; simp [getReg_setReg, hr]
  rw [show (((ofParts rA mA).setReg .x1 (F_7803c684.base + BitVec.ofNat 64 (4 * 18) + auipcOff 0xfffe0#20)).getReg
      .x2) = sp - 32#64 by simp [getReg_setReg, hat.x2]]
  refine sw_contract _ (sp - 32#64) 2#64 rC mC hagC
    (cw_of_code hcw (by simpa using hat.saved.code))
    (by simp [getReg_setReg]) (by simp [getReg_setReg, hat.x2]) (stack_sub hstk)
    (by simp [getReg_setReg, hat.x10]) (by decide) ?_
  intro rD mD hret
  -- back from the call
  have hs : Saved s0 sp (ofParts rD mD) :=
    saved_after_call hfr hat.saved (fun r hr => by simp [getReg_setReg, hr]) (fun a => by simp)
      (by simp) hret
  exact fromCall s0 sp xs hfr rD mD (ofParts rD mD) (Agree.refl _)
    (by rw [hret.cs .x2 (by decide)]; simp [getReg_setReg, hat.x2])
    (by rw [hret.cs .x9 (by decide)]; simp [getReg_setReg, hat.x9]) hs hrv htop hdone

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
  refine SafeN.of_contract hok (g := 0) (fn := ⟨"write_vectored", F_7803c684.base, prog, 0x20⟩) rfl
    (by rw [hpc]; rfl) ?_ (Post := Done s sp xs)
    (fun _ _ hpost => contract s sp bufs xs cnt hxl hokx hstk hcw hdis _ _ (agree_ofParts_regsOf s)
      hsp hb hc hx rfl hsp.symm hpost) ?_
  · intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact prog_map ▸ hcode
    · exact swProg_map ▸ hcodeS
    · exact scwProg_map ▸ hcodeW
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

end Cases.Zip2005.WriteVectored
