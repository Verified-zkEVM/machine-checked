/-
  Cases.Zip2005.Runtime.MemcmpLprog

  `memcmp(a, b, n)` proved at Lprog, for every length `n`, and carried down to `stepSp1`.

  The function's twelve instructions are lifted to an Lprog body (`lift`), and the body is run
  at Lprog: the byte loop by induction on the bytes left (`loop`), the entry and the empty
  case on top (`halts`). `reach_of_halts` turns the run into one over `stepSp1`, so `safe` is a
  specification over the machine with nothing symbolic left in its proof: the result is zero
  exactly when the `n` bytes at `a` and at `b` agree, memory and code are untouched, and every
  register but `x10`..`x14` keeps its value.

  `Memcmp.lean` proves the same function by symbolic execution, for blocks of 32 and 64
  bytes.
-/

import MachineChecked.RiscV.Lprog.Lift
import Cases.Zip2005.Image.F_7803f54c

namespace Cases.Zip2005

open RiscvZkvm.Rv64

theorem zeroExtend_byte_inj (x y : BitVec 8) (h : BitVec.zeroExtend 64 x = BitVec.zeroExtend 64 y) :
    x = y := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have hx := x.isLt; have hy := y.isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem sext32_sub_bytes (x y : BitVec 8) :
    BitVec.signExtend 64 ((BitVec.zeroExtend 64 x + -BitVec.zeroExtend 64 y).truncate 32) =
      BitVec.zeroExtend 64 x + -BitVec.zeroExtend 64 y := by
  rw [← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · have e : (2 ^ 64 - y.toNat % 2 ^ 64 + x.toNat % 2 ^ 64) % 2 ^ 64 = x.toNat - y.toNat := by omega
    simp only [e, decide_eq_true_eq]
    split <;> omega
  · have e : (2 ^ 64 - y.toNat % 2 ^ 64 + x.toNat % 2 ^ 64) % 2 ^ 64 =
        2 ^ 64 - (y.toNat - x.toNat) := by omega
    simp only [e, decide_eq_true_eq]
    split <;> omega

end Cases.Zip2005

namespace Cases.Zip2005.MemcmpLprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog MachineChecked.RiscV.Lprog Cases.Zip2005.Image

/-- The instructions of `memcmp`. -/
def prog : List Instr := F_7803f54c.prog.filterMap id

theorem prog_map : prog.map some = F_7803f54c.prog := by decide

theorem wf : WF prog := by unfold WF; decide

/-- The registers `memcmp` may change. -/
def clobbered : List Reg := [.x10, .x11, .x12, .x13, .x14]

/-- The end of a run of `memcmp` from a machine state `u0`, as an Lprog state. -/
def Post (u0 : MachineState) (a b : Word) (n : Nat) (s : State rvIsa) : Prop :=
  s.pc = 2 * prog.length + 1 ∧
  ((ofParts s.regs s.m).getReg .x10 = 0 ↔
    ∀ i < n, u0.getByte (a + BitVec.ofNat 64 i) = u0.getByte (b + BitVec.ofNat 64 i)) ∧
  (∀ addr, s.m.getMem addr = u0.getMem addr) ∧ s.m.code = u0.code ∧
  (∀ r, r ∉ clobbered → (ofParts s.regs s.m).getReg r = u0.getReg r) ∧
  BitVec.signExtend 64 (((ofParts s.regs s.m).getReg .x10).truncate 32) = (ofParts s.regs s.m).getReg .x10

theorem ofNat_eq_zero {x : Nat} (hx : x < 2 ^ 64) (h : BitVec.ofNat 64 x = 0#64) : x = 0 := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this

theorem ofNat_add_neg_one {x : Nat} (h : 0 < x) :
    BitVec.ofNat 64 x + 18446744073709551615#64 = BitVec.ofNat 64 (x - 1) := by
  have e : (18446744073709551615#64 : Word) = -1#64 := by decide
  rw [e, ← BitVec.sub_eq_add_neg, show x = (x - 1) + 1 by omega, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

set_option maxHeartbeats 4000000 in
/-- **The byte loop**, from byte `j < n`, at the loop head. -/
theorem loop (u0 : MachineState) (a b : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true) :
    ∀ k j (regs : String → BitVec 64) (m u : MachineState), n - j = k → j < n →
      Agree (ofParts regs m) u →
      u.getReg .x10 = a + BitVec.ofNat 64 j → u.getReg .x11 = b + BitVec.ofNat 64 j →
      u.getReg .x12 = BitVec.ofNat 64 (n - j) →
      (∀ addr, u.getMem addr = u0.getMem addr) → u.code = u0.code →
      (∀ r, r ∉ clobbered → u.getReg r = u0.getReg r) →
      (∀ i < j, u0.getByte (a + BitVec.ofNat 64 i) = u0.getByte (b + BitVec.ofNat 64 i)) →
      rvIsa.Halts (lift prog) (Post u0 a b n) ⟨2, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ _ hk hj; omega
  | succ k ih =>
    intro j regs m u hk hj hag h10 h11 h12 hmem hcode hkept hbytes
    apply reaches_label (kd := .internal) (l := 1) (by decide)
    apply reaches_opn hag (i := .LBU .x13 .x10 0) (by decide) rfl
      (by simp [memOkSp1, memAccess, h10, signExtend12, hva j hj, alignedFor])
    intro r1 m1 hag1
    apply reaches_label (kd := .internal) (l := 2) (by decide)
    apply reaches_opn hag1 (i := .LBU .x14 .x11 0) (by decide) rfl
      (by simp [memOkSp1, memAccess, h11, signExtend12, hvb j hj, alignedFor, execInstrBr,
        getReg_setReg])
    intro r2 m2 hag2
    -- the two bytes are loaded
    generalize hu2 : execInstrBr (execInstrBr u (.LBU .x13 .x10 0)) (.LBU .x14 .x11 0) = u2 at hag2
    have e : ∀ r, u2.getReg r = if r = .x14 then (u0.getByte (b + BitVec.ofNat 64 j)).zeroExtend 64
        else if r = .x13 then (u0.getByte (a + BitVec.ofNat 64 j)).zeroExtend 64 else u.getReg r := by
      intro r; subst hu2
      simp [execInstrBr, getReg_setReg, MachineState.getByte, h10, h11, hmem, signExtend12]
    have em : ∀ addr, u2.getMem addr = u0.getMem addr := by
      intro addr; subst hu2; simp [execInstrBr, hmem]
    have ec : u2.code = u0.code := by subst hu2; simp [execInstrBr, hcode]
    clear hu2
    apply reaches_label (kd := .internal) (l := 3) (by decide)
    have hbj : j < n := hj
    apply reaches_cond hag2 (op := "ne") (a := .x13) (b := .x14) (l := 10) (by decide)
      (c := u2.getReg .x13 != u2.getReg .x14) (by simp [cmpEval]) (j := 20) (by decide)
    · -- the bytes differ: the result is their difference
      intro hne
      apply reaches_label (kd := .internal) (l := 10) (by decide)
      apply reaches_opn hag2 (i := .SUB .x10 .x13 .x14) (by decide) rfl rfl
      intro r3 m3 hag3
      apply reaches_label (kd := .internal) (l := 11) (by decide)
      apply halts_ret (by decide)
      simp only [Post]
      refine ⟨by decide, ?_, fun addr => ?_, ?_, fun r hr => ?_, ?_⟩
      · rw [hag3.regs]
        simp only [e, if_true, bne_iff_ne, ne_eq, reduceCtorEq, if_false] at hne
        simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg, e, reduceCtorEq,
          if_true, if_false, and_self, ne_eq, not_false_eq_true]
        constructor
        · intro h; exact absurd (by bv_omega) hne
        · intro h; exact absurd (congrArg _ (h j hj)) hne
      · exact (hag3.mem addr).trans ((by simp [execInstrBr, em]))
      · exact hag3.code.trans (by simp [execInstrBr, ec])
      · rw [hag3.regs]
        simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h0, h1, h2, h3, h4⟩ := hr
        simp [execInstrBr, getReg_setReg, e, h0, h3, h4]
        exact hkept r (by simp [clobbered, h0, h1, h2, h3, h4])
      · rw [hag3.regs]
        simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg, e, reduceCtorEq,
          if_true, if_false, and_self, ne_eq, not_false_eq_true]
        rw [BitVec.sub_eq_add_neg]
        exact sext32_sub_bytes _ _
    · -- the bytes agree: step the pointers and the count
      intro heq
      have hbyte : u0.getByte (a + BitVec.ofNat 64 j) = u0.getByte (b + BitVec.ofNat 64 j) := by
        simp only [e, if_true, bne_eq_false_iff_eq, reduceCtorEq, if_false] at heq
        exact zeroExtend_byte_inj _ _ heq
      apply reaches_label (kd := .internal) (l := 4) (by decide)
      apply reaches_opn hag2 (i := .ADDI .x11 .x11 1) (by decide) rfl rfl
      intro r3 m3 hag3
      apply reaches_label (kd := .internal) (l := 5) (by decide)
      apply reaches_opn hag3 (i := .ADDI .x12 .x12 0xfff) (by decide) rfl rfl
      intro r4 m4 hag4
      apply reaches_label (kd := .internal) (l := 6) (by decide)
      apply reaches_opn hag4 (i := .ADDI .x10 .x10 1) (by decide) rfl rfl
      intro r5 m5 hag5
      generalize hu5 : execInstrBr (execInstrBr (execInstrBr u2 (.ADDI .x11 .x11 1))
        (.ADDI .x12 .x12 0xfff)) (.ADDI .x10 .x10 1) = u5 at hag5
      have e5 : ∀ r, u5.getReg r = if r = .x10 then a + BitVec.ofNat 64 (j + 1)
          else if r = .x12 then BitVec.ofNat 64 (n - (j + 1))
          else if r = .x11 then b + BitVec.ofNat 64 (j + 1) else u2.getReg r := by
        have hinc : ∀ x : Word, x + BitVec.ofNat 64 j + 1#64 = x + BitVec.ofNat 64 (j + 1) := by
          intro x; rw [BitVec.add_assoc]; congr 1
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have hdec : BitVec.ofNat 64 (n - j) + 18446744073709551615#64 = BitVec.ofNat 64 (n - (j + 1)) := by
          rw [ofNat_add_neg_one (by omega), show n - j - 1 = n - (j + 1) by omega]
        intro r; subst hu5
        simp [execInstrBr, getReg_setReg, e, h10, h11, h12, signExtend12, hinc, hdec]
      have em5 : ∀ addr, u5.getMem addr = u0.getMem addr := by
        intro addr; subst hu5; simp [execInstrBr, em]
      have ec5 : u5.code = u0.code := by subst hu5; simp [execInstrBr, ec]
      clear hu5
      have kept5 : ∀ r, r ∉ clobbered → u5.getReg r = u0.getReg r := by
        intro r hr
        have hr' := hr
        simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        obtain ⟨h0, h1, h2, h3, h4⟩ := hr'
        rw [e5, e]
        simp only [h0, h1, h2, h3, h4, if_false]
        exact hkept r hr
      apply reaches_label (kd := .internal) (l := 7) (by decide)
      apply reaches_cond hag5 (op := "ne") (a := .x12) (b := .x0) (l := 1) (by decide)
        (c := u5.getReg .x12 != u5.getReg .x0) (by simp [cmpEval]) (j := 2) (by decide)
      · -- the back edge: one more byte agrees
        intro hc
        have hlt : j + 1 < n := by
          rcases Nat.lt_or_ge (j + 1) n with h | hge
          · exact h
          · simp [e5, getReg_x0, show n - (j + 1) = 0 by omega] at hc
        exact ih (j + 1) r5 m5 u5 (by omega) hlt hag5 (by simp [e5]) (by simp [e5]) (by simp [e5])
          em5 ec5 kept5 (fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
            · exact hbytes i h
            · exact hbyte)
      · -- the last byte agrees: the blocks are equal
        intro hc
        have hz : n - (j + 1) = 0 := by
          simp only [e5, reduceCtorEq, if_false, if_true, getReg_x0, bne_eq_false_iff_eq] at hc
          exact ofNat_eq_zero (by omega) hc
        apply reaches_label (kd := .internal) (l := 8) (by decide)
        apply reaches_opn hag5 (i := .ADDI .x10 .x0 0) (by decide) rfl rfl
        intro r6 m6 hag6
        apply reaches_label (kd := .internal) (l := 9) (by decide)
        apply halts_ret (by decide)
        simp only [Post]
        refine ⟨by decide, ?_, fun addr => ?_, ?_, fun r hr => ?_, ?_⟩
        · rw [hag6.regs]
          simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg, reduceCtorEq,
            if_true, and_self, ne_eq, not_false_eq_true, getReg_x0]
          refine ⟨fun _ i hi => ?_, fun _ => by simp [signExtend12]⟩
          rcases Nat.lt_or_ge i j with h | h
          · exact hbytes i h
          · obtain rfl : i = j := by omega
            exact hbyte
        · exact (hag6.mem addr).trans (by simp [execInstrBr, em5])
        · exact hag6.code.trans (by simp [execInstrBr, ec5])
        · rw [hag6.regs]
          have h0 : r ≠ Reg.x10 := fun h => hr (by simp [clobbered, h])
          simp [execInstrBr, getReg_setReg, h0]
          exact kept5 r hr
        · rw [hag6.regs]
          simp [execInstrBr, getReg_setReg, getReg_x0, signExtend12]

/-- **`memcmp` at Lprog**: from the entry, the run halts at the return, in a state `Post` describes. -/
theorem halts (u0 : MachineState) (a b : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (regs : String → BitVec 64) (m : MachineState) (hag : Agree (ofParts regs m) u0)
    (h10 : u0.getReg .x10 = a) (h11 : u0.getReg .x11 = b) (h12 : u0.getReg .x12 = BitVec.ofNat 64 n) :
    rvIsa.Halts (lift prog) (Post u0 a b n) ⟨0, regs, m⟩ := by
  apply reaches_label (kd := .internal) (l := 0) (by decide)
  apply reaches_cond hag (op := "eq") (a := .x12) (b := .x0) (l := 8) (by decide)
    (c := u0.getReg .x12 == u0.getReg .x0) (by simp [cmpEval]) (j := 16) (by decide)
  · -- no bytes: the result is zero
    intro hc
    have hz : n = 0 := by
      simp only [h12, getReg_x0, beq_iff_eq] at hc
      exact ofNat_eq_zero hn hc
    subst hz
    apply reaches_label (kd := .internal) (l := 8) (by decide)
    apply reaches_opn hag (i := .ADDI .x10 .x0 0) (by decide) rfl rfl
    intro r1 m1 hag1
    apply reaches_label (kd := .internal) (l := 9) (by decide)
    apply halts_ret (by decide)
    simp only [Post]
    refine ⟨by decide, ?_, fun addr => ?_, ?_, fun r hr => ?_, ?_⟩
    · rw [hag1.regs]
      simp [execInstrBr, getReg_setReg, getReg_x0, signExtend12]
    · exact hag1.mem addr
    · exact hag1.code
    · rw [hag1.regs]
      have h0 : r ≠ Reg.x10 := fun h => hr (by simp [clobbered, h])
      simp [execInstrBr, getReg_setReg, h0]
    · rw [hag1.regs]
      simp [execInstrBr, getReg_setReg, getReg_x0, signExtend12]
  · -- some bytes: the loop
    intro hc
    have hpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [h12, getReg_x0] at hc
      · exact h
    exact loop u0 a b n hn hva hvb n 0 regs m u0 (by omega) hpos hag (by simp [h10])
      (by simp [h11]) (by simp [h12]) (fun _ => rfl) rfl (fun _ _ => rfl)
      (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- **`memcmp(a, b, n)` over `stepSp1`**, for every length: it returns to `ra` with zero in `x10`
    exactly when the `n` bytes at `a` and at `b` agree (and sign-extended from 32 bits, as an
    `int`), memory and code untouched, and every register but `x10`..`x14` as it was. -/
theorem safe {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState) (ra a b : Word)
    (n : Nat) (hn : n < 2 ^ 64)
    (hpc : s.pc = F_7803f54c.base) (hcode : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hra : s.getReg .x1 = ra) (h10 : s.getReg .x10 = a) (h11 : s.getReg .x11 = b)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (hk : ∀ t, t.pc = ra &&& ~~~1#64 → t.code = s.code → (∀ addr, t.getMem addr = s.getMem addr) →
      (∀ r, r ∉ clobbered → t.getReg r = s.getReg r) →
      (t.getReg .x10 = 0 ↔
        ∀ i < n, s.getByte (a + BitVec.ofNat 64 i) = s.getByte (b + BitVec.ofNat 64 i)) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 →
      SafeN G k P t) :
    SafeN G k P s := by
  have hc : CodeAt F_7803f54c.base (prog.map some) s := prog_map ▸ hcode
  refine SafeN.of_reaches (reach_of_halts wf (sim_entry (fun _ => 0) hc hpc)
    (halts s a b n hn hva hvb _ _ (agree_ofParts_regsOf _ s) h10 h11 h12)) ?_
  rintro t ⟨s', hs', hpc', hx10, hmem, hcode', hkept, hsx⟩
  apply hk
  · rcases hs'.pc with ⟨hle, _⟩ | ⟨_, ht⟩
    · rw [hpc'] at hle; omega
    · rw [ht, ← hs'.agree.regs .x1, hkept .x1 (by decide), hra]
  · rw [← hs'.agree.code]; exact hcode'
  · intro addr; rw [← hs'.agree.mem addr]; exact hmem addr
  · intro r hr; rw [← hs'.agree.regs r]; exact hkept r hr
  · rw [← hs'.agree.regs]; exact hx10
  · rw [← hs'.agree.regs]; exact hsx

end Cases.Zip2005.MemcmpLprog
