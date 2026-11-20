/-
  Examples.BranchesO0.RiscV.Proofs

  The functions of `Examples/src/c/branches_o0.c` (the same source as `branches.c`), compiled by
  clang at `-O0` to `Examples/elf/branches_o0.elf`. Every function sets up a frame (`ra` and `s0`
  saved, `s0` the frame pointer) and keeps every argument and local in it: each value goes
  through a store and a load. The specifications are those of `Examples.Branches.RiscV`
  (`smax`, `clampSpec`, `countDown` in `Examples/Spec.lean`, `sumMem` in `Examples/Kit.lean`).

  * `add3`, `max2` (signed), `umax2`, `clamp`: as at `-O2`.
  * `sum(p, n)`: the wrapping sum of the `n` longs from `p`. At `-O0` the loop counts `i` up to
    `n` and reads `p[i]` at `p + 8 * i`, so no bound on `n` is needed; it asks instead that the
    array be outside the frame, since a store to a local would change it.
  * `count_down(n)`: `countDown`, the C loop itself, by induction on the halvings left.

  Each contract keeps every register but `a0` (and `a1` where the code uses it), with `ra`, `s0`
  and `sp` restored by the epilogue, and every doubleword of memory outside the frame (`Kept`).
  The loops' lemmas carry the frame's slots as hypotheses at the loop's head (`sum_loop`,
  `count_down_loop`). `_start` is an endless loop and has no contract.
-/

import Examples.BranchesO0.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.BranchesO0.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.BranchesO0.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-! ## `countDown`, a halving at a time -/

/-- A word that is not zero takes a halving. -/
theorem countDown_ne_zero {v : Word} (h : ¬v = 0#64) : countDown v.toNat ≠ 0 := by
  rw [countDown]; have : v.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  simp [this]

/-- One halving of a word that is not zero. -/
theorem countDown_shr {v : Word} (h : ¬v = 0#64) :
    countDown v.toNat = countDown (v >>> 1).toNat + 1 := by
  rw [countDown]; have : v.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  simp [this, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## The stack frame -/

/-- Every doubleword outside the `n` bytes below `top` reads in `m` as in `m0`. -/
def Kept (n top : Word) (m0 m : MachineState) : Prop :=
  ∀ c, n ≤ c - (top - n) → m.getMem c = m0.getMem c

/-- The three registers the epilogue restores, and the rest. -/
theorem reg_cases (r : Reg) : r = .x1 ∨ r = .x2 ∨ r = .x8 ∨ (r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x8) := by
  cases r <;> simp

/-- Memory kept by doing nothing. -/
theorem Kept.refl (n top : Word) (m : MachineState) : Kept n top m m := fun _ _ => rfl

/-- A store at `top + k`, inside the `n` bytes below `top`, keeps what `Kept` asks. -/
theorem Kept.setMem {n top k v : Word} {m0 m : MachineState} (hk : k + n < n)
    (h : Kept n top m0 m) : Kept n top m0 (m.setMem (top + k) v) := by
  intro c hc
  rw [getMem_setMem, ite_eq_right (by bv_omega)]
  exact h c hc


/-- `add3(a, b, c)`: the sum. Every register but `a0`, `a1` is kept (`ra`, `s0`, `sp` restored), and every doubleword of memory outside the 48-byte frame. -/
theorem add3_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 ∧
      (∀ r, r ∉ [Reg.x10, .x11] → r' r = regs r) ∧ Kept 48#64 top m m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  all_goals
    refine hk _ _ ⟨?_, fun r h => ?_, ?_⟩
    · simp only [lsym_simp]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8⟩ <;> simp_all [lsym_simp]
    · repeat apply Kept.setMem (by decide)
      exact Kept.refl _ _ _

/-- **`add3` on the machine.** -/
theorem add3_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 →
      (∀ c, 48#64 ≤ c - (s.getReg .x2 - 48#64) → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode add3_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, hm⟩
  refine hk t hpc' ?_ fun c hc => (hag.mem c).symm.trans (hm c hc)
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `max2(a, b)`: the greater, signed. Every register but `a0`, `a1` is kept, and every doubleword of memory outside the 48-byte frame. -/
theorem max2_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = smax (regs .x10) (regs .x11) ∧
      (∀ r, r ∉ [Reg.x10, .x11] → r' r = regs r) ∧ Kept 48#64 top m m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp]
  all_goals
    refine hk _ _ ⟨?_, fun r h => ?_, ?_⟩
    · simp [lsym_simp, smax, hc]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8⟩ <;> simp_all [lsym_simp]
    · repeat apply Kept.setMem (by decide)
      exact Kept.refl _ _ _

/-- **`max2` on the machine.** -/
theorem max2_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1040#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = smax (s.getReg .x10) (s.getReg .x11) →
      (∀ c, 48#64 ≤ c - (s.getReg .x2 - 48#64) → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x1040#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode max2_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, hm⟩
  refine hk t hpc' ?_ fun c hc => (hag.mem c).symm.trans (hm c hc)
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `umax2(a, b)`: the greater, unsigned. Every register but `a0`, `a1` is kept, and every doubleword of memory outside the 48-byte frame. -/
theorem umax2_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = umax (regs .x10) (regs .x11) ∧
      (∀ r, r ∉ [Reg.x10, .x11] → r' r = regs r) ∧ Kept 48#64 top m m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq with [hra, hsp]
  all_goals
    refine hk _ _ ⟨?_, fun r h => ?_, ?_⟩
    · simp only [lsym_simp, umax]; bv_decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8⟩ <;> simp_all [lsym_simp]
    · repeat apply Kept.setMem (by decide)
      exact Kept.refl _ _ _

/-- **`umax2` on the machine.** -/
theorem umax2_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1094#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = umax (s.getReg .x10) (s.getReg .x11) →
      (∀ c, 48#64 ≤ c - (s.getReg .x2 - 48#64) → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x1094#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode umax2_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, hm⟩
  refine hk t hpc' ?_ fun c hc => (hag.mem c).symm.trans (hm c hc)
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `clamp(x, lo, hi)`: `x < lo ? lo : (x > hi ? hi : x)`, signed, for any `lo` and `hi`. Every register but `a0`, `a1` is kept, and every doubleword of memory outside the 64-byte frame. -/
theorem clamp_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = clampSpec (regs .x10) (regs .x11) (regs .x12) ∧
      (∀ r, r ∉ [Reg.x10, .x11] → r' r = regs r) ∧ Kept 64#64 top m m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f3_eq with [hra, hsp]
  all_goals
    refine hk _ _ ⟨?_, fun r h => ?_, ?_⟩
    · simp only [lsym_simp, clampSpec]; bv_decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8⟩ <;> simp_all [lsym_simp]
    · repeat apply Kept.setMem (by decide)
      exact Kept.refl _ _ _

/-- **`clamp` on the machine.** -/
theorem clamp_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10e8#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = clampSpec (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) →
      (∀ c, 64#64 ≤ c - (s.getReg .x2 - 64#64) → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[3]? = some fn ∧ fn.base = 0x10e8#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode clamp_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, hm⟩
  refine hk t hpc' ?_ fun c hc => (hag.mem c).symm.trans (hm c hc)
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## `count_down` -/

/-- **The loop of `count_down`**, at its head: `n` is `v` and `k` is `c` in the frame, and
    `c` and the halvings left of `v` make up the halvings of `x`. By induction on those left. -/
theorem count_down_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m0 : MachineState) (R : Reg → Word) (x : Word)
    (hr1 : R .x1 = ret) (hr2 : R .x2 = top)
    (hpost : ∀ r' m', r' .x10 = BitVec.ofNat 64 (countDown x.toNat) →
      (∀ r, r ∉ [Reg.x10] → r' r = R r) → Kept 32#64 top m0 m' → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ f (v c : Word) (regs : Reg → Word) (m : MachineState), countDown v.toNat = f →
      c + BitVec.ofNat 64 f = BitVec.ofNat 64 (countDown x.toNat) →
      regs .x2 = top + 18446744073709551584#64 → regs .x8 = top →
      (∀ r, r ∉ [Reg.x2, .x8, .x10] → regs r = R r) →
      m.getMem (top + 18446744073709551608#64) = ret →
      m.getMem (top + 18446744073709551600#64) = R .x8 →
      m.getMem (top + 18446744073709551592#64) = v →
      m.getMem (top + 18446744073709551584#64) = c → Kept 32#64 top m0 m →
      LSafeN fns G N Q ⟨⟨5, 16, ret, top⟩ :: rest, regs, m⟩ := by
  intro f
  induction f with
  | zero =>
    intro v c regs m hf hc0 hsp h8 hR hm1 hm2 hm3 hm4 hK
    lsym f5_eq stop [16] with [hsp, h8, hm1, hm2, hm3, hm4]
    · refine hpost _ _ ?_ (fun r h => ?_) hK
      · simp only [lsym_simp]; simpa using hc0
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8'⟩ <;> simp_all [lsym_simp]
    · exact absurd hf (countDown_ne_zero hc)
  | succ f ih =>
    intro v c regs m hf hc0 hsp h8 hR hm1 hm2 hm3 hm4 hK
    lsym f5_eq stop [16] with [hsp, h8, hm1, hm2, hm3, hm4]
    · subst hc; simp [countDown] at hf
    · rw [countDown_shr hc] at hf
      refine ih (v >>> 1) (c + 1#64) _ _ (by omega) ?_ (by simp [lsym_simp, hsp])
        (by simp [lsym_simp, h8]) (fun r h => ?_) ?_ ?_ ?_ ?_
        (Kept.setMem (by decide) (Kept.setMem (by decide) hK))
      · rw [← hc0, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (1#64)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
        simp [lsym_simp, h, hR r (by simp [h])]
      all_goals simp [hm1, hm2]

/-- `count_down(n)`: the number of halvings that take `n` to zero (its bit length). Every
    register but `a0` is kept, and every doubleword of memory outside the 32-byte frame. -/
theorem count_down_contract : rvIsa.Contract (liftProg fns) sp1Ctx 5
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = BitVec.ofNat 64 (countDown (regs .x10).toNat) ∧
      (∀ r, r ∉ [Reg.x10] → r' r = regs r) ∧ Kept 32#64 top m m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f5_eq stop [16] with [hra, hsp]
  refine count_down_loop m regs (regs .x10) hra hsp (fun r' m' h1 h2 h3 => hk r' m' ⟨h1, h2, h3⟩)
    _ (regs .x10) 0#64 _ _ rfl (by simp) (by simp [lsym_simp]) (by simp [lsym_simp]) (fun r h => ?_)
    (by simp) (by simp) (by simp) (by simp)
    (Kept.setMem (by decide) (Kept.setMem (by decide) (Kept.setMem (by decide)
      (Kept.setMem (by decide) (Kept.refl _ _ _)))))
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8⟩ <;> simp_all [lsym_simp]

/-- **`count_down` on the machine.** -/
theorem count_down_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x11e8#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (countDown (s.getReg .x10).toNat) →
      (∀ c, 32#64 ≤ c - (s.getReg .x2 - 32#64) → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[5]? = some fn ∧ fn.base = 0x11e8#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode count_down_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, hm⟩
  refine hk t hpc' ?_ fun c hc => (hag.mem c).symm.trans (hm c hc)
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## `sum` -/

/-- The loop's exit: `i` has reached `n`. -/
theorem sum_exit {j : Nat} {n : Word} (hj : j ≤ n.toNat) (hc : n ≤ BitVec.ofNat 64 j) :
    j = n.toNat := by bv_omega

/-- The return of `sum`, with the `n` longs summed. -/
theorem sum_ret {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {m0 m : MachineState} {R regs : Reg → Word} {p n : Word}
    (hpost : ∀ r' m', r' .x10 = sumMem m0 p n.toNat →
      (∀ r, r ∉ [Reg.x10, .x11] → r' r = R r) → Kept 48#64 top m0 m' →
      LSafeN fns G N Q ⟨rest, r', m'⟩) (hr1 : R .x1 = ret) (hr2 : R .x2 = top)
    (hR : ∀ r, r ∉ [Reg.x2, .x8, .x10, .x11] → regs r = R r) (hK : Kept 48#64 top m0 m) (a b : Word) :
    LSafeN fns G N Q ⟨rest, updReg (updReg (updReg (updReg (updReg (updReg regs .x10 a) .x11 b)
      .x10 (sumMem m0 p n.toNat)) .x1 ret) .x8 (R .x8)) .x2 top, m⟩ := by
  refine hpost _ _ (by simp [lsym_simp]) (fun r h => ?_) hK
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8⟩ <;> simp_all [lsym_simp]

/-- **The loop of `sum`**, at its head: `p`, `n`, `s` and `i` in the frame, with `i = j` and the
    first `j` longs summed. By induction on those left. -/
theorem sum_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m0 : MachineState) (R : Reg → Word) (p n : Word)
    (hr1 : R .x1 = ret) (hr2 : R .x2 = top)
    (hout : ∀ i < n.toNat, 48#64 ≤ p + BitVec.ofNat 64 (8 * i) - (top - 48#64))
    (hpost : ∀ r' m', r' .x10 = sumMem m0 p n.toNat →
      (∀ r, r ∉ [Reg.x10, .x11] → r' r = R r) → Kept 48#64 top m0 m' →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → Word) (m : MachineState), n.toNat - j = k → j ≤ n.toNat →
      regs .x2 = top + 18446744073709551568#64 → regs .x8 = top →
      (∀ r, r ∉ [Reg.x2, .x8, .x10, .x11] → regs r = R r) →
      m.getMem (top + 18446744073709551608#64) = ret →
      m.getMem (top + 18446744073709551600#64) = R .x8 →
      m.getMem (top + 18446744073709551592#64) = p →
      m.getMem (top + 18446744073709551584#64) = n →
      m.getMem (top + 18446744073709551576#64) = sumMem m0 p j →
      m.getMem (top + 18446744073709551568#64) = BitVec.ofNat 64 j → Kept 48#64 top m0 m →
      LSafeN fns G N Q ⟨⟨4, 20, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro j regs m hk hj hsp h8 hR hm1 hm2 hm3 hm4 hm5 hm6 hK
    lsym f4_eq stop [20] with [hsp, h8, hm1, hm2, hm3, hm4, hm5, hm6]
    · obtain rfl : j = n.toNat := sum_exit hj hc
      exact sum_ret hpost hr1 hr2 hR hK _ _
    · exact absurd hc (by bv_omega)
  | succ k ih =>
    intro j regs m hk hj hsp h8 hR hm1 hm2 hm3 hm4 hm5 hm6 hK
    have hjn : j < n.toNat := by omega
    have hread : m.getMem (p + BitVec.ofNat 64 (8 * j)) = m0.getMem (p + BitVec.ofNat 64 (8 * j)) :=
      hK _ (hout j hjn)
    lsym f4_eq stop [20] with [hsp, h8, hm1, hm2, hm3, hm4, hm5, hm6, hread]
    · exact absurd (sum_exit hj hc) (by omega)
    · refine ih (j + 1) _ _ (by omega) (by omega) (by simp [lsym_simp, hsp])
        (by simp [lsym_simp, h8]) (fun r h => ?_) (by simp [hm1]) (by simp [hm2]) (by simp [hm3])
        (by simp [hm4]) (by simp [sumMem]) (by simp [ofNat_succ])
        (Kept.setMem (by decide) (Kept.setMem (by decide) hK))
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      simp [lsym_simp, h, hR r (by simp [h])]

/-- `sum(p, n)`: the wrapping sum of the `n` longs from `p`, for any `n`, when none of them is in
    the 48-byte frame (the array is an object of its own, not the function's locals). Every
    register but `a0`, `a1` is kept, and every doubleword of memory outside the frame. -/
theorem sum_contract : rvIsa.Contract (liftProg fns) sp1Ctx 4
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧
      ∀ i < (regs .x11).toNat, 48#64 ≤ regs .x10 + BitVec.ofNat 64 (8 * i) - (top - 48#64))
    (fun _ top regs m r' m' => r' .x10 = sumMem m (regs .x10) (regs .x11).toNat ∧
      (∀ r, r ∉ [Reg.x10, .x11] → r' r = regs r) ∧ Kept 48#64 top m m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hout⟩ hk
  lsym f4_eq stop [20] with [hra, hsp]
  refine sum_loop m regs (regs .x10) (regs .x11) hra hsp hout
    (fun r' m' h1 h2 h3 => hk r' m' ⟨h1, h2, h3⟩) _ 0 _ _ rfl (Nat.zero_le _)
    (by simp [lsym_simp]) (by simp [lsym_simp]) (fun r h => ?_)
    (by simp) (by simp) (by simp) (by simp) (by simp [sumMem]) (by simp)
    (Kept.setMem (by decide) (Kept.setMem (by decide) (Kept.setMem (by decide)
      (Kept.setMem (by decide) (Kept.setMem (by decide) (Kept.setMem (by decide)
        (Kept.refl _ _ _)))))))
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  rcases reg_cases r with rfl | rfl | rfl | ⟨h1, h2, h8⟩ <;> simp_all [lsym_simp]

/-- **`sum` on the machine.** -/
theorem sum_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1168#64) (hcode : Loaded fns s)
    (hout : ∀ i < (s.getReg .x11).toNat,
      48#64 ≤ s.getReg .x10 + BitVec.ofNat 64 (8 * i) - (s.getReg .x2 - 48#64))
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = sumMem s (s.getReg .x10) (s.getReg .x11).toNat →
      (∀ c, 48#64 ≤ c - (s.getReg .x2 - 48#64) → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[4]? = some fn ∧ fn.base = 0x1168#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sum_contract
    ⟨rfl, rfl, by simpa [regsOf] using hout⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, hm⟩
  refine hk t hpc' ?_ fun c hc => (hag.mem c).symm.trans (hm c (by simpa [regsOf] using hc))
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

end Examples.BranchesO0.RiscV
