/-
  Examples.Branches.RiscV.Proofs

  The functions of `Examples/src/c/branches.c`, compiled by clang at `-O2` to
  `Examples/elf/branches.elf`: straight-line arithmetic, branches, and two loops.

  * `add3(a, b, c)`: the sum.
  * `max2(a, b)`: the greater, signed (`smax`).
  * `umax2(a, b)`: the greater, unsigned (`umax`).
  * `clamp(x, lo, hi)`: `x < lo ? lo : (x > hi ? hi : x)`, signed (`clampSpec`). No precondition
    `lo ≤ hi` is needed: the binary computes the C expression for every `x`, `lo`, `hi`.
  * `sum(p, n)`: the wrapping sum of the `n` longs from `p` (`sumMem`), for `n < 2 ^ 61`. The
    binary walks a pointer to the end pointer `p + 8 * n`; past `2 ^ 61` that end pointer wraps
    (and the C's `p[i]` would be out of any object), so the precondition is asked for.
  * `count_down(n)`: the number of times `n >>= 1` runs before `n` is zero (`countDown`, the C
    loop on numbers: the bit length of `n`). clang has no loop left: it fills the bits below the
    highest, complements, and counts them with a population count, then subtracts from 64. The
    machine's result is characterised bit-wise by `bv_decide` (`count_down_bits`) and that
    characterisation pins it to `countDown` (`countDown_unique`).

  `_start` is a jump to itself and never returns: it has no contract.

  Each function has its contract at Lprog, proved with `lsym`, and the same statement over
  riscv-zkvm's machine (`_correct`), through `SafeN.of_isa_contract`.
-/

import Examples.Branches.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Branches.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Branches.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-! ## `countDown` (`smax`, `clampSpec`, `countDown` are in `Examples/Spec.lean`, `sumMem` in
  `Examples/Kit.lean`, shared with `BranchesO0`) -/

/-- `countDown n ≤ k` exactly when `n < 2 ^ k`. -/
theorem countDown_le_iff (k : Nat) : ∀ n, countDown n ≤ k ↔ n < 2 ^ k := by
  induction k with
  | zero => intro n; rw [countDown]; split <;> simp_all
  | succ k ih =>
    intro n; rw [countDown]
    split
    · subst_vars; simp [Nat.two_pow_pos]
    · rw [Nat.pow_succ]; have := ih (n / 2); omega

/-- A logical shift right, on numbers. -/
theorem toNat_ushiftRight' (x r : BitVec 64) : (x >>> r).toNat = x.toNat / 2 ^ r.toNat := by
  simp [BitVec.ushiftRight_eq', Nat.shiftRight_eq_div_pow]

/-- A number below `2 ^ 64` is pinned to `countDown` by its shifts: `r` halvings take it to
    zero and `r - 1` do not. -/
theorem countDown_unique (x r : Word) (h1 : r ≤ 64#64) (h2 : x >>> r = 0#64)
    (h3 : r = 0#64 ∨ x >>> (r - 1#64) ≠ 0#64) : r = BitVec.ofNat 64 (countDown x.toNat) := by
  have hr : r.toNat ≤ 64 := by bv_omega
  have hlt : x.toNat < 2 ^ r.toNat := by
    have := congrArg BitVec.toNat h2
    rw [toNat_ushiftRight'] at this
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp (by simpa using this)
  have hle := (countDown_le_iff _ _).mpr hlt
  have hge : r.toNat ≤ countDown x.toNat := by
    rcases h3 with h3 | h3
    · subst h3; simp
    · have hr0 : r ≠ 0#64 := by rintro rfl; exact h3 (by bv_decide)
      have hr0' : r.toNat ≠ 0 := fun h => hr0 (BitVec.eq_of_toNat_eq (by simpa using h))
      have hge' : 2 ^ (r.toNat - 1) ≤ x.toNat := by
        refine Nat.le_of_not_lt fun h => h3 ?_
        apply BitVec.eq_of_toNat_eq
        have e : (r - 1#64).toNat = r.toNat - 1 := by bv_omega
        rw [toNat_ushiftRight', e, Nat.div_eq_of_lt h]; rfl
      have : ¬countDown x.toNat ≤ r.toNat - 1 := fun h =>
        absurd ((countDown_le_iff _ _).mp h) (by omega)
      omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## `add3`, `max2`, `umax2`, `clamp` -/

/-- `add3(a, b, c)`: the sum, every other register and the memory kept. -/
theorem add3_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  apply hk
  exact ⟨by simp only [lsym_simp]; ac_rfl, fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`add3` on the machine.** -/
theorem add3_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode add3_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `max2(a, b)`: the greater, signed; every other register and the memory kept. -/
theorem max2_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = smax (regs .x10) (regs .x11) ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp]
  · exact hk _ _ ⟨by simp [smax, hc], fun _ _ => rfl, rfl⟩
  · exact hk _ _ ⟨by simp [lsym_simp, smax, hc], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`max2` on the machine.** -/
theorem max2_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x100c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = smax (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x100c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode max2_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `umax2(a, b)`: the greater, unsigned; every other register and the memory kept. -/
theorem umax2_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = umax (regs .x10) (regs .x11) ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq with [hra, hsp]
  · exact hk _ _ ⟨by simp [umax, hc], fun _ _ => rfl, rfl⟩
  · exact hk _ _ ⟨by simp [lsym_simp, umax, BitVec.not_lt.mpr hc], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`umax2` on the machine.** -/
theorem umax2_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1018#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = umax (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x1018#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode umax2_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `clamp(x, lo, hi)`: `x < lo ? lo : (x > hi ? hi : x)`, signed, for any `lo` and `hi`; every
    register but `a0` and `a3`, and the memory, kept. -/
theorem clamp_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = clampSpec (regs .x10) (regs .x11) (regs .x12) ∧
      (∀ r, r ≠ .x10 → r ≠ .x13 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f3_eq with [hra, hsp]
  all_goals
    refine hk _ _ ⟨?_, fun r h h' => ?_, rfl⟩
    · simp only [lsym_simp, clampSpec] at *; bv_decide
    · simp [lsym_simp, h, h']

/-- **`clamp` on the machine.** -/
theorem clamp_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1024#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = clampSpec (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[3]? = some fn ∧ fn.base = 0x1024#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode clamp_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## `sum` -/

/-- **The loop of `sum`**, at its head, with `j < n` doublewords summed. -/
theorem sum_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (p : Word) (n : Nat) (hn : n < 2 ^ 61)
    (hpost : ∀ r' m', r' .x10 = sumMem m p n → m' = m → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64), n - j = k → j < n →
      regs .x12 = p + BitVec.ofNat 64 (8 * j) → regs .x11 = p + BitVec.ofNat 64 (8 * n) →
      regs .x10 = sumMem m p j → regs .x1 = ret → regs .x2 = top →
      LSafeN fns G N Q ⟨⟨4, 10, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ hk hj; omega
  | succ k ih =>
    intro j regs hk hj h12 h11 h10 hra hsp
    lsym f4_eq stop [10] with [h12, h11, h10, hra, hsp]
    · -- the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · obtain rfl : n = j + 1 := by omega
          simp only [lsym_addr] at hc; simp at hc
      apply ih (j + 1) _ (by omega) hlt
      all_goals simp [lsym_simp, lsym_addr, sumMem, h11, hra, hsp, BitVec.add_comm]
    · -- the exit
      have : j + 1 = n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exfalso
          have := congrArg BitVec.toNat hc
          simp [BitVec.toNat_add, BitVec.toNat_ofNat] at this
          omega
        · omega
      subst this
      apply hpost
      · simp [lsym_simp, sumMem, BitVec.add_comm]
      · rfl

/-- `sum(p, n)`: the wrapping sum of the `n` longs from `p`, for `n < 2 ^ 61` (so that `8 * n`
    does not wrap); memory unchanged. -/
theorem sum_contract : rvIsa.Contract (liftProg fns) sp1Ctx 4
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ (regs .x11).toNat < 2 ^ 61)
    (fun _ _ regs m r' m' => r' .x10 = sumMem m (regs .x10) (regs .x11).toNat ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hn⟩ hk
  lsym f4_eq stop [10] with [hra, hsp]
  · -- no doublewords
    apply hk
    simp [lsym_simp, hc, sumMem]
  · -- the loop, from its first doubleword
    have hpos : 0 < (regs .x11).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x11).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hc
      · exact h
    apply sum_loop m (regs .x10) _ hn (fun r' m' h1 h2 => hk r' m' ⟨h1, h2⟩) _ 0 _ rfl hpos
    all_goals simp [lsym_simp, sumMem, hra, hsp, shl3]

/-- **`sum` on the machine.** -/
theorem sum_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1048#64) (hcode : Loaded fns s) (hn : (s.getReg .x11).toNat < 2 ^ 61)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = sumMem s (s.getReg .x10) (s.getReg .x11).toNat →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[4]? = some fn ∧ fn.base = 0x1048#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sum_contract
    ⟨rfl, rfl, by simpa [regsOf] using hn⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## `count_down` -/

/-- `count_down(n)`: the number of halvings that take `n` to zero (its bit length); every
    register but `a0`..`a5`, and the memory, kept. -/
theorem count_down_contract : rvIsa.Contract (liftProg fns) sp1Ctx 5
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = BitVec.ofNat 64 (countDown (regs .x10).toNat) ∧
      (∀ r, r ∉ [Reg.x10, .x11, .x12, .x13, .x14, .x15] → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f5_eq with [hra, hsp]
  · refine hk _ _ ⟨?_, fun _ _ => rfl, rfl⟩
    simp only [lsym_simp, hc]; rw [countDown]; rfl
  · refine hk _ _ ⟨?_, fun r h => ?_, rfl⟩
    · simp only [lsym_simp]
      generalize regs .x10 = x at hc ⊢
      apply countDown_unique
      all_goals bv_decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      simp [lsym_simp, h]

/-- **`count_down` on the machine.** -/
theorem count_down_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1078#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (countDown (s.getReg .x10).toNat) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[5]? = some fn ∧ fn.base = 0x1078#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode count_down_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

end Examples.Branches.RiscV
