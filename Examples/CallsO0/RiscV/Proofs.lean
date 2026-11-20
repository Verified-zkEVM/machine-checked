/-
  Examples.CallsO0.RiscV.Proofs

  The functions of `Examples/src/c/calls_o0.c` (the same source as `calls.c`), compiled by clang at
  `-O0` to `Examples/elf/calls_o0.elf`: every function builds a frame (`ra` and `s0` saved, `s0`
  the frame pointer) and keeps its arguments in it.

  The contracts state the result, the registers kept, and the memory kept: every doubleword
  outside a window of `n` bytes below the stack pointer (`Outside top n a`), the window being the
  function's frame and its callees'. A caller reads its own frame back after a call because it is
  outside the callee's window (`outside_of`), and a callee's window lies in its caller's
  (`outside_shift`).

  * `inc`, `sum4`: leaves.
  * `twice_inc`, `tail_inc`, `apply_inc`, `keep`, `checked_div`: calls through the callees'
    contracts.
  * `apply(f, x)`: a call through a register to whatever `f` is, proved for `f = inc`.
  * `fact`: recursion, by induction on the argument, with room for its frames below `sp`.
  * `stop`: never returns (its contract's postcondition is `False`); `_start` likewise, not proved.

  Each but `stop` has its contract at Lprog, proved with `lsym`, and the same statement over
  riscv-zkvm's machine (`_correct`).
-/

import Examples.CallsO0.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.CallsO0.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.CallsO0.RiscV.Image

theorem hok : ProgOk fns := by decide

/-- A register the register file kept, read on the machine. -/
theorem getReg_kept {r' : Reg → BitVec 64} {m' t s : MachineState}
    (h : Agree (ofParts r' m') t) {r : Reg} (hr : r' r = regsOf s r) : t.getReg r = s.getReg r := by
  rw [← h.regs, getReg_ofParts]
  split
  · subst_vars; rfl
  · exact hr

/-- A cell of memory kept, read on the machine. -/
theorem getMem_kept {r' : Reg → BitVec 64} {m' t s : MachineState}
    (h : Agree (ofParts r' m') t) {a : Word} (ha : m'.getMem a = s.getMem a) : t.getMem a = s.getMem a := by
  rw [← h.mem, getMem_ofParts]; exact ha

/-- `a` is not one of the `n` bytes below `top` (counted modulo `2^64`). -/
def Outside (top : Word) (n : Nat) (a : Word) : Prop :=
  n ≤ (a - (top - BitVec.ofNat 64 n)).toNat

/-- A callee's window, `k` bytes below the caller's `top`, inside the caller's. -/
theorem outside_shift {top a c : Word} {k n : Nat} (hc : c = -BitVec.ofNat 64 k)
    (h : Outside top (k + n) a) : Outside (top + c) n a := by
  subst hc; unfold Outside at *
  have e : top + -BitVec.ofNat 64 k - BitVec.ofNat 64 n = top - BitVec.ofNat 64 (k + n) := by
    rw [BitVec.ofNat_add]
    generalize BitVec.ofNat 64 k = x; generalize BitVec.ofNat 64 n = y; bv_omega
  rw [e]; omega

/-- A cell of the frame, `-c` bytes from `top`, is not outside the window. -/
theorem outside_ne {top a : Word} {n : Nat} (h : Outside top n a) (c : Word)
    (hc : 0 < (-c).toNat ∧ (-c).toNat ≤ n) : a ≠ top + c := by
  rintro rfl; unfold Outside at h
  have hn : n < 2 ^ 64 := Nat.lt_of_le_of_lt h (BitVec.isLt _)
  have e : top + c - (top - BitVec.ofNat 64 n) = c + BitVec.ofNat 64 n := by
    generalize BitVec.ofNat 64 n = x; bv_omega
  rw [e] at h
  have : (BitVec.ofNat 64 n).toNat = n := by simp; omega
  bv_omega

/-- A caller's cell, `top + d`, is outside its callee's window. -/
theorem outside_of (top c d : Word) (n : Nat) (h : n ≤ (d - (c - BitVec.ofNat 64 n)).toNat) :
    Outside (top + c) n (top + d) := by
  unfold Outside
  have e : top + d - (top + c - BitVec.ofNat 64 n) = d - (c - BitVec.ofNat 64 n) := by
    generalize BitVec.ofNat 64 n = x; bv_omega
  rw [e]; exact h

/-- `inc(x)`: `x + 1`. Every register but `a0` kept (`ra`, `s0` and `sp` by the frame), and the
    memory outside the 32 bytes of the frame below `sp`. -/
theorem inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = regs .x10 + 1 ∧ (∀ r, r ≠ .x10 → r' r = regs r) ∧
      (∀ a, Outside top 32 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  apply hk
  refine ⟨by simp [lsym_simp], fun r h => ?_, fun a ha => ?_⟩
  · by_cases h1 : r = .x1
    · subst h1; simp [lsym_simp, hra]
    by_cases h2 : r = .x2
    · subst h2; simp [lsym_simp, hsp]
    by_cases h8 : r = .x8
    · subst h8; simp [lsym_simp]
    simp [lsym_simp, h, h1, h2, h8]
  · obtain ⟨n1, n2, n3⟩ : a ≠ top + 18446744073709551608#64 ∧ a ≠ top + 18446744073709551600#64 ∧
        a ≠ top + 18446744073709551592#64 := by
      unfold Outside at ha; refine ⟨?_, ?_, ?_⟩ <;> bv_omega
    simp [n1, n2, n3]

/-- **`inc` on the machine.** -/
theorem inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 1 →
      (∀ r, r ≠ .x10 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 32 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 => getReg_kept hag (hr r h0)) (fun a ha => getMem_kept hag (hm a ha))

/-- `twice_inc(x)`: `x + 2`, by two calls of `inc` through its contract, `x` kept in the frame.
    Every register but `a0` kept, and the memory outside 64 bytes below `sp` (its frame and
    `inc`'s). -/
theorem twice_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = regs .x10 + 2 ∧ (∀ r, r ≠ .x10 → r' r = regs r) ∧
      (∀ a, Outside top 64 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp] using [inc_contract]
  all_goals
    obtain ⟨h10a, hra_a, hma⟩ := hret_1
    obtain ⟨h10b, hrb, hmb⟩ := hret
    have hsp1 := hra_a .x2 (by decide)
    simp only [reduceCtorEq, ite_false, ite_true] at hsp1
    rw [hsp1] at hmb
    have hm := fun a h => (hmb a h).trans (hma a h)
  · rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
    simp [lsym_simp]
  · simp [lsym_simp]
  · apply hk
    refine ⟨?_, fun r h => ?_, fun a ha => ?_⟩
    · simp only [lsym_simp]; rw [h10b, h10a]; bv_omega
    · by_cases h1 : r = .x1
      · subst h1; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp [hra]
      by_cases h2 : r = .x2
      · subst h2; simp [lsym_simp, hsp]
      by_cases h8 : r = .x8
      · subst h8; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp
      simp only [lsym_simp]; rw [hrb r h, hra_a r h]; simp [h, h1, h2, h8]
    · rw [hm _ (outside_shift (k := 32) (by decide +kernel) ha)]
      have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
      have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
      have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
      simp [n1, n2, n3]

/-- **`twice_inc` on the machine.** -/
theorem twice_inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x102c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 2 →
      (∀ r, r ≠ .x10 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 64 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x102c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode twice_inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 => getReg_kept hag (hr r h0)) (fun a ha => getMem_kept hag (hm a ha))

/-- `sum4(a, b, c, d)`: the sum, every argument through the frame. Every register but `a0`, `a1`
    kept, and the memory outside the 48 bytes of the frame. -/
theorem sum4_contract : rvIsa.Contract (liftProg fns) sp1Ctx 5
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 + regs .x13 ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r' r = regs r) ∧
      (∀ a, Outside top 48 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f5_eq with [hra, hsp]
  apply hk
  refine ⟨by simp [lsym_simp], fun r h h' => ?_, fun a ha => ?_⟩
  · by_cases h1 : r = .x1
    · subst h1; simp [lsym_simp, hra]
    by_cases h2 : r = .x2
    · subst h2; simp [lsym_simp, hsp]
    by_cases h8 : r = .x8
    · subst h8; simp [lsym_simp]
    simp [lsym_simp, h, h', h1, h2, h8]
  · have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
    have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
    have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
    have n4 := outside_ne ha 18446744073709551584#64 (by decide +kernel)
    have n5 := outside_ne ha 18446744073709551576#64 (by decide +kernel)
    have n6 := outside_ne ha 18446744073709551568#64 (by decide +kernel)
    simp [n1, n2, n3, n4, n5, n6]

/-- **`sum4` on the machine.** -/
theorem sum4_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1128#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 + s.getReg .x13 →
      (∀ r, r ≠ .x10 → r ≠ .x11 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 48 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[5]? = some fn ∧ fn.base = 0x1128#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sum4_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 h1 => getReg_kept hag (hr r h0 h1)) (fun a ha => getMem_kept hag (hm a ha))

/-- `stop`'s loop, safe at every budget: one unit spent at its label each time round. -/
theorem stop_loop {G : State rvIsa → Prop} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} : ∀ N (regs : Reg → Word) (m : MachineState),
      LSafeN fns G N Q ⟨⟨8, 10, ret, top⟩ :: rest, regs, m⟩ := by
  intro N
  induction N with
  | zero => intro _ _; exact Ascent.SafeN.zero
  | succ n ih =>
    intro regs m
    refine SafeN.label_spend f8_eq rfl ?_
    lsym f8_eq stop [10]
    exact ih _ _

/-- `stop` never returns: its postcondition is `False`. After its prologue, a loop that never
    ends (`stop_loop`). -/
theorem stop_contract : rvIsa.Contract (liftProg fns) sp1Ctx 8
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top) (fun _ _ _ _ _ _ => False) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ _
  lsym f8_eq stop [10] with [hra, hsp]
  exact stop_loop _ _ _

/-- `checked_div(a, b)`: the quotient, when the divisor is not zero; it calls `stop` and never
    returns otherwise. Every register but `a0`, `a1` kept, and the memory outside the frame. -/
theorem checked_div_contract : rvIsa.Contract (liftProg fns) sp1Ctx 9
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => regs .x11 ≠ 0 ∧ r' .x10 = (regs .x10).sdiv (regs .x11) ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r' r = regs r) ∧
      (∀ a, Outside top 32 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f9_eq with [hra, hsp] using [stop_contract]
  apply hk
  refine ⟨hc, by simp [lsym_simp, hc], fun r h h' => ?_, fun a ha => ?_⟩
  · by_cases h1 : r = .x1
    · subst h1; simp [lsym_simp, hra]
    by_cases h2 : r = .x2
    · subst h2; simp [lsym_simp, hsp]
    by_cases h8 : r = .x8
    · subst h8; simp [lsym_simp]
    simp [lsym_simp, h, h', h1, h2, h8]
  · have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
    have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
    have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
    have n4 := outside_ne ha 18446744073709551584#64 (by decide +kernel)
    simp [n1, n2, n3, n4]

/-- **`checked_div` on the machine.** It returns only when the divisor
    is not zero. -/
theorem checked_div_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1228#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      s.getReg .x11 ≠ 0#64 →
      t.getReg .x10 = (s.getReg .x10).sdiv (s.getReg .x11) →
      (∀ r, r ≠ .x10 → r ≠ .x11 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 32 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[9]? = some fn ∧ fn.base = 0x1228#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode checked_div_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨hc, h10, hr, hm⟩
  exact hk t hpc' (by simpa [regsOf] using hc) (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 h1 => getReg_kept hag (hr r h0 h1)) (fun a ha => getMem_kept hag (hm a ha))

/-- `apply(f, x)`: a call through a register of whatever `f` is; proved for `f = inc` (`a0` is
    `inc`'s address, `0x1000`), through `inc`'s contract. Every register but `a0`, `a1` kept,
    and the memory outside 64 bytes below `sp`. -/
theorem apply_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ regs .x10 = 0x1000#64)
    (fun _ top regs m r' m' => r' .x10 = regs .x11 + 1 ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r' r = regs r) ∧
      (∀ a, Outside top 64 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hf⟩ hk
  lsym f3_eq with [hra, hsp, hf] using [inc_contract]
  all_goals obtain ⟨h10b, hrb, hm⟩ := hret
  · rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
    simp [lsym_simp]
  · simp [lsym_simp]
  · apply hk
    refine ⟨?_, fun r h h' => ?_, fun a ha => ?_⟩
    · simp only [lsym_simp]; exact h10b
    · by_cases h1 : r = .x1
      · subst h1; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp [hra]
      by_cases h2 : r = .x2
      · subst h2; simp [lsym_simp, hsp]
      by_cases h8 : r = .x8
      · subst h8; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp
      simp only [lsym_simp]; rw [hrb r h]; simp [h, h', h1, h2, h8]
    · rw [hm _ (outside_shift (k := 32) (by decide +kernel) ha)]
      have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
      have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
      have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
      have n4 := outside_ne ha 18446744073709551584#64 (by decide +kernel)
      simp [n1, n2, n3, n4]

/-- **`apply` on the machine.** `f` is fixed to `inc`'s address,
    `0x1000`, as in `apply_contract`: `apply` calls through a register whatever `f` is, and this
    is the one function it is proved for. -/
theorem apply_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10c0#64) (hcode : Loaded fns s)
    (hf : s.getReg .x10 = 0x1000#64)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x11 + 1 →
      (∀ r, r ≠ .x10 → r ≠ .x11 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 64 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[3]? = some fn ∧ fn.base = 0x10c0#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode apply_contract ⟨rfl, rfl, by simpa [regsOf] using hf⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 h1 => getReg_kept hag (hr r h0 h1)) (fun a ha => getMem_kept hag (hm a ha))

/-- `apply_inc(x)`: `apply(inc, x)`, `x + 1`, through `apply`'s contract. Every register but
    `a0`, `a1` kept, and the memory outside 96 bytes below `sp`. -/
theorem apply_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 4
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = regs .x10 + 1 ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r' r = regs r) ∧
      (∀ a, Outside top 96 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f4_eq with [hra, hsp] using [apply_contract]
  all_goals obtain ⟨h10b, hrb, hm⟩ := hret
  · rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
    simp [lsym_simp]
  · simp [lsym_simp]
  · apply hk
    refine ⟨?_, fun r h h' => ?_, fun a ha => ?_⟩
    · simp only [lsym_simp]; exact h10b
    · by_cases h1 : r = .x1
      · subst h1; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp [hra]
      by_cases h2 : r = .x2
      · subst h2; simp [lsym_simp, hsp]
      by_cases h8 : r = .x8
      · subst h8; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp
      simp only [lsym_simp]; rw [hrb r h h']; simp [h, h', h1, h2, h8]
    · rw [hm _ (outside_shift (k := 32) (by decide +kernel) ha)]
      have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
      have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
      have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
      simp [n1, n2, n3]

/-- **`apply_inc` on the machine.** -/
theorem apply_inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10f4#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 1 →
      (∀ r, r ≠ .x10 → r ≠ .x11 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 96 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[4]? = some fn ∧ fn.base = 0x10f4#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode apply_inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 h1 => getReg_kept hag (hr r h0 h1)) (fun a ha => getMem_kept hag (hm a ha))

/-- `tail_inc(x)`: `inc(x + 1)`, `x + 2` (at `-O0` a call, not a tail call). Every register but
    `a0` kept, and the memory outside 64 bytes below `sp`. -/
theorem tail_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 7
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = regs .x10 + 2 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧
      (∀ a, Outside top 64 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f7_eq with [hra, hsp] using [inc_contract]
  all_goals obtain ⟨h10b, hrb, hm⟩ := hret
  · rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
    simp [lsym_simp]
  · simp [lsym_simp]
  · apply hk
    refine ⟨?_, fun r h => ?_, fun a ha => ?_⟩
    · simp only [lsym_simp]; exact h10b
    · by_cases h1 : r = .x1
      · subst h1; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp [hra]
      by_cases h2 : r = .x2
      · subst h2; simp [lsym_simp, hsp]
      by_cases h8 : r = .x8
      · subst h8; simp only [lsym_simp]; rw [hm _ (outside_of _ _ _ _ (by decide +kernel))]
        simp
      simp only [lsym_simp]; rw [hrb r h]; simp [h, h1, h2, h8]
    · rw [hm _ (outside_shift (k := 32) (by decide +kernel) ha)]
      have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
      have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
      have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
      simp [n1, n2, n3]

/-- **`tail_inc` on the machine.** -/
theorem tail_inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x11e0#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 2 →
      (∀ r, r ≠ .x10 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 64 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[7]? = some fn ∧ fn.base = 0x11e0#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode tail_inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 => getReg_kept hag (hr r h0)) (fun a ha => getMem_kept hag (hm a ha))

/-- `keep(a, b, c, d)`: `a + b + c + d + a * b + c * d`, the four arguments kept in the frame across
    the call of `sum4`. Every register but `a0`..`a3` kept, and the memory outside 112 bytes below
    `sp` (its frame and `sum4`'s). -/
theorem keep_contract : rvIsa.Contract (liftProg fns) sp1Ctx 6
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 + regs .x13 +
        regs .x10 * regs .x11 + regs .x12 * regs .x13 ∧
      (∀ r, r ∉ [Reg.x10, .x11, .x12, .x13] → r' r = regs r) ∧
      (∀ a, Outside top 112 a → m'.getMem a = m.getMem a)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f6_eq with [hra, hsp] using [sum4_contract]
  all_goals
    obtain ⟨h10b, hrb, hm⟩ := hret
    have c8 := hm _ (outside_of top 18446744073709551552#64 18446744073709551608#64 48 (by decide +kernel))
    have c16 := hm _ (outside_of top 18446744073709551552#64 18446744073709551600#64 48 (by decide +kernel))
    have c24 := hm _ (outside_of top 18446744073709551552#64 18446744073709551592#64 48 (by decide +kernel))
    have c32 := hm _ (outside_of top 18446744073709551552#64 18446744073709551584#64 48 (by decide +kernel))
    have c40 := hm _ (outside_of top 18446744073709551552#64 18446744073709551576#64 48 (by decide +kernel))
    have c48 := hm _ (outside_of top 18446744073709551552#64 18446744073709551568#64 48 (by decide +kernel))
    simp only [MachineState.getMem_setMem_eq, ne_eq, MachineState.getMem_setMem_ne, BitVec.add_right_inj,
      BitVec.reduceEq, not_false_eq_true] at c8 c16 c24 c32 c40 c48
  · simp [lsym_simp, c8]
  · simp [lsym_simp]
  · apply hk
    refine ⟨?_, fun r h => ?_, fun a ha => ?_⟩
    · simp only [lsym_simp, c24, c32, c40, c48]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      obtain ⟨h10, h11, h12, h13⟩ := h
      by_cases h1 : r = .x1
      · subst h1; simp [lsym_simp, c8, hra]
      by_cases h2 : r = .x2
      · subst h2; simp [lsym_simp, hsp]
      by_cases h8 : r = .x8
      · subst h8; simp [lsym_simp, c16]
      simp only [lsym_simp]; rw [hrb r h10 h11]; simp [h10, h11, h12, h13, h1, h2, h8]
    · have n56 := outside_ne ha 18446744073709551560#64 (by decide +kernel)
      rw [MachineState.getMem_setMem_ne n56, hm _ (outside_shift (k := 64) (by decide +kernel) ha)]
      have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
      have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
      have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
      have n4 := outside_ne ha 18446744073709551584#64 (by decide +kernel)
      have n5 := outside_ne ha 18446744073709551576#64 (by decide +kernel)
      have n6 := outside_ne ha 18446744073709551568#64 (by decide +kernel)
      simp [n1, n2, n3, n4, n5, n6]

/-- From `ra = ret`, `sp = top` and `a0 = k`, with room for `k + 1` frames of 48 bytes below
    `top`. -/
def FactPre (k : Nat) : Word → Word → (Reg → Word) → MachineState → Prop :=
  fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ regs .x10 = BitVec.ofNat 64 k ∧
    48 * (k + 1) ≤ top.toNat

/-- `k!` in `a0`; every register but `a0` and `a1` kept; the memory outside those frames kept. -/
def FactPost (k : Nat) : Word → Word → (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop :=
  fun _ top regs m r' m' => r' .x10 = BitVec.ofNat 64 (factN k) ∧
    (∀ r, r ≠ .x10 → r ≠ .x11 → r' r = regs r) ∧
    (∀ a, Outside top (48 * (k + 1)) a → m'.getMem a = m.getMem a)

/-- The caller's cells `top - 8`, `top - 16` and `top - 40` are outside the windows of the
    recursive call, at `top - 48`. -/
theorem fact_cells {top : Word} {j : Nat} (hroom : 48 * (j + 1 + 1) ≤ top.toNat) :
    Outside (top + 18446744073709551568#64) (48 * (j + 1)) (top + 18446744073709551608#64) ∧
    Outside (top + 18446744073709551568#64) (48 * (j + 1)) (top + 18446744073709551600#64) ∧
    Outside (top + 18446744073709551568#64) (48 * (j + 1)) (top + 18446744073709551576#64) := by
  have hn : (BitVec.ofNat 64 (48 * (j + 1))).toNat = 48 * (j + 1) := by
    have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
  unfold Outside
  generalize BitVec.ofNat 64 (48 * (j + 1)) = x at hn
  have e : ∀ c : Word, top + c - (top + 18446744073709551568#64 - x) = x + (c + 48#64) := by
    intro c; bv_omega
  rw [e, e, e]
  have := top.isLt
  refine ⟨?_, ?_, ?_⟩ <;> rw [BitVec.toNat_add] <;> simp only [hn] <;> simp <;> omega

/-- **`fact`'s contract**: `n!`, modulo `2^64`, by induction on `n`: the recursive call goes
    through the contract of `n - 1`. The memory outside the `n + 1` frames is kept. -/
theorem fact_contract : ∀ k, rvIsa.Contract (liftProg fns) sp1Ctx 2 (FactPre k) (FactPost k) := by
  intro k
  induction k with
  | zero =>
    intro G N Q ret top rest regs m ⟨hra, hsp, h10, hroom⟩ hk
    lsym f2_eq with [hra, hsp, h10]
    apply hk
    refine ⟨by simp [lsym_simp, factN], fun r h h' => ?_, fun a ha => ?_⟩
    · by_cases h1 : r = .x1
      · subst h1; simp [lsym_simp, hra]
      by_cases h2 : r = .x2
      · subst h2; simp [lsym_simp, hsp]
      by_cases h8 : r = .x8
      · subst h8; simp [lsym_simp]
      simp [lsym_simp, h, h1, h2, h8]
    · have n1 := outside_ne ha 18446744073709551608#64 (by decide +kernel)
      have n2 := outside_ne ha 18446744073709551600#64 (by decide +kernel)
      have n3 := outside_ne ha 18446744073709551592#64 (by decide +kernel)
      have n4 := outside_ne ha 18446744073709551584#64 (by decide +kernel)
      simp [n1, n2, n3, n4]
  | succ j ih =>
    intro G N Q ret top rest regs m ⟨hra, hsp, h10, hroom⟩ hk
    have hj : j + 1 < 2 ^ 64 := by have := top.isLt; omega
    lsym f2_eq with [hra, hsp, h10, FactPre, FactPost] using [ih]
    · -- the precondition of the recursive call
      refine ⟨by simp [lsym_simp], by simp [lsym_simp], ?_, ?_⟩
      · simp only [lsym_simp]; bv_omega
      · simp only [lsym_simp]; bv_omega
    rotate_right
    · -- `k + 1` is not zero
      exact absurd hc (by bv_omega)
    all_goals
      obtain ⟨h10b, hrb, hm⟩ := hret
      obtain ⟨o8, o16, o40⟩ := fact_cells hroom
      have c8 := hm _ o8
      have c16 := hm _ o16
      have c40 := hm _ o40
      simp only [MachineState.getMem_setMem_eq, ne_eq, MachineState.getMem_setMem_ne, BitVec.add_right_inj,
        BitVec.reduceEq, not_false_eq_true] at c8 c16 c40
    · simp [lsym_simp, c8]
    · simp [lsym_simp]
    · apply hk
      refine ⟨?_, fun r h h' => ?_, fun a ha => ?_⟩
      · simp only [lsym_simp, c40, factN, BitVec.ofNat_mul]
      · by_cases h1 : r = .x1
        · subst h1; simp [lsym_simp, c8, hra]
        by_cases h2 : r = .x2
        · subst h2; simp [lsym_simp, hsp]
        by_cases h8 : r = .x8
        · subst h8; simp [lsym_simp, c16]
        simp only [lsym_simp]; rw [hrb r h h']; simp [h, h', h1, h2, h8]
      · have hn : 48 ≤ 48 * (j + 1 + 1) := by omega
        have n32 := outside_ne ha 18446744073709551584#64 ⟨by decide +kernel, Nat.le_trans (by decide +kernel) hn⟩
        have ha' : Outside top (48 + 48 * (j + 1)) a := by
          rw [show 48 + 48 * (j + 1) = 48 * (j + 1 + 1) by omega]; exact ha
        rw [MachineState.getMem_setMem_ne n32, hm _ (outside_shift (by decide +kernel) ha')]
        have n1 := outside_ne ha 18446744073709551608#64 ⟨by decide +kernel, Nat.le_trans (by decide +kernel) hn⟩
        have n2 := outside_ne ha 18446744073709551600#64 ⟨by decide +kernel, Nat.le_trans (by decide +kernel) hn⟩
        have n3 := outside_ne ha 18446744073709551592#64 ⟨by decide +kernel, Nat.le_trans (by decide +kernel) hn⟩
        have n5 := outside_ne ha 18446744073709551576#64 ⟨by decide +kernel, Nat.le_trans (by decide +kernel) hn⟩
        simp [n1, n2, n3, n5]

/-- **`keep` on the machine.** -/
theorem keep_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1174#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 + s.getReg .x13 +
        s.getReg .x10 * s.getReg .x11 + s.getReg .x12 * s.getReg .x13 →
      (∀ r, r ∉ [Reg.x10, .x11, .x12, .x13] → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) 112 a → t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[6]? = some fn ∧ fn.base = 0x1174#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode keep_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h => getReg_kept hag (hr r h)) (fun a ha => getMem_kept hag (hm a ha))

/-- **`fact` on the machine**, with room for `n + 1` frames below the stack pointer. -/
theorem fact_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x105c#64) (hcode : Loaded fns s)
    (hroom : 48 * ((s.getReg .x10).toNat + 1) ≤ (s.getReg .x2).toNat)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (factN (s.getReg .x10).toNat) →
      (∀ r, r ≠ .x10 → r ≠ .x11 → t.getReg r = s.getReg r) →
      (∀ a, Outside (s.getReg .x2) (48 * ((s.getReg .x10).toNat + 1)) a → t.getMem a = s.getMem a) →
      SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x105c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode (fact_contract (s.getReg .x10).toNat)
    ⟨rfl, rfl, by simp [regsOf], hroom⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hm⟩
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)
    (fun r h0 h1 => getReg_kept hag (hr r h0 h1)) (fun a ha => getMem_kept hag (hm a ha))

end Examples.CallsO0.RiscV
