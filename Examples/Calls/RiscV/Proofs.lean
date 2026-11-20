/-
  Examples.Calls.RiscV.Proofs

  The functions of `Examples/src/c/calls.c`, compiled by clang to `Examples/elf/calls.elf`: calls,
  tail calls, a call through a register, values kept across a call, and a function that never
  returns.

  * `inc`, `sum4`: leaves. `twice_inc`, `tail_inc`, `keep`, `checked_div`, `apply_inc`: calls
    through the callees' contracts.
  * `apply(f, x)`: a tail call through a register to whatever `f` is; proved for `f = inc`.
  * `fact(n)`: `n!` modulo `2^64`; clang turns the recursion into a loop (`fact_loop`).
  * `stop`: never returns (its contract's postcondition is `False`); `_start` likewise, not proved.

  Each but `stop` has its contract at Lprog, proved with `lsym`, and the same statement over
  riscv-zkvm's machine (`_correct`).
-/

import Examples.Calls.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Calls.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Calls.RiscV.Image

theorem hok : ProgOk fns := by decide

/-- `inc`: `a0 + 1`, every other register and the memory kept. -/
theorem inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + 1 ∧ (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  apply hk
  exact ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩


/-- **`inc` on the machine.** -/
theorem inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 1 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10

/-- `twice_inc`: a call and a tail call of `inc`, through its contract, with `ra` saved in a
    frame across the call. -/
theorem twice_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x10 + 2) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp] using [inc_contract]
  apply hk; simp [lsym_simp, hret, hret_1, BitVec.add_assoc]


/-- **`twice_inc` on the machine.** -/
theorem twice_inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1008#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 2 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x1008#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode twice_inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' h10
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)

/-! ## `fact` -/

/-- The registers `fact` may change. -/
def factClobbered : List Reg := [.x10, .x11, .x12]

/-- **The loop of `fact`**, at its head (label 3) with the counter `j ≠ 0` in `a1` and an
    accumulator in `a0` whose product with `j!` is `v`: it returns `v`. By induction on `j`. -/
theorem fact_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (regs0 : Reg → Word) (v : Word) :
    ∀ j (regs : Reg → Word), (regs .x11).toNat = j → j ≠ 0 →
      regs .x1 = ret → regs .x2 = top →
      regs .x10 * BitVec.ofNat 64 (factN j) = v →
      (∀ r, r ∉ factClobbered → regs r = regs0 r) →
      (∀ r' m', r' .x10 = v ∧ (∀ r, r ∉ factClobbered → r' r = regs0 r) ∧ m' = m →
        LSafeN fns G N Q ⟨rest, r', m'⟩) →
      LSafeN fns G N Q ⟨⟨2, 6, ret, top⟩ :: rest, regs, m⟩ := by
  intro j
  induction j with
  | zero => intro _ _ h; exact absurd rfl h
  | succ j ih =>
    intro regs hj _ hra hsp hv hf hk
    have e11 : regs .x11 = BitVec.ofNat 64 (j + 1) := by rw [← hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    lsym f2_eq stop [6] with [hra, hsp, e11]
    · -- the counter is not yet one: the back edge
      have hj0 : j ≠ 0 := by rintro rfl; exact hc rfl
      refine ih _ ?_ hj0 (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp]) ?_ (fun r hr => ?_) hk
      · simp only [lsym_simp]; bv_omega
      · rw [← hv]; simp only [lsym_simp, factN, BitVec.ofNat_mul]
        ac_rfl
      · simp only [factClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        rw [← hf r (by simp [factClobbered, hr])]; simp [lsym_simp, hr]
    · -- the counter is one
      have hj0 : j = 0 := by bv_omega
      subst hj0
      refine hk _ _ ⟨?_, fun r hr => ?_, rfl⟩
      · rw [← hv]; simp [lsym_simp, factN]
      · rw [← hf r hr]
        simp only [factClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]

/-- `fact(n)`: `n!`, modulo `2^64`; every register but `x10`..`x12` and the memory kept. clang
    turns the recursion into a loop. -/
theorem fact_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = BitVec.ofNat 64 (factN (regs .x10).toNat) ∧
      (∀ r, r ∉ factClobbered → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq stop [6] with [hra, hsp]
  · refine hk _ _ ⟨by simp [lsym_simp, hc, factN], fun r hr => ?_, rfl⟩
    simp only [factClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [lsym_simp, hr]
  · refine fact_loop m regs _ (regs .x10).toNat _ (by simp [lsym_simp]) (by simpa [BitVec.toNat_eq] using hc)
      (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp]) (by simp [lsym_simp]) (fun r hr => ?_) hk
    simp only [factClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [lsym_simp, hr]

/-- **`fact` on the machine.** -/
theorem fact_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1020#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (factN (s.getReg .x10).toNat) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x1020#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode fact_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10

/-- `tail_inc`: `a0 + 2`, by a tail call of `inc`. -/
theorem tail_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 7
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x10 + 2) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f7_eq with [hra, hsp] using [inc_contract]
  apply hk; simp [lsym_simp, hret]


/-- **`tail_inc` on the machine.** -/
theorem tail_inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10d4#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 2 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[7]? = some fn ∧ fn.base = 0x10d4#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode tail_inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' h10
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)

/-- `stop` never returns: its postcondition is `False`. A loop that never ends is safe at every
    budget, by induction on it, one unit spent at the loop's label (`SafeN.label_spend`). -/
theorem stop_contract : rvIsa.Contract (liftProg fns) sp1Ctx 8
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top) (fun _ _ _ _ _ _ => False) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ _
  induction N with
  | zero => exact Ascent.SafeN.zero
  | succ n ih =>
    refine SafeN.label_spend f8_eq rfl ?_
    lsym f8_eq stop [0]
    exact ih (fun _ _ h => h.elim)

/-- `checked_div`: the quotient, when the divisor is not zero; it never returns otherwise. -/
theorem checked_div_contract : rvIsa.Contract (liftProg fns) sp1Ctx 9
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => regs .x11 ≠ 0 ∧ r' .x10 = (regs .x10).sdiv (regs .x11)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f9_eq with [hra, hsp] using [stop_contract]
  exact hk _ _ ⟨hc, by simp [lsym_simp, hc]⟩


/-- **`checked_div` on the machine.** It returns only when the divisor
    is not zero. -/
theorem checked_div_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10e0#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      s.getReg .x11 ≠ 0#64 → t.getReg .x10 = (s.getReg .x10).sdiv (s.getReg .x11) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[9]? = some fn ∧ fn.base = 0x10e0#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode checked_div_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨hc, h10⟩
  exact hk t hpc' (by simpa [regsOf] using hc)
    (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)

/-- `apply(f, x)`: a tail call through `t1`, to whatever `f` is; here, `inc`. -/
theorem apply_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ regs .x10 = 0x1000#64)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x11 + 1) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hf⟩ hk
  lsym f3_eq with [hra, hsp, hf] using [inc_contract]
  apply hk; simp [lsym_simp, hret]


/-- **`apply` on the machine.** `f` is fixed to `inc`'s address,
    `0x1000`, as in `apply_contract`: `apply` is a tail call through a register to whatever `f` is,
    and this is the one function it is proved for. -/
theorem apply_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1048#64) (hcode : Loaded fns s)
    (hf : s.getReg .x10 = 0x1000#64)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x11 + 1 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[3]? = some fn ∧ fn.base = 0x1048#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode apply_contract
    ⟨rfl, rfl, by simpa [regsOf] using hf⟩ ?_
  rintro t r' m' hag hpc' h10
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)

/-- `apply_inc(x)`: `apply(inc, x)`, a tail call that passes a function's address. -/
theorem apply_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 4
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x10 + 1) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f4_eq with [hra, hsp] using [apply_contract]
  apply hk; simp [lsym_simp, hret]


/-- **`apply_inc` on the machine.** -/
theorem apply_inc_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1054#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + 1 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[4]? = some fn ∧ fn.base = 0x1054#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode apply_inc_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' h10
  exact hk t hpc' (by rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10)

/-- `sum4`: the sum of `a0`..`a3`; it writes `a0` and `a2`, and no memory. -/
theorem sum4_contract : rvIsa.Contract (liftProg fns) sp1Ctx 5
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 + regs .x13 ∧
      (∀ r, r ≠ .x10 → r ≠ .x12 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f5_eq with [hra, hsp]
  apply hk
  refine ⟨by simp [lsym_simp]; bv_decide, fun r h1 h2 => by simp [lsym_simp, h1, h2], rfl⟩


/-- **`sum4` on the machine.** -/
theorem sum4_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x106c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 + s.getReg .x13 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[5]? = some fn ∧ fn.base = 0x106c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sum4_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [getReg_of_agree hag (by decide)]; simpa [regsOf] using h10

/-- `keep(a, b, c, d)`: `a + b + c + d + a * b + c * d`, with `a`..`d` kept in `s0`..`s3`
    across the call of `sum4`, and those saved in a frame and restored: the registers the
    convention keeps are kept. -/
theorem keep_contract : rvIsa.Contract (liftProg fns) sp1Ctx 6
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x10 + regs .x11 + regs .x12 + regs .x13 +
        regs .x10 * regs .x11 + regs .x12 * regs .x13 ∧
      r' .x8 = regs .x8 ∧ r' .x9 = regs .x9 ∧ r' .x18 = regs .x18 ∧ r' .x19 = regs .x19 ∧
      r' .x2 = regs .x2) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f6_eq with [hra, hsp] using [sum4_contract]
  apply hk
  simp [lsym_simp]
  refine ⟨?_, hsp.symm⟩
  rw [BitVec.mul_comm (regs .x13), BitVec.mul_comm (regs .x11)]
  ac_rfl


/-- **`keep` on the machine.** -/
theorem keep_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x107c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 + s.getReg .x13 +
        s.getReg .x10 * s.getReg .x11 + s.getReg .x12 * s.getReg .x13 →
      t.getReg .x8 = s.getReg .x8 → t.getReg .x9 = s.getReg .x9 → t.getReg .x18 = s.getReg .x18 →
      t.getReg .x19 = s.getReg .x19 → t.getReg .x2 = s.getReg .x2 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[6]? = some fn ∧ fn.base = 0x107c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode keep_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, h8, h9, h18, h19, h2⟩
  simp only [regsOf] at h10 h8 h9 h18 h19 h2
  refine hk t hpc' ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [getReg_of_agree hag (by decide)] <;> assumption

end Examples.Calls.RiscV
