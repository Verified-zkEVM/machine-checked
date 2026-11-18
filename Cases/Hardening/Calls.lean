import Cases.Hardening.Gen.Calls
import LprogRiscV.Lsym

namespace Cases.Hardening.Calls

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift
open Cases.Hardening.Gen.Calls

/-- `inc`: `a0 + 1`, every other register and the memory kept. -/
theorem inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + 1 ∧ (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  apply hk
  exact ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩

/-- `twice_inc`: a call and a tail call of `inc`, through its contract, with `ra` saved in a
    frame across the call. -/
theorem twice_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x10 + 2) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp] using [inc_contract]
  apply hk; simp [lsym_simp, hret, hret_1, BitVec.add_assoc]

/-- `tail_inc`: `a0 + 2`, by a tail call of `inc`. -/
theorem tail_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 7
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x10 + 2) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f7_eq with [hra, hsp] using [inc_contract]
  apply hk; simp [lsym_simp, hret]

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

/-- `apply(f, x)`: a tail call through `t1`, to whatever `f` is; here, `inc`. -/
theorem apply_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ regs .x10 = 0x1000#64)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x11 + 1) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hf⟩ hk
  lsym f3_eq with [hra, hsp, hf] using [inc_contract]
  apply hk; simp [lsym_simp, hret]

/-- `apply_inc(x)`: `apply(inc, x)`, a tail call that passes a function's address. -/
theorem apply_inc_contract : rvIsa.Contract (liftProg fns) sp1Ctx 4
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs _ r' _ => r' .x10 = regs .x10 + 1) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f4_eq with [hra, hsp] using [apply_contract]
  apply hk; simp [lsym_simp, hret]

/-- `sum4`: the sum of `a0`..`a3`; it writes `a0` and `a2`, and no memory. -/
theorem sum4_contract : rvIsa.Contract (liftProg fns) sp1Ctx 5
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 + regs .x13 ∧
      (∀ r, r ≠ .x10 → r ≠ .x12 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f5_eq with [hra, hsp]
  apply hk
  refine ⟨by simp [lsym_simp]; bv_decide, fun r h1 h2 => by simp [lsym_simp, h1, h2], rfl⟩

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

end Cases.Hardening.Calls
