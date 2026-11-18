import Cases.Hardening.Gen.KU128.F155
import LprogRiscV.Lsym

/-!
  # A guest's `__udivti3`, through its callee's contract

  `k_u128`, one of `scripts/decompile-check`'s Rust guests, built for SP1 by rustc. Its
  `__udivti3` (`compiler_builtins`) passes a pointer into its own frame to
  `u128_div_rem`, which it calls by `auipc` and `jalr`, and returns the quotient it reads
  back from there. Its contract is proved from a contract of `u128_div_rem`, which is
  assumed here (`hdiv`): the point is how real code composes through a contract, a result
  returned through memory included. Of the guest's modules, only the words and `__udivti3`'s
  (`F155`) are kept: `u128_div_rem` is not stepped.
-/

namespace Cases.Hardening.Guest

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift
open Cases.Hardening.Gen.KU128

/-- A 128-bit number from its two halves. -/
def u128 (lo hi : Word) : BitVec 128 := hi ++ lo

/-- `u128_div_rem(out, a_lo, a_hi, b_lo, b_hi)`: the quotient's halves at `out` and `out + 8`,
    the remainder's at `out + 16` and `out + 24`; `s0`, `sp` kept; memory outside those four
    cells, kept. -/
def DivPre : Word → Word → (Reg → Word) → MachineState → Prop :=
  fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ regs .x14 ++ regs .x13 ≠ 0#128

def DivPost : Word → Word → (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop :=
  fun _ top regs m r' m' =>
    let q := u128 (regs .x11) (regs .x12) / u128 (regs .x13) (regs .x14)
    m'.getMem (regs .x10) = q.truncate 64 ∧ m'.getMem (regs .x10 + 8#64) = (q >>> 64).truncate 64 ∧
    r' .x8 = regs .x8 ∧ r' .x2 = top ∧
    ∀ a, a ≠ regs .x10 → a ≠ regs .x10 + 8#64 → a ≠ regs .x10 + 16#64 → a ≠ regs .x10 + 24#64 →
      m'.getMem a = m.getMem a

/-- `__udivti3(a, b)`: the 128-bit quotient in `a0` and `a1`, from `u128_div_rem`'s contract. -/
theorem udivti3_contract (hdiv : rvIsa.Contract (liftProg fns) sp1Ctx 154 DivPre DivPost) :
    rvIsa.Contract (liftProg fns) sp1Ctx 155
      (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ regs .x13 ++ regs .x12 ≠ 0#128)
      (fun _ top regs _ r' _ =>
        let q := u128 (regs .x10) (regs .x11) / u128 (regs .x12) (regs .x13)
        r' .x10 = q.truncate 64 ∧ r' .x11 = (q >>> 64).truncate 64 ∧ r' .x2 = top) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hb⟩ hk
  lsym f155_eq with [hra, hsp, hb, DivPre, DivPost] using [hdiv]
  apply hk; simp [lsym_simp]

end Cases.Hardening.Guest
