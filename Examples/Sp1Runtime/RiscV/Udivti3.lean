import Examples.Sp1Runtime.RiscV.Image
import MachineChecked.RiscV.Lift.Contract
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

  `udivti3_contract` is the contract at Lprog, `udivti3_correct` the same statement over
  riscv-zkvm's machine; both take `u128_div_rem`'s contract as a hypothesis.
-/

namespace Examples.Sp1Runtime.RiscV.Udivti3

open RiscvZkvm.Rv64 MachineChecked.RiscV Lprog Lprog.RiscV Lprog.RiscV.Machine
  MachineChecked.RiscV.Lift
open Examples.Sp1Runtime.RiscV.Image

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

/-- **`__udivti3(a, b)` on the machine**, for a divisor that is not zero: it returns with the
    128-bit quotient `a / b` in `a0` (low half) and `a1` (high half), and `sp` as it was.

    This is NOT a proof of `__udivti3` alone: `u128_div_rem`'s contract (`hdiv`) is assumed,
    not proved. `u128_div_rem` is not kept here, and nothing in this repository proves it. -/
theorem udivti3_correct (hdiv : rvIsa.Contract (liftProg fns) sp1Ctx 154 DivPre DivPost)
    {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x7800ed88#64) (hcode : Loaded fns s)
    (hb : u128 (s.getReg .x12) (s.getReg .x13) ≠ 0#128)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (u128 (s.getReg .x10) (s.getReg .x11) /
        u128 (s.getReg .x12) (s.getReg .x13)).truncate 64 →
      t.getReg .x11 = ((u128 (s.getReg .x10) (s.getReg .x11) /
        u128 (s.getReg .x12) (s.getReg .x13)) >>> 64).truncate 64 →
      t.getReg .x2 = s.getReg .x2 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hbase⟩ : ∃ fn, fns[155]? = some fn ∧ fn.base = 0x7800ed88#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hbase.symm) hcode (udivti3_contract hdiv)
    ⟨rfl, rfl, by simpa [regsOf, u128] using hb⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, h11, h2⟩
  have e : ∀ r, r ≠ .x0 → t.getReg r = r' r := fun r hr => by
    rw [← hag.regs, getReg_ofParts, ite_eq_right hr]
  have g : ∀ r, regsOf s r = s.getReg r := fun r => by simp [regsOf]
  refine hk t hpc' ?_ ?_ ?_
  · rw [e _ (by decide), h10]; simp only [g]
  · rw [e _ (by decide), h11]; simp only [g]
  · rw [e _ (by decide), h2]

end Examples.Sp1Runtime.RiscV.Udivti3
