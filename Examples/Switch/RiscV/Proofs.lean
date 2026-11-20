/-
  Examples.Switch.RiscV.Proofs

  `src/c/switch.c`, compiled by clang (`elf/switch.elf`): `classify(k)`, a dense `switch` over
  `k = 0..7` returning `10, 21, 32, 43, 54, 65, 76, 87`, and `-1` otherwise.

  The `switch` was written to be compiled to a jump table, but clang saw that the values are
  `10 + 11 k` and compiled it to straight-line code with no table and no indirect jump:
  `sltiu` for `k < 8`, a multiply and add, and a mask that turns the result into `-1` when
  `k ≥ 8`. There is no `.rodata`, so the precondition says nothing of memory. The
  specification is the C's table of values (`classifySpec`), not the arithmetic.

  Its contract at Lprog, proved with `lsym`, and the same statement over riscv-zkvm's machine
  (`_correct`). `_start` is an endless loop, by design.
-/

import Examples.Switch.RiscV.Image
import Examples.Kit

namespace Examples.Switch.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Switch.RiscV.Image

theorem hok : ProgOk fns := by decide

/-- `classify(k)`, as the C's `switch` states it: `-1` is the word of all ones. -/
def classifySpec (k : Word) : Word :=
  match k.toNat with
  | 0 => 10#64 | 1 => 21#64 | 2 => 32#64 | 3 => 43#64
  | 4 => 54#64 | 5 => 65#64 | 6 => 76#64 | 7 => 87#64
  | _ => -1#64

/-- What clang computes is the table. -/
theorem classify_arith (k : Word) :
    (if k < 8#64 then 1#64 else 0#64) + 18446744073709551615#64 ||| k * 11#64 + 10#64 =
      classifySpec k := by
  unfold classifySpec
  by_cases h : k < 8#64
  · have : k = 0#64 ∨ k = 1#64 ∨ k = 2#64 ∨ k = 3#64 ∨ k = 4#64 ∨ k = 5#64 ∨ k = 6#64 ∨
        k = 7#64 := by bv_omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have hk : 8 ≤ k.toNat := by bv_omega
    have e : (if k < 8#64 then 1#64 else 0#64) + 18446744073709551615#64 ||| k * 11#64 + 10#64 =
        -1#64 := by
      rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
      generalize k * 11#64 + 10#64 = y
      bv_decide
    rw [e]
    split <;> first | omega | rfl

/-- `classify(k)`: `classifySpec k` in `a0`, the memory kept. -/
theorem classify_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = classifySpec (regs .x10) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  refine hk _ _ ⟨?_, rfl⟩
  rw [← classify_arith]; simp [lsym_simp]

/-- **`classify` on the machine.** -/
theorem classify_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = classifySpec (s.getReg .x10) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode classify_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

end Examples.Switch.RiscV
