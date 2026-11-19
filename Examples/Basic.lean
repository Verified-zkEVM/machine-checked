/-
  Examples.Basic

  The three functions of `Examples/src/c/basic.c`, compiled by clang to `Examples/elf/basic.elf`:
  straight-line code, a branch and a loop.

  * `add3(a, b, c)`: the sum.
  * `max_u64(a, b)`: the greater, unsigned.
  * `sum_to(n)`: the C is a loop adding `n`, `n - 1`, …, `1`. clang has no loop left: it computes
    `n + (n - 1)² - (n - 1)(n - 2) / 2`, the product in 128 bits (`mul`, `mulhu`) so that its half
    is exact. The specification is the sum (`sumTo`, with `sumTo_eq` for its closed form), and
    `sum_to_arith` is the arithmetic that takes the machine's expression to it.

  Each has its contract at Lprog, proved with `lsym`, and the same statement over riscv-zkvm's
  machine (`_correct`).
-/

import Examples.Gen.Basic
import Examples.Kit

namespace Examples.Basic

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Gen.Basic

theorem hok : ProgOk fns := by decide

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
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode add3_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `max_u64(a, b)`: the greater, unsigned; every other register and the memory kept. -/
theorem max_u64_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = (if regs .x11 < regs .x10 then regs .x10 else regs .x11) ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp]
  · exact hk _ _ ⟨by simp [hc], fun _ _ => rfl, rfl⟩
  · exact hk _ _ ⟨by simp [lsym_simp, BitVec.not_lt.mpr hc], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`max_u64` on the machine.** -/
theorem max_u64_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (if s.getReg .x11 < s.getReg .x10 then s.getReg .x10 else s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x1000c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode max_u64_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h10

/-- The sum `n + (n - 1) + … + 1`, as the loop of `sum_to` adds it. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- Twice the sum is `n (n + 1)`. -/
theorem two_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo]; grind

/-- **The closed form** of the sum. -/
theorem sumTo_eq (n : Nat) : sumTo n = n * (n + 1) / 2 := by
  have := two_sumTo n; omega

/-- Half of a 128-bit value, in 64 bits, from its two halves. -/
theorem half_prod (p : BitVec 128) :
    (p.setWidth 64 >>> 1) ||| ((p >>> 64).setWidth 64 <<< 63) = (p >>> 1).setWidth 64 := by
  bv_decide

/-- What `mul`, `mulhu` and the two shifts compute: half of the full product, in 64 bits. -/
theorem half_mul (a b : Word) :
    ((a * b) >>> 1) ||| ((a.setWidth 128 * b.setWidth 128) >>> 64).setWidth 64 <<< 63 =
      BitVec.ofNat 64 (a.toNat * b.toNat / 2) := by
  have e : a * b = (a.setWidth 128 * b.setWidth 128).setWidth 64 := by
    rw [BitVec.setWidth_mul _ _ (by decide)]; simp
  rw [e, half_prod]
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  have : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by decide
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 128),
    Nat.mod_eq_of_lt this]

/-- The identity clang uses: `n + (n - 1)²` is the sum to `n` and half of `(n - 1)(n - 2)`. -/
theorem tri_split (k : Nat) : (k + 1) + k * k = sumTo (k + 1) + k * (k - 1) / 2 := by
  cases k with
  | zero => rfl
  | succ j =>
    have h1 := two_sumTo (j + 2); have h2 := two_sumTo j
    have h3 : (j + 1) * (j + 1 - 1) / 2 = sumTo j := by
      rw [Nat.add_sub_cancel, Nat.mul_comm, ← h2]; omega
    rw [h3]; grind

/-- **The machine's expression is the sum**, for `x ≠ 0`. At `x = 1` the factor `x - 2` wraps to
    `2^64 - 1`, against `x - 1 = 0`. -/
theorem sum_to_arith (x : Word) (hx : x ≠ 0#64) :
    x + ((x + 18446744073709551615#64) * (x + 18446744073709551615#64) +
      -(((x + 18446744073709551615#64) * (x + 18446744073709551614#64)) >>> 1 |||
        BitVec.setWidth 64 ((BitVec.setWidth 128 (x + 18446744073709551615#64) *
          BitVec.setWidth 128 (x + 18446744073709551614#64)) >>> 64) <<< 63)) =
      BitVec.ofNat 64 (sumTo x.toNat) := by
  rw [half_mul]
  obtain ⟨k, hk⟩ : ∃ k, x.toNat = k + 1 := ⟨x.toNat - 1, by bv_omega⟩
  have ha : (x + 18446744073709551615#64).toNat = k := by bv_omega
  have hab : (x + 18446744073709551615#64).toNat * (x + 18446744073709551614#64).toNat = k * (k - 1) := by
    rw [ha]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; exact (Nat.zero_mul _).trans (Nat.zero_mul _).symm
    · have hb : (x + 18446744073709551614#64).toNat = k - 1 := by bv_omega
      rw [hb]
  have hxe : BitVec.ofNat 64 (k + 1) = x := BitVec.eq_of_toNat_eq (by rw [hk, BitVec.toNat_ofNat]; omega)
  have hae : BitVec.ofNat 64 k = x + 18446744073709551615#64 :=
    BitVec.eq_of_toNat_eq (by rw [ha, BitVec.toNat_ofNat]; omega)
  rw [hab, hk]
  have h := congrArg (BitVec.ofNat 64) (tri_split k)
  rw [BitVec.ofNat_add (k + 1) (k * k), BitVec.ofNat_add (sumTo (k + 1)), BitVec.ofNat_mul, hxe, hae] at h
  generalize BitVec.ofNat 64 (k * (k - 1) / 2) = t at h ⊢
  generalize BitVec.ofNat 64 (sumTo (k + 1)) = s at h ⊢
  generalize (x + 18446744073709551615#64) * (x + 18446744073709551615#64) = q at h ⊢
  bv_decide

/-- `sum_to(n)`: the sum `n + (n - 1) + … + 1` (modulo `2^64`); every register but `x10`..`x13`
    and the memory kept. -/
theorem sum_to_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = BitVec.ofNat 64 (sumTo (regs .x10).toNat) ∧
      (∀ r, r ∉ [Reg.x10, .x11, .x12, .x13] → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq with [hra, hsp]
  · exact hk _ _ ⟨by simp [hc, sumTo], fun _ _ => rfl, rfl⟩
  · refine hk _ _ ⟨?_, fun r h => ?_, rfl⟩
    · simp only [lsym_simp]; exact sum_to_arith _ hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      simp [lsym_simp, h]

/-- **`sum_to` on the machine.** -/
theorem sum_to_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10018#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (sumTo (s.getReg .x10).toNat) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x10018#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sum_to_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h10

end Examples.Basic
