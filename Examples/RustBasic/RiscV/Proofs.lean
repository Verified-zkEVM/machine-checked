/-
  Examples.RustBasic.RiscV.Proofs

  The functions of `Examples/src/rust/basic.rs`, compiled by rustc to `Examples/elf/rustbasic.elf`:
  arithmetic, a branch and two loops. (The panic handler, function 0, is a jump to itself and is
  not called by any of them.)

  * `add3(a, b, c)`: the sum.
  * `max_u64(a, b)`: the greater, unsigned.
  * `gcd(a, b)`: Euclid's algorithm with `remu`; the result is `wgcd`, `Nat.gcd` as a word. The loop is entered
    with `b ≠ 0` and replaces `(a, b)` by `(b, a % b)`: its lemma is by strong induction on `b`.
    `remu` by zero is never reached.
  * `sum_slice(xs)`: the sum, wrapping, of the words of a slice (a pointer and a length). The
    slice is a list of words in memory (`WordsAt`), the result its sum (`wsum`). The loop
    counts the byte length down and is by induction on the words left.

  Each has its contract at Lprog, proved with `lsym`, and the same statement over riscv-zkvm's
  machine (`_correct`).
-/

import Examples.RustBasic.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.RustBasic.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.RustBasic.RiscV.Image

theorem hok : ProgOk fns := by decide

/-- `add3(a, b, c)`: the sum, every other register and the memory kept. -/
theorem add3_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp]
  apply hk
  exact ⟨by simp only [lsym_simp]; ac_rfl, fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`add3` on the machine.** -/
theorem add3_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10004#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x10004#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode add3_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h10

/-- `max_u64(a, b)`: the greater, unsigned; every other register and the memory kept. -/
theorem max_u64_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = umax (regs .x10) (regs .x11) ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f3_eq with [hra, hsp]
  · exact hk _ _ ⟨by simp [umax, hc], fun _ _ => rfl, rfl⟩
  · exact hk _ _ ⟨by simp [lsym_simp, umax, BitVec.not_lt.mpr hc], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`max_u64` on the machine.** -/
theorem max_u64_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10028#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = umax (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[3]? = some fn ∧ fn.base = 0x10028#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode max_u64_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h10

/-- The registers `gcd` may change. -/
def gcdClobbered : List Reg := [.x10, .x11, .x12]

/-- **Euclid's loop**, at its head with a second argument that is not zero: by strong induction
    on that argument. -/
theorem gcd_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) :
    ∀ n (regs : Reg → Word), (regs .x11).toNat = n → regs .x11 ≠ 0#64 →
      regs .x1 = ret → regs .x2 = top →
      (∀ r' m', r' .x10 = wgcd (regs .x10) (regs .x11) ∧
        (∀ r, r ∉ gcdClobbered → r' r = regs r) ∧ m' = m → LSafeN fns G N Q ⟨rest, r', m'⟩) →
      LSafeN fns G N Q ⟨⟨2, 2, ret, top⟩ :: rest, regs, m⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro regs hn hb hra hsp hk
    lsym f2_eq stop [2] with [hra, hsp, hb]
    · -- the remainder is not zero: once more, with it as the second argument
      have hlt : (regs .x10 % regs .x11).toNat < n := by
        rw [BitVec.toNat_umod, ← hn]; exact Nat.mod_lt _ (by bv_omega)
      refine ih _ hlt _ (by simp [lsym_simp]) (by simpa [lsym_simp] using hc) (by simp [lsym_simp, hra])
        (by simp [lsym_simp, hsp]) fun r' m' ⟨h10, hf, hm⟩ => hk r' m' ⟨?_, fun r hr => ?_, hm⟩
      · rw [h10]; simp only [wgcd, lsym_simp, ↓reduceIte, BitVec.toNat_umod]
        rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
      · rw [hf r hr]
        simp only [gcdClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]
    · -- the remainder is zero: the second argument is the divisor
      refine hk _ _ ⟨?_, fun r hr => ?_, rfl⟩
      · have hz : (regs .x10).toNat % (regs .x11).toNat = 0 := by
          rw [← BitVec.toNat_umod, hc]; rfl
        simp only [wgcd, lsym_simp, ↓reduceIte]
        rw [Nat.gcd_comm, Nat.gcd_rec, hz, Nat.gcd_zero_left, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · simp only [gcdClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]

/-- `gcd(a, b)`: the greatest common divisor; every register but `x10`..`x12` and the memory
    kept. -/
theorem gcd_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' =>
      r' .x10 = wgcd (regs .x10) (regs .x11) ∧
      (∀ r, r ∉ gcdClobbered → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq stop [2] with [hra, hsp]
  · -- the second argument is zero: the first is the divisor
    exact hk _ _ ⟨by simp [wgcd, hc], fun _ _ => rfl, rfl⟩
  · exact gcd_loop m _ regs rfl hc hra hsp hk

/-- **`gcd` on the machine.** -/
theorem gcd_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10010#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = wgcd (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x10010#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode gcd_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h10

/-- The words `xs` are in memory from `p`, eight bytes each, at addresses a load may read. -/
def WordsAt (m : MachineState) : Word → List Word → Prop
  | _, [] => True
  | p, x :: xs => isValidDwordAccessSp1 p = true ∧ m.getMem p = x ∧ WordsAt m (p + 8#64) xs

/-- The byte count, one word fewer. -/
theorem ofNat_sub8 (k : Nat) :
    BitVec.ofNat 64 (8 * (k + 1)) + 18446744073709551608#64 = BitVec.ofNat 64 (8 * k) := by
  rw [Nat.mul_add, BitVec.ofNat_add]
  generalize BitVec.ofNat 64 (8 * k) = y
  bv_decide

/-- The registers `sum_slice` may change. -/
def sumClobbered : List Reg := [.x10, .x11, .x12, .x13]

/-- **The loop of `sum_slice`**, at its head with the words `xs` left from `x12` and their byte
    count in `x11`: it adds them to `x10`. -/
theorem sum_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) :
    ∀ (xs : List Word) (regs : Reg → Word), xs ≠ [] → 8 * xs.length < 2 ^ 64 →
      WordsAt m (regs .x12) xs → regs .x11 = BitVec.ofNat 64 (8 * xs.length) →
      regs .x1 = ret → regs .x2 = top →
      (∀ r' m', r' .x10 = regs .x10 + wsum xs ∧
        (∀ r, r ∉ sumClobbered → r' r = regs r) ∧ m' = m → LSafeN fns G N Q ⟨rest, r', m'⟩) →
      LSafeN fns G N Q ⟨⟨4, 8, ret, top⟩ :: rest, regs, m⟩ := by
  intro xs
  induction xs with
  | nil => intro _ h; exact absurd rfl h
  | cons x tl ih =>
    intro regs _ hlen ⟨hv, hx, htl⟩ h11 hra hsp hk
    lsym f4_eq stop [8] with [hra, hsp, hv, h11]
    · -- words are left: the back edge
      rw [ofNat_sub8] at hc
      have hne : tl ≠ [] := by rintro rfl; exact hc rfl
      refine ih _ hne (by simp only [List.length_cons] at hlen; omega) (by simpa [lsym_simp] using htl)
        (by simp [lsym_simp, ofNat_sub8]) (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp])
        fun r' m' ⟨h10, hf, hm⟩ => hk r' m' ⟨?_, fun r hr => ?_, hm⟩
      · rw [h10]; simp only [lsym_simp, ↓reduceIte, hx, wsum]; ac_rfl
      · rw [hf r hr]
        simp only [sumClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]
    · -- none are left
      rw [ofNat_sub8] at hc
      have hnil : tl = [] := by
        have := congrArg BitVec.toNat hc
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [List.length_cons] at hlen; omega)] at this
        have h8 : 8 * tl.length = 0 := by simpa using this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      refine hk _ _ ⟨?_, fun r hr => ?_, rfl⟩
      · simp only [lsym_simp, ↓reduceIte, hx, wsum]; ac_rfl
      · simp only [sumClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]

/-- `sum_slice(xs)`, the slice as a pointer in `x10` and a length in `x11`: the sum of its words
    (modulo `2^64`); every register but `x10`..`x13` and the memory kept. -/
theorem sum_slice_contract (xs : List Word) : rvIsa.Contract (liftProg fns) sp1Ctx 4
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧ xs.length < 2 ^ 61 ∧
      regs .x11 = BitVec.ofNat 64 xs.length ∧ WordsAt m (regs .x10) xs)
    (fun _ _ regs m r' m' => r' .x10 = wsum xs ∧
      (∀ r, r ∉ sumClobbered → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hlen, h11, hw⟩ hk
  lsym f4_eq stop [8] with [hra, hsp, h11]
  · -- an empty slice
    have hnil : xs = [] := by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst hnil
    refine hk _ _ ⟨by simp [lsym_simp, wsum], fun r hr => ?_, rfl⟩
    simp only [sumClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [lsym_simp, hr]
  · -- the loop, from the first word and a sum of zero
    have hne : xs ≠ [] := by rintro rfl; exact hc rfl
    refine sum_loop m xs _ hne (by omega) (by simpa [lsym_simp] using hw)
      (by simp [lsym_simp]) (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp])
      fun r' m' ⟨h10, hf, hm⟩ => hk r' m' ⟨?_, fun r hr => ?_, hm⟩
    · rw [h10]; simp [lsym_simp]
    · rw [hf r hr]
      simp only [sumClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [lsym_simp, hr]

/-- **`sum_slice` on the machine.** -/
theorem sum_slice_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (xs : List Word) (hpc : s.pc = 0x10034#64) (hcode : Loaded fns s)
    (hlen : xs.length < 2 ^ 61) (h11 : s.getReg .x11 = BitVec.ofNat 64 xs.length)
    (hw : WordsAt s (s.getReg .x10) xs)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 → t.getReg .x10 = wsum xs →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[4]? = some fn ∧ fn.base = 0x10034#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode (sum_slice_contract xs)
    ⟨rfl, rfl, hlen, h11, hw⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h10

end Examples.RustBasic.RiscV
