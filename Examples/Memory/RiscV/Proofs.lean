/-
  Examples.Memory.RiscV.Proofs

  `src/c/memory.c`, compiled by clang (`elf/memory.elf`): memory, a loop over an array, and a
  call with a stack frame. Four functions, each with its contract at Lprog, proved with `lsym`,
  and the same statement over riscv-zkvm's machine, through `SafeN.of_isa_contract`.

  * `swap(a, b)` exchanges the doublewords at `a` and `b`, whether or not `a = b`, and leaves
    every other doubleword of memory as it was.
  * `sum_array(p, n)` returns the wrapping sum of the `n` doublewords from `p` (`wsum`), for
    `n < 2 ^ 61`, memory unchanged. The loop walks a pointer to the end pointer `p + 8 * n`;
    it is a lemma of its own (`sum_array_loop`), by induction on the doublewords left.
  * `max2(a, b)` returns the unsigned maximum (`umax`), and keeps every other register and the
    memory.
  * `max3(a, b, c)` returns `umax (umax a b) c`: a call of `max2` with `ra` and `s0` saved in a
    16-byte frame, then a tail call of it through `t1`. It is proved through `max2_contract`,
    not through `max2`'s body. It keeps every register but `a0`, `a1` and `t1`, and every
    doubleword of memory but the two of its frame.

  No precondition asks that an address be valid. A load or store whose address is not valid (or
  a store onto code) traps, and a machine that traps does not return, so a contract, which
  speaks of the states the function returns in, holds of it. `lsym` gives each access's check
  as a hypothesis on the path after it.
-/

import Examples.Memory.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Memory.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Memory.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-! ## `swap` -/

/-- `swap(a, b)`: the doublewords at `a` and `b` exchanged, whether or not `a = b`; every other
    doubleword of memory unchanged. -/
theorem swap_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m _ m' => m'.getMem (regs .x10) = m.getMem (regs .x11) ∧
      m'.getMem (regs .x11) = m.getMem (regs .x10) ∧
      (∀ c, c ≠ regs .x10 → c ≠ regs .x11 → m'.getMem c = m.getMem c)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  apply hk
  refine ⟨?_, ?_, ?_⟩
  · simp only [lsym_simp, MachineState.getMem, MachineState.setMem]
    split <;> simp_all
  · simp [lsym_simp, MachineState.getMem, MachineState.setMem]
  · intro c h1 h2; simp [lsym_simp, MachineState.getMem, MachineState.setMem, h1, h2]

/-- **`swap` on the machine.** -/
theorem swap_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getMem (s.getReg .x10) = s.getMem (s.getReg .x11) →
      t.getMem (s.getReg .x11) = s.getMem (s.getReg .x10) →
      (∀ c, c ≠ s.getReg .x10 → c ≠ s.getReg .x11 → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode swap_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h1, h2, h3⟩
  simp only [regsOf] at h1 h2 h3
  refine hk t hpc' ?_ ?_ fun c hc1 hc2 => ?_
  · rw [← hag.mem]; simpa using h1
  · rw [← hag.mem]; simpa using h2
  · rw [← hag.mem]; exact h3 c (by simpa using hc1) (by simpa using hc2)

/-! ## `sum_array` -/

/-- The wrapping sum of the first `k` doublewords from `p`. -/
def wsum (m : MachineState) (p : Word) : Nat → Word
  | 0 => 0
  | k + 1 => wsum m p k + m.getMem (p + BitVec.ofNat 64 (8 * k))

/-- The shift that scales an index to a byte offset, as a multiplication. -/
theorem shl3 (x : Word) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- **The loop of `sum_array`**, at its head, with `j < n` doublewords summed. -/
theorem sum_array_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (p : Word) (n : Nat) (hn : n < 2 ^ 61)
    (hpost : ∀ r' m', r' .x10 = wsum m p n → m' = m → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64), n - j = k → j < n →
      regs .x12 = p + BitVec.ofNat 64 (8 * j) → regs .x11 = p + BitVec.ofNat 64 (8 * n) →
      regs .x10 = wsum m p j → regs .x1 = ret → regs .x2 = top →
      LSafeN fns G N Q ⟨⟨1, 10, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ hk hj; omega
  | succ k ih =>
    intro j regs hk hj h12 h11 h10 hra hsp
    lsym f1_eq stop [10] with [h12, h11, h10, hra, hsp]
    · -- the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · obtain rfl : n = j + 1 := by omega
          simp only [lsym_addr] at hc; simp at hc
      apply ih (j + 1) _ (by omega) hlt
      all_goals simp [lsym_simp, lsym_addr, wsum, h11, hra, hsp, BitVec.add_comm]
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
      · simp [lsym_simp, wsum, BitVec.add_comm]
      · rfl

/-- `sum_array(p, n)`: the wrapping sum of the `n` doublewords from `p`, for `n < 2 ^ 61` (so
    that `8 * n` does not wrap); memory unchanged. -/
theorem sum_array_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ (regs .x11).toNat < 2 ^ 61)
    (fun _ _ regs m r' m' => r' .x10 = wsum m (regs .x10) (regs .x11).toNat ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hn⟩ hk
  lsym f1_eq stop [10] with [hra, hsp]
  · -- no doublewords
    apply hk
    simp [lsym_simp, hc, wsum]
  · -- the loop, from its first doubleword
    have hpos : 0 < (regs .x11).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x11).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hc
      · exact h
    apply sum_array_loop m (regs .x10) _ hn (fun r' m' h1 h2 => hk r' m' ⟨h1, h2⟩) _ 0 _ rfl hpos
    all_goals simp [lsym_simp, wsum, hra, hsp, shl3]

/-- **`sum_array` on the machine.** -/
theorem sum_array_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10014#64) (hcode : Loaded fns s) (hn : (s.getReg .x11).toNat < 2 ^ 61)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = wsum s (s.getReg .x10) (s.getReg .x11).toNat →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x10014#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sum_array_contract
    ⟨rfl, rfl, by simpa [regsOf] using hn⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## `max2` and `max3` -/

/-- `max2(a, b)`: the unsigned maximum; every other register and the memory kept. -/
theorem max2_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = umax (regs .x10) (regs .x11) ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq with [hra, hsp]
  · apply hk
    exact ⟨by simp [umax, hc], fun _ _ => rfl, rfl⟩
  · apply hk
    exact ⟨by simp [lsym_simp, umax, BitVec.not_lt.mpr hc], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`max2` on the machine.** -/
theorem max2_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10044#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = umax (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x10044#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode max2_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `max3(a, b, c)`: the unsigned maximum of the three, through `max2`'s contract. Every register
    but `a0`, `a1` and `t1` is kept (`ra` and `s0` by the frame), and every doubleword of memory
    but the two of the frame, below the stack pointer. -/
theorem max3_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ top regs m r' m' => r' .x10 = umax (umax (regs .x10) (regs .x11)) (regs .x12) ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x6 → r' r = regs r) ∧
      (∀ c, c ≠ top - 8#64 → c ≠ top - 16#64 → m'.getMem c = m.getMem c)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f3_eq with [hra, hsp] using [max2_contract]
  apply hk
  obtain ⟨h10, hr, rfl⟩ := hret
  obtain ⟨h10', hr', -⟩ := hret_1
  refine ⟨by rw [h10, h10'], fun r h1 h2 h3 => ?_, fun c h1 h2 => ?_⟩
  · rw [hr r h1, hr' r h1]
    repeat' split
    all_goals simp_all
  · have e8 : top + 18446744073709551608#64 = top - 8#64 := by bv_omega
    have e16 : top + 18446744073709551600#64 = top - 16#64 := by bv_omega
    simp [MachineState.getMem, MachineState.setMem, e8, e16, h1, h2]

/-- **`max3` on the machine.** -/
theorem max3_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10050#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = umax (umax (s.getReg .x10) (s.getReg .x11)) (s.getReg .x12) →
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x6 → t.getReg r = s.getReg r) →
      (∀ c, c ≠ s.getReg .x2 - 8#64 → c ≠ s.getReg .x2 - 16#64 → t.getMem c = s.getMem c) →
      SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[3]? = some fn ∧ fn.base = 0x10050#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode max3_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hr, hmem⟩
  refine hk t hpc' ?_ (fun r h1 h2 h3 => ?_) fun c h1 h2 => ?_
  · rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10
  · rw [← hag.regs, getReg_ofParts, hr r h1 h2 h3]; simp only [regsOf]
    split
    · subst r; rfl
    · rfl
  · rw [← hag.mem]; exact hmem c h1 h2

end Examples.Memory.RiscV
