import Examples.Rec.RiscV.Image
import Examples.Spec
import Examples.Kit

/-!
  # Recursion: `fib`

  `fib(n) = n < 2 ? n : fib(n - 1) + fib(n - 2)`, which clang compiles to a loop around one
  recursive call (the second becomes the loop). Its contract is proved by induction on `n`:
  the call inside the loop goes through the contract of a smaller argument (`using [hcall]`).
  The frame condition (memory at and above `sp` kept) is what lets a caller read back the
  registers it saved across the call.
-/

namespace Examples.Rec.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Rec.RiscV.Image

theorem hok : ProgOk fns := by decide

/-- From `ra = ret`, `sp = top` and `a0 = k`, with room for `k + 1` frames below `top`. -/
def FibPre (k : Nat) : Word → Word → (Reg → Word) → MachineState → Prop :=
  fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ regs .x10 = BitVec.ofNat 64 k ∧
    32 * (k + 1) ≤ top.toNat

/-- `fib k` in `a0`; `sp` and the registers the convention keeps, kept; memory at and above
    `top`, kept. -/
def FibPost (k : Nat) : Word → Word → (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop :=
  fun _ top regs m r' m' => r' .x10 = BitVec.ofNat 64 (fibN k) ∧ r' .x2 = top ∧
    r' .x8 = regs .x8 ∧ r' .x9 = regs .x9 ∧ r' .x18 = regs .x18 ∧
    ∀ a, top ≤ a → m'.getMem a = m.getMem a

theorem four_le {j : Nat} (hj : j < 2 ^ 63) (h2 : 2 ≤ j)
    (hc : 1#64 < BitVec.ofNat 64 j + 18446744073709551614#64) : 4 ≤ j := by bv_omega

theorem frame_le {top : Word} {k c : Nat} (htop : 32 * (k + 1) ≤ top.toNat) (h1 : 8 ≤ c) (h2 : c ≤ 32) :
    top + 18446744073709551584#64 ≤ top - BitVec.ofNat 64 c := by bv_omega

theorem above_le {top a : Word} {k : Nat} (htop : 32 * (k + 1) ≤ top.toNat) (ha : top ≤ a) :
    top + 18446744073709551584#64 ≤ a := by bv_omega

theorem sub_two {j : Nat} (hj : j < 2 ^ 63) (h2 : 2 ≤ j) :
    BitVec.ofNat 64 j + 18446744073709551614#64 = BitVec.ofNat 64 (j - 2) := by bv_omega

theorem sub_one {j : Nat} (hj : j < 2 ^ 63) (h1 : 1 ≤ j) :
    BitVec.ofNat 64 j + 18446744073709551615#64 = BitVec.ofNat 64 (j - 1) := by bv_omega

theorem sp_frame {top : Word} : top + 18446744073709551584#64 = top - 32#64 := by bv_omega

theorem room {top : Word} {j k : Nat} (htop : 32 * (k + 1) ≤ top.toNat) (hjk : j ≤ k) (h1 : 1 ≤ j) :
    32 * (j - 1 + 1) ≤ (top + -32#64).toNat := by bv_omega

theorem room2 {top : Word} {j k : Nat} (htop : 32 * (k + 1) ≤ top.toNat) (hjk : j ≤ k) (h2 : 2 ≤ j) :
    32 * (j - 2 + 1) ≤ (top + -32#64).toNat := by bv_omega

theorem fib_step (a b f : Word) : a + (f + -(b + a)) = f + -b := by bv_omega

theorem le_three {j : Nat} (hj : j < 2 ^ 63) (h2 : 2 ≤ j)
    (hc : BitVec.ofNat 64 j + 18446744073709551614#64 ≤ 1#64) : j ≤ 3 := by bv_omega

theorem cell_le {top : Word} {k : Nat} (htop : 32 * (k + 1) ≤ top.toNat) (c : Word)
    (hc : c = 18446744073709551608#64 ∨ c = 18446744073709551600#64 ∨ c = 18446744073709551592#64 ∨
      c = 18446744073709551584#64) :
    top + 18446744073709551584#64 ≤ top + c := by
  rcases hc with rfl | rfl | rfl | rfl <;> bv_omega

theorem exit_sum (j : Nat) (hj : 2 ≤ j) (h3 : j ≤ 3) (f : Word) :
    BitVec.ofNat 64 j + (18446744073709551614#64 +
      (BitVec.ofNat 64 (fibN (j - 1)) + (f + -BitVec.ofNat 64 (fibN j)))) = f := by
  obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
  · simp [fibN]; bv_omega
  · simp [fibN]; bv_omega

/-- An address at or above `top` is none of the frame's cells. -/
theorem above_ne {top a : Word} {k : Nat} (htop : 32 * (k + 1) ≤ top.toNat) (ha : top ≤ a) :
    a ≠ top + 18446744073709551608#64 ∧ a ≠ top + 18446744073709551600#64 ∧
      a ≠ top + 18446744073709551592#64 ∧ a ≠ top + 18446744073709551584#64 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem fib_loop (k : Nat) (_hk : k < 2 ^ 63)
    (ih : ∀ j < k, rvIsa.Contract (liftProg fns) sp1Ctx 0 (FibPre j) (FibPost j))
    {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    (m0 : MachineState) (regs0 : Reg → Word) (htop : 32 * (k + 1) ≤ top.toNat)
    (hpost : ∀ r' m', FibPost k ret top regs0 m0 r' m' → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ j (regs : Reg → Word) (m : MachineState), 2 ≤ j → j ≤ k →
      regs .x8 = BitVec.ofNat 64 j → regs .x9 = BitVec.ofNat 64 (fibN k) - BitVec.ofNat 64 (fibN j) →
      regs .x18 = 1#64 → regs .x2 = top - 32#64 →
      m.getMem (top - 8#64) = ret → m.getMem (top - 16#64) = regs0 .x8 →
      m.getMem (top - 24#64) = regs0 .x9 → m.getMem (top - 32#64) = regs0 .x18 →
      (∀ a, top ≤ a → m.getMem a = m0.getMem a) →
      LSafeN fns G N Q ⟨⟨0, 20, ret, top⟩ :: rest, regs, m⟩ := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ihj =>
  intro regs m hj2 hjk h8 h9 h18 h2 mra ms0 ms1 ms2 mhi
  have hcall := ih (j - 1) (by omega)
  have hj64 : j < 2 ^ 64 := by omega
  -- the cells of the frame, at and above the callee's `sp`
  lsym f0_eq stop [20] with [FibPre, FibPost, h8, h9, h18, h2] using [hcall]
  · -- the precondition of the call
    refine ⟨by simp [lsym_simp], ?_, ?_, ?_⟩
    · simp [lsym_simp]
    · simp [lsym_simp, sub_one (j := j) (by omega) (by omega)]
    · simp only [lsym_simp, h2]
      exact room htop hjk (by omega)
  · -- the back edge
    obtain ⟨r10, r2, r8, r9, r18, rm⟩ := hret
    have hj4 : 4 ≤ j := four_le (by omega) hj2 hc
    -- the frame's cells are at and above the callee's `sp`
    have keep : ∀ c : Nat, 8 ≤ c → c ≤ 32 → m'.getMem (top - BitVec.ofNat 64 c) = m.getMem (top - BitVec.ofNat 64 c) :=
      fun c h1 h2 => rm _ (frame_le htop h1 h2)
    apply ihj (j - 2) (by omega) _ m' (by omega) (by omega)
    · simp [lsym_simp, sub_two (j := j) (by omega) hj2]
    · have hf : fibN j = fibN (j - 2) + fibN (j - 1) := by
        rw [show j = (j - 2) + 2 by omega, fibN]; simp [Nat.add_comm]
      simp only [lsym_simp, hf, BitVec.ofNat_add]
      exact fib_step _ _ _
    · simp [lsym_simp, r18]
    · simp [lsym_simp, r2]
    · rw [keep 8 (by omega) (by omega)]; exact mra
    · rw [keep 16 (by omega) (by omega)]; exact ms0
    · rw [keep 24 (by omega) (by omega)]; exact ms1
    · rw [keep 32 (by omega) (by omega)]; exact ms2
    · intro a ha; rw [rm a (above_le htop ha)]; exact mhi a ha
  all_goals
    obtain ⟨r10, r2, r8, r9, r18, rm⟩ := hret
    have h3 : j ≤ 3 := le_three (by omega) hj2 hc
    simp only [lsym_addr] at mra ms0 ms1 ms2
    have keep := fun c hc => rm _ (cell_le htop c hc)
  · simp only [lsym_simp, lsym_addr]; rw [keep _ (by decide)]; exact mra
  · simp only [lsym_simp, lsym_addr]
  · apply hpost
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · simp only [lsym_simp, lsym_addr]; exact exit_sum j hj2 h3 _
    · simp only [lsym_simp, lsym_addr]
    · simp only [lsym_simp, lsym_addr]; rw [keep _ (by decide)]; exact ms0
    · simp only [lsym_simp, lsym_addr]; rw [keep _ (by decide)]; exact ms1
    · simp only [lsym_simp, lsym_addr]; exact ms2
    · rw [rm a (above_le htop ha)]; exact mhi a ha

/-- **`fib`'s contract**: `fib k` in `a0`, for `k < 2 ^ 63` with room for `k + 1` frames, by
    induction on `k`: the recursive call is on a smaller argument. -/
theorem fib_contract : ∀ k, k < 2 ^ 63 →
    rvIsa.Contract (liftProg fns) sp1Ctx 0 (FibPre k) (FibPost k) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro hk G N Q ret top rest regs m ⟨hra, hsp, h10, htop⟩ hk'
  have hk64 : k < 2 ^ 64 := by omega
  lsym f0_eq stop [20] with [hra, hsp, h10]
  · -- `k < 2`: `fib k` is `k`
    have h2 : k < 2 := by omega
    apply hk'
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      all_goals simp [lsym_simp, fibN]
    · simp [lsym_simp]
    · simp [lsym_simp]
    · simp [lsym_simp]
    · simp [lsym_simp]
    · obtain ⟨n1, n2, n3, n4⟩ := above_ne htop ha
      simp [lsym_simp, MachineState.getMem, MachineState.setMem, n1, n2, n3, n4]
  · -- the loop, from `k`
    have h2 : 2 ≤ k := by omega
    apply fib_loop k hk (fun j hj => ih j hj (by omega)) m regs htop hk' k _ _ h2 (Nat.le_refl k)
    all_goals simp [lsym_simp, lsym_addr, MachineState.getMem, MachineState.setMem]
    intro a ha
    obtain ⟨n1, n2, n3, n4⟩ := above_ne htop ha
    simp [n1, n2, n3, n4]

/-- **`fib` on the machine**: `fib k` in `a0` for `a0 = k < 2 ^ 63` with room for `k + 1`
    32-byte frames below `sp`; `sp`, `s0`, `s1`, `s2` and the memory at and above `sp` kept. -/
theorem fib_correct {G : MachineState → Prop} {N : Nat} {P : Prop} (s : MachineState) (k : Nat)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s) (hk : k < 2 ^ 63)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 k) (hroom : 32 * (k + 1) ≤ (s.getReg .x2).toNat)
    (hcont : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (fibN k) → t.getReg .x2 = s.getReg .x2 →
      t.getReg .x8 = s.getReg .x8 → t.getReg .x9 = s.getReg .x9 → t.getReg .x18 = s.getReg .x18 →
      (∀ a, s.getReg .x2 ≤ a → t.getMem a = s.getMem a) → SafeN G N P t) :
    SafeN G N P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode (fib_contract k hk)
    ⟨rfl, rfl, by simpa [regsOf] using h10, by simpa [regsOf] using hroom⟩ ?_
  rintro t r' m' hag hpc' ⟨r10, r2, r8, r9, r18, rm⟩
  simp only [regsOf] at r2 r8 r9 r18 rm
  refine hcont t hpc' ?_ ?_ ?_ ?_ ?_ fun a ha => ?_
  · rw [← hag.regs, getReg_ofParts]; simpa using r10
  · rw [← hag.regs, getReg_ofParts]; simpa using r2
  · rw [← hag.regs, getReg_ofParts]; simpa using r8
  · rw [← hag.regs, getReg_ofParts]; simpa using r9
  · rw [← hag.regs, getReg_ofParts]; simpa using r18
  · rw [← hag.mem]; exact rm a (by simpa using ha)

end Examples.Rec.RiscV
