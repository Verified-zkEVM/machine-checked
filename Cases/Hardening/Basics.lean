import Cases.Hardening.Gen.Basics
import LprogRiscV.Lsym

namespace Cases.Hardening.Basics

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift
open Cases.Hardening.Gen.Basics

theorem add3_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = regs .x10 + regs .x11 + regs .x12 → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f0_eq with [hra, hsp]
  all_goals (apply hpost; simp_all [lsym_simp]; try bv_decide)

/-- `max2`: the greater, signed. -/
theorem max2_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = (if (regs .x11).slt (regs .x10) then regs .x10 else regs .x11) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨1, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq with [hra, hsp]
  all_goals (apply hpost; simp_all [lsym_simp]; try bv_omega)

/-- `umax2`: the greater, unsigned. -/
theorem umax2_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = (if regs .x11 < regs .x10 then regs .x10 else regs .x11) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨2, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f2_eq with [hra, hsp]
  all_goals (apply hpost; simp_all [lsym_simp]; try bv_omega)

/-- `clamp`: `x` within `[lo, hi]`, signed, when `lo ≤ hi`. -/
theorem clamp_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top) (hle : (regs .x11).sle (regs .x12))
    (hpost : ∀ r' m', r' .x10 = (if (regs .x10).slt (regs .x11) then regs .x11
        else if (regs .x12).slt (regs .x10) then regs .x12 else regs .x10) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨3, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f3_eq with [hra, hsp]
  all_goals (apply hpost; simp_all [lsym_simp]; try bv_decide)

/-- The sum of the first `k` doublewords from `p`. -/
def sumMem (m : MachineState) (p : Word) : Nat → Word
  | 0 => 0
  | k + 1 => sumMem m p k + m.getMem (p + BitVec.ofNat 64 (8 * k))

theorem sum_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (p : Word) (n : Nat) (hn : 8 * n < 2 ^ 64)
    (hpost : ∀ r' m', r' .x10 = sumMem m p n → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64), n - j = k → j < n →
      regs .x12 = p + BitVec.ofNat 64 (8 * j) → regs .x11 = p + BitVec.ofNat 64 (8 * n) →
      regs .x10 = sumMem m p j → regs .x1 = ret → regs .x2 = top →
      LSafeN fns G N Q ⟨⟨4, 10, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ hk hj; omega
  | succ k ih =>
    intro j regs hk hj h12 h11 h10 hra hsp
    lsym f4_eq stop [10] with [h12, h11, h10, hra, hsp]
    · -- the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · obtain rfl : n = j + 1 := by omega
          simp only [lsym_addr] at hc; simp at hc
      apply ih (j + 1) _ (by omega) hlt
      all_goals simp [lsym_simp, lsym_addr, sumMem, h11, hra, hsp, BitVec.add_comm]
    · -- the exit
      apply hpost
      have : j + 1 = n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exfalso
          have := congrArg BitVec.toNat hc
          simp [BitVec.toNat_add, BitVec.toNat_ofNat] at this
          omega
        · omega
      subst this
      simp [lsym_simp, sumMem, BitVec.add_comm]

/-- **`sum(p, n)`**: the sum of the `n` doublewords from `p`. -/
theorem sum_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState) (p : Word) (n : Nat)
    (hn : 8 * n < 2 ^ 64) (hp : regs .x10 = p) (hnr : regs .x11 = BitVec.ofNat 64 n)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = sumMem m p n → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨4, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f4_eq stop [10] with [hp, hnr, hra, hsp]
  · -- no doublewords
    have hz : n = 0 := by
      have := congrArg BitVec.toNat hc; simp at this; omega
    subst hz
    apply hpost; simp [lsym_simp, sumMem]
  · -- the loop, from its first doubleword
    have hpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hc
      · exact h
    apply sum_loop m p n hn hpost n 0 _ (by omega) hpos
    all_goals simp [lsym_simp, sumMem, hra, hsp]

/-- **`count_down(x)`**: the number of bits of `x` (the loop `while (x) { x >>= 1; k++; }`,
    which clang compiles to a population count of the bits below the highest). -/
theorem count_down_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 ≤ 64#64 ∧ regs .x10 >>> r' .x10 = 0#64 ∧
        (r' .x10 = 0#64 ∨ regs .x10 >>> (r' .x10 - 1#64) ≠ 0#64) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨5, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f5_eq with [hra, hsp]
  all_goals (apply hpost; simp only [lsym_simp] at *; bv_decide)

end Cases.Hardening.Basics
