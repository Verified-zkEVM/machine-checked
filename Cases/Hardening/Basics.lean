import Cases.Hardening.Gen.Basics
import LprogRiscV.Lsym

namespace Cases.Hardening.Basics

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift
open Cases.Hardening.Gen.Basics

/-- `max2`: the greater, signed. -/
theorem max2_spec {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (regs : Reg → BitVec 64) (m : MachineState)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top)
    (hpost : ∀ r' m', r' .x10 = (if (regs .x11).slt (regs .x10) then regs .x10 else regs .x11) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨1, 0, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq with [hra, hsp]
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
