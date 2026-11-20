/-
  Examples.Arith.RiscV.Proofs

  # Arithmetic at its edges

  `src/c/arith.c`, compiled by clang (`elf/arith.elf`). Each function against what C says it
  computes, by `bv_decide` once `lsym` has stepped it: division and remainder by zero and at the
  one overflow, the high half of products, signed and not, a rotation, a count of the 1 bits, an
  absolute value without a branch. What is checked is the lift's meaning of `div`, `rem`,
  `divu`, `mulh`, `mulhu`, `sll`, `srl` and `sra`, against C's.

  Each has its contract at Lprog, proved with `lsym`, and the same statement over riscv-zkvm's
  machine (`_correct`). The result is in `a0`; the memory is kept.

  Not here: `add32`, `shl32`, `sra32` and `div32`, which clang compiles to the 32-bit word
  instructions `addw`, `sllw`, `sraw` and `divw`. riscv-zkvm's machine does not run them, so the
  `--proved` lift leaves the four functions out, and there is nothing to prove them against.
  `_start` is an endless loop, by design.
-/

import Examples.Arith.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Arith.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Arith.RiscV.Image

theorem hok : ProgOk fns := by decide

/-- What every function here asks: called from `ret`, with the stack at `top`. -/
def Called : Word → Word → (Reg → Word) → MachineState → Prop :=
  fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top

/-- What every function here gives: `f a0 a1` in `a0`, the memory kept. -/
def Gives (f : Word → Word → Word) :
    Word → Word → (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop :=
  fun _ _ regs m r' m' => r' .x10 = f (regs .x10) (regs .x11) ∧ m' = m

/-- From a contract of the shape `Called`/`Gives`, the statement over the machine. -/
theorem gives_correct {i : Nat} {f : Word → Word → Word} {base : Word}
    (hcon : rvIsa.Contract (liftProg fns) sp1Ctx i Called (Gives f))
    (hb : ∃ fn, fns[i]? = some fn ∧ fn.base = base)
    {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = base) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = f (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ := hb
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode hcon ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## Division and remainder -/

/-- `sdiv(a, b)`: `b == 0 ? 0 : a / b`, C's division, which rounds toward zero; the overflow
    `INT64_MIN / -1` (undefined in C) gives `INT64_MIN`, as RISC-V's `div` does. -/
def sdivSpec (a b : Word) : Word := if b = 0 then 0 else a.sdiv b

theorem sdiv_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0 Called (Gives sdivSpec) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  all_goals (refine hk _ _ ⟨?_, rfl⟩; simp only [sdivSpec, lsym_simp] at *; bv_decide)

/-- **`sdiv` on the machine.** -/
theorem sdiv_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = sdivSpec (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s :=
  gives_correct sdiv_contract ⟨_, rfl, rfl⟩ s hpc hcode hk

/-- `srem(a, b)`: `b == 0 ? a : a % b`, the remainder with the sign of the dividend. -/
def sremSpec (a b : Word) : Word := if b = 0 then a else a.srem b

theorem srem_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1 Called (Gives sremSpec) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f1_eq with [hra, hsp]
  all_goals (refine hk _ _ ⟨?_, rfl⟩; simp only [sremSpec, lsym_simp] at *; bv_decide)

/-- **`srem` on the machine.** -/
theorem srem_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1014#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = sremSpec (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s :=
  gives_correct srem_contract ⟨_, rfl, rfl⟩ s hpc hcode hk

/-- `udiv(a, b)`: `b == 0 ? 0 : a / b`, unsigned. -/
def udivSpec (a b : Word) : Word := if b = 0 then 0 else a / b

theorem udiv_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2 Called (Gives udivSpec) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq with [hra, hsp]
  all_goals (refine hk _ _ ⟨?_, rfl⟩; simp only [udivSpec, lsym_simp] at *; bv_decide)

/-- **`udiv` on the machine.** -/
theorem udiv_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1020#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = udivSpec (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s :=
  gives_correct udiv_contract ⟨_, rfl, rfl⟩ s hpc hcode hk

/-! ## The high half of products -/

/-- `mulhi(a, b)`: the high half of the unsigned 128-bit product. -/
def mulhiSpec (a b : Word) : Word := ((a.zeroExtend 128 * b.zeroExtend 128) >>> 64).truncate 64

theorem mulhi_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3 Called (Gives mulhiSpec) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f3_eq with [hra, hsp]
  -- the product is too wide for `bv_decide`: it is the same product, its factors swapped
  refine hk _ _ ⟨?_, rfl⟩; simp only [mulhiSpec, lsym_simp]; rw [BitVec.mul_comm]

/-- **`mulhi` on the machine.** -/
theorem mulhi_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1034#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = mulhiSpec (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s :=
  gives_correct mulhi_contract ⟨_, rfl, rfl⟩ s hpc hcode hk

/-- `smulhi(a, b)`: the high half of the signed 128-bit product. -/
def smulhiSpec (a b : Word) : Word :=
  ((a.signExtend 128 * b.signExtend 128).sshiftRight 64).truncate 64

theorem smulhi_contract : rvIsa.Contract (liftProg fns) sp1Ctx 4 Called (Gives smulhiSpec) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f4_eq with [hra, hsp]
  -- the lift shifts the product logically, C arithmetically: the low 64 bits after a shift
  -- by 64 are the same
  refine hk _ _ ⟨?_, rfl⟩; simp only [smulhiSpec, lsym_simp]; rw [BitVec.mul_comm]
  generalize BitVec.signExtend 128 (regs .x10) * BitVec.signExtend 128 (regs .x11) = p
  bv_decide

/-- **`smulhi` on the machine.** -/
theorem smulhi_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x103c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = smulhiSpec (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s :=
  gives_correct smulhi_contract ⟨_, rfl, rfl⟩ s hpc hcode hk

/-! ## A rotation -/

/-- `rotl(x, s)`: with `s` taken mod 64, `(x << s) | (x >> ((64 - s) & 63))`, as C states it, the
    shift amounts as words. -/
def rotlSpec (x s : Word) : Word :=
  x <<< (s &&& 63#64) ||| x >>> ((64#64 - (s &&& 63#64)) &&& 63#64)

theorem rotl_contract : rvIsa.Contract (liftProg fns) sp1Ctx 5 Called (Gives rotlSpec) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f5_eq with [hra, hsp]
  -- `(64 - (s & 63)) & 63` is `-s & 63`
  have e : (64#64 - (regs .x11 &&& 63#64)) &&& 63#64 = (0 - regs .x11) &&& 63#64 := by bv_decide
  refine hk _ _ ⟨?_, rfl⟩; rw [rotlSpec, e]; simp only [lsym_simp]
  simp [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_and, BitVec.toNat_neg]

/-- **`rotl` on the machine.** -/
theorem rotl_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x105c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = rotlSpec (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s :=
  gives_correct rotl_contract ⟨_, rfl, rfl⟩ s hpc hcode hk

/-! ## The 1 bits: `popcount`, Kernighan's loop -/

/-- The low bit of `a &&& b` is clear if one of theirs is. -/
theorem and_mod_two_zero {a b : Nat} (h : a % 2 = 0 ∨ b % 2 = 0) : (a &&& b) % 2 = 0 := by
  have h1 := Nat.testBit_and a b 0
  simp only [Nat.testBit_zero] at h1
  rcases Nat.mod_two_eq_zero_or_one (a &&& b) with hx | hx
  · exact hx
  · rcases h with h | h <;> simp [h, hx] at h1

/-- **Kernighan's step**: `n &&& (n - 1)` is `n` with its lowest 1 bit cleared, one 1 bit fewer. -/
theorem ones_and_pred : ∀ n, 0 < n → ones (n &&& (n - 1)) + 1 = ones n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro hn
  rw [ones_eq (n &&& (n - 1)), and_mod_two_zero (by omega), Nat.and_div_two, ones_eq n]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have e : (n - 1) / 2 = n / 2 - 1 := by omega
    rw [e, ← ih (n / 2) (by omega) (by omega), h]; omega
  · have e : (n - 1) / 2 = n / 2 := by omega
    rw [e, Nat.and_self, h]; omega

/-- The machine's step, `(x - 1) &&& x`, as numbers. -/
theorem step_toNat {x : Word} (hx : x ≠ 0#64) :
    ((x + 18446744073709551615#64) &&& x).toNat = x.toNat &&& (x.toNat - 1) := by
  have e : (x + 18446744073709551615#64).toNat = x.toNat - 1 := by bv_omega
  rw [BitVec.toNat_and, e, Nat.and_comm]

/-- The registers `popcount` may change. -/
def popClobbered : List Reg := [.x10, .x11, .x12]

/-- **The loop of `popcount`**, at its head with `x10 ≠ 0` and the count so far in `x11`: by
    strong induction on `x10`, which loses a 1 bit each time round. -/
theorem popcount_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) :
    ∀ n (regs : Reg → Word), (regs .x10).toNat = n → regs .x10 ≠ 0#64 →
      regs .x1 = ret → regs .x2 = top →
      (∀ r' m', r' .x10 = regs .x11 + BitVec.ofNat 64 (ones n) ∧
        (∀ r, r ∉ popClobbered → r' r = regs r) ∧ m' = m → LSafeN fns G N Q ⟨rest, r', m'⟩) →
      LSafeN fns G N Q ⟨⟨6, 4, ret, top⟩ :: rest, regs, m⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro regs hn hx hra hsp hk
    have hstep := ones_and_pred n (by bv_omega)
    have hnat := step_toNat hx
    rw [hn] at hnat
    lsym f6_eq stop [4] with [hra, hsp, hx]
    · have hlt : n &&& (n - 1) < n := Nat.lt_of_le_of_lt Nat.and_le_right (by bv_omega)
      apply ih _ hlt
      · simp only [lsym_simp]; exact hnat
      · simp only [lsym_simp]; exact hc
      · simp only [lsym_simp]; exact hra
      · simp only [lsym_simp]; exact hsp
      · intro r' m' ⟨h10, hf, hm⟩
        apply hk r' m'
        refine ⟨?_, fun r hr => ?_, hm⟩
        · rw [h10, ← hstep]; simp only [lsym_simp, BitVec.ofNat_add]; bv_omega
        · rw [hf r hr]
          simp only [popClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [lsym_simp, hr]
    · -- no bit is left: `n` had one
      refine hk _ _ ⟨?_, fun r hr => ?_, rfl⟩
      · have h0 : n &&& (n - 1) = 0 := by rw [← hnat, hc, BitVec.toNat_zero]
        rw [← hstep, h0]; simp [lsym_simp, ones]
      · simp only [popClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]

/-- `popcount(x)`: the number of 1 bits of `x` (`ones`); every register but `x10`..`x12` and the
    memory kept. -/
theorem popcount_contract : rvIsa.Contract (liftProg fns) sp1Ctx 6 Called
    (fun _ _ regs m r' m' => r' .x10 = BitVec.ofNat 64 (ones (regs .x10).toNat) ∧
      (∀ r, r ∉ popClobbered → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f6_eq stop [4] with [hra, hsp]
  · -- `x = 0`: no 1 bit
    refine hk _ _ ⟨by simp [lsym_simp, hc, ones], fun r hr => ?_, rfl⟩
    simp only [popClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [lsym_simp, hr]
  · apply popcount_loop m _ _ rfl
    · simp only [lsym_simp]; exact hc
    · simp only [lsym_simp]; exact hra
    · simp only [lsym_simp]; exact hsp
    · intro r' m' ⟨h10, hf, hm⟩
      apply hk r' m'
      refine ⟨?_, fun r hr => ?_, hm⟩
      · rw [h10]; simp [lsym_simp]
      · rw [hf r hr]
        simp only [popClobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]

/-- **`popcount` on the machine.** -/
theorem popcount_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1070#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (ones (s.getReg .x10).toNat) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[6]? = some fn ∧ fn.base = 0x1070#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode popcount_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## An absolute value without a branch -/

/-- `abs_branchless(x)`: `|x|`, with `|INT64_MIN| = INT64_MIN`. -/
def absSpec (x _ : Word) : Word := if x.slt 0 then -x else x

theorem abs_branchless_contract : rvIsa.Contract (liftProg fns) sp1Ctx 7 Called (Gives absSpec) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f7_eq with [hra, hsp]
  all_goals (refine hk _ _ ⟨?_, rfl⟩; simp only [absSpec, lsym_simp] at *; bv_decide)

/-- **`abs_branchless` on the machine.** -/
theorem abs_branchless_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1090#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = absSpec (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s :=
  gives_correct abs_branchless_contract ⟨_, rfl, rfl⟩ s hpc hcode hk

end Examples.Arith.RiscV
