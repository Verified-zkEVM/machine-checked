/-
  Examples.Big.RiscV.Proofs

  `mix(x, y)` of `src/c/big.c`, compiled by clang to `Examples/elf/big.elf`: thirty-two unrolled
  rounds of `x ^= y + 0x9e3779b97f4a7c15 * k; x = (x << 7) | (x >> 57); y += x ^ k;`, then
  `return x ^ y`, in 290 instructions of straight-line code. Its contract at Lprog, proved with
  `lsym`, and the same statement over riscv-zkvm's machine (`mix_correct`).

  The specification (`mix`) is the C: `rounds` folds `round` over `k = 1, …, 32`. clang does not
  multiply: it loads each product `0x9e3779b97f4a7c15 * k` from `.rodata` at `0x2490`, in an
  order of its own, and loads each two rounds ahead. The precondition says memory holds that
  table (`TableAt`).

  The body is too long for one `lsym` call within the default limits, so it is checked in eight
  pieces of four rounds each, with intermediate `stop`s (`rounds_1_4` … `rounds_29_32`). At the
  head of round `k` (`k` odd) the state is in `x10`, `x11`, and the next two products are in
  `x12` and `x13`; each piece takes that to the head of round `k + 4`. `mix_contract` chains them.
  `_start` loops forever by design and is not proved.
-/

import Examples.Big.RiscV.Image
import Examples.Kit

namespace Examples.Big.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Big.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-! ## The specification -/

/-- The multiplier of `big.c`, `0x9e3779b97f4a7c15`. -/
def C : BitVec 64 := 0x9e3779b97f4a7c15#64

/-- Round `k` of `mix` on `(x, y)`: `x ^= y + C * k; x = (x << 7) | (x >> 57); y += x ^ k;`. -/
def round (k : Nat) (p : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  let x := p.1 ^^^ (p.2 + C * BitVec.ofNat 64 k)
  let x := (x <<< 7) ||| (x >>> 57)
  (x, p.2 + (x ^^^ BitVec.ofNat 64 k))

/-- Rounds `a`, `a + 1`, …, `a + n - 1`, in that order. -/
def rounds (a n : Nat) (p : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range' a n).foldl (fun p k => round k p) p

/-- `mix(x, y)`: rounds `1` to `32`, then `x ^ y`. -/
def mix (x y : BitVec 64) : BitVec 64 :=
  let p := rounds 1 32 (x, y)
  p.1 ^^^ p.2

/-! ## The machine's rounds -/

/-- A round as the machine computes it, with `c = C * k` loaded and `k` a word. -/
def mround (c k : BitVec 64) (p : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  let t := (p.2 + c) ^^^ p.1
  let x := t <<< 7 ||| t >>> 57
  (x, (x ^^^ k) + p.2)

theorem round_eq (k : Nat) (p : BitVec 64 × BitVec 64) :
    round k p = mround (C * BitVec.ofNat 64 k) (BitVec.ofNat 64 k) p := by
  simp only [round, mround, Prod.mk.injEq]
  exact ⟨by rw [BitVec.xor_comm p.1], by rw [BitVec.xor_comm p.1, BitVec.add_comm p.2]⟩

/-- The thirty-two rounds, as the eight pieces take them. -/
theorem rounds_split (p : BitVec 64 × BitVec 64) :
    rounds 1 32 p = rounds 29 4 (rounds 25 4 (rounds 21 4 (rounds 17 4 (rounds 13 4 (rounds 9 4
      (rounds 5 4 (rounds 1 4 p))))))) := by
  simp only [rounds, List.range', List.foldl, Nat.reduceAdd]

theorem xor_swap (p : BitVec 64 × BitVec 64) : p.1 ^^^ p.2 = p.2 ^^^ p.1 := BitVec.xor_comm _ _

/-! ## Memory and registers -/

/-- The order in which `.rodata` holds the products `C * k`, a doubleword each from `0x2490`
    (read off `llvm-objdump -s -j .rodata Examples/elf/big.elf`). -/
def order : List Nat :=
  [2, 8, 7, 18, 28, 6, 1, 10, 16, 5, 9, 13, 22, 14, 26, 15, 27, 29, 24, 25, 30, 31, 12, 20, 21,
    32, 11, 3, 17, 19, 4, 23]

/-- Memory holds the table of products `C * k`, `k = 1, …, 32`, at `0x2490`, as `big.elf`'s
    `.rodata` has it. -/
def TableAt (m : MachineState) : Prop :=
  ∀ i < 32, m.getMem (0x2490#64 + BitVec.ofNat 64 (8 * i)) = C * BitVec.ofNat 64 (order.getD i 0)

/-- The registers `mix` may change. -/
def clobbered : List Reg := [.x10, .x11, .x12, .x13]

/-- Every register `mix` does not change is as it was in `regs`. -/
def Kept (r regs : Reg → Word) : Prop := ∀ q, q ∉ clobbered → r q = regs q

theorem Kept.trans {r s t : Reg → Word} (h1 : Kept r s) (h2 : Kept s t) : Kept r t :=
  fun q h => (h1 q h).trans (h2 q h)

/-! ## The pieces -/

/-- **Rounds 1 to 4** [0 to 80], with the first two loads. -/
theorem rounds_1_4 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (hpost : ∀ r : Reg → Word, (r .x10, r .x11) = rounds 1 4 (regs .x10, regs .x11) →
      r .x12 = C * BitVec.ofNat 64 5 → r .x13 = C * BitVec.ofNat 64 6 → Kept r regs →
      LSafeN fns G N Q ⟨⟨0, 80, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 6 (by decide)
  have l1 := htbl 0 (by decide)
  have l2 := htbl 27 (by decide)
  have l3 := htbl 30 (by decide)
  have l4 := htbl 9 (by decide)
  have l5 := htbl 5 (by decide)
  simp [order, C] at l0 l1 l2 l3 l4 l5
  lsym f0_eq stop [80] with [l0, l1, l2, l3, l4, l5]
  refine hpost _ ?_ ?_ ?_ ?_
  · simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · simp [lsym_simp, C]
  · simp [lsym_simp, C]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-- **Rounds 5 to 8** [80 to 152]. -/
theorem rounds_5_8 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (h12 : regs .x12 = C * BitVec.ofNat 64 5) (h13 : regs .x13 = C * BitVec.ofNat 64 6)
    (hpost : ∀ r : Reg → Word, (r .x10, r .x11) = rounds 5 4 (regs .x10, regs .x11) →
      r .x12 = C * BitVec.ofNat 64 9 → r .x13 = C * BitVec.ofNat 64 10 → Kept r regs →
      LSafeN fns G N Q ⟨⟨0, 152, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 80, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 2 (by decide)
  have l1 := htbl 1 (by decide)
  have l2 := htbl 10 (by decide)
  have l3 := htbl 7 (by decide)
  simp [order, C] at l0 l1 l2 l3 h12 h13
  lsym f0_eq stop [152] with [l0, l1, l2, l3, h12, h13]
  refine hpost _ ?_ ?_ ?_ ?_
  · simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · simp [lsym_simp, C]
  · simp [lsym_simp, C]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-- **Rounds 9 to 12** [152 to 224]. -/
theorem rounds_9_12 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (h12 : regs .x12 = C * BitVec.ofNat 64 9) (h13 : regs .x13 = C * BitVec.ofNat 64 10)
    (hpost : ∀ r : Reg → Word, (r .x10, r .x11) = rounds 9 4 (regs .x10, regs .x11) →
      r .x12 = C * BitVec.ofNat 64 13 → r .x13 = C * BitVec.ofNat 64 14 → Kept r regs →
      LSafeN fns G N Q ⟨⟨0, 224, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 152, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 26 (by decide)
  have l1 := htbl 22 (by decide)
  have l2 := htbl 11 (by decide)
  have l3 := htbl 13 (by decide)
  simp [order, C] at l0 l1 l2 l3 h12 h13
  lsym f0_eq stop [224] with [l0, l1, l2, l3, h12, h13]
  refine hpost _ ?_ ?_ ?_ ?_
  · simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · simp [lsym_simp, C]
  · simp [lsym_simp, C]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-- **Rounds 13 to 16** [224 to 296]. -/
theorem rounds_13_16 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (h12 : regs .x12 = C * BitVec.ofNat 64 13) (h13 : regs .x13 = C * BitVec.ofNat 64 14)
    (hpost : ∀ r : Reg → Word, (r .x10, r .x11) = rounds 13 4 (regs .x10, regs .x11) →
      r .x12 = C * BitVec.ofNat 64 17 → r .x13 = C * BitVec.ofNat 64 18 → Kept r regs →
      LSafeN fns G N Q ⟨⟨0, 296, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 224, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 15 (by decide)
  have l1 := htbl 8 (by decide)
  have l2 := htbl 28 (by decide)
  have l3 := htbl 3 (by decide)
  simp [order, C] at l0 l1 l2 l3 h12 h13
  lsym f0_eq stop [296] with [l0, l1, l2, l3, h12, h13]
  refine hpost _ ?_ ?_ ?_ ?_
  · simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · simp [lsym_simp, C]
  · simp [lsym_simp, C]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-- **Rounds 17 to 20** [296 to 368]. -/
theorem rounds_17_20 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (h12 : regs .x12 = C * BitVec.ofNat 64 17) (h13 : regs .x13 = C * BitVec.ofNat 64 18)
    (hpost : ∀ r : Reg → Word, (r .x10, r .x11) = rounds 17 4 (regs .x10, regs .x11) →
      r .x12 = C * BitVec.ofNat 64 21 → r .x13 = C * BitVec.ofNat 64 22 → Kept r regs →
      LSafeN fns G N Q ⟨⟨0, 368, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 296, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 29 (by decide)
  have l1 := htbl 23 (by decide)
  have l2 := htbl 24 (by decide)
  have l3 := htbl 12 (by decide)
  simp [order, C] at l0 l1 l2 l3 h12 h13
  lsym f0_eq stop [368] with [l0, l1, l2, l3, h12, h13]
  refine hpost _ ?_ ?_ ?_ ?_
  · simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · simp [lsym_simp, C]
  · simp [lsym_simp, C]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-- **Rounds 21 to 24** [368 to 440]. -/
theorem rounds_21_24 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (h12 : regs .x12 = C * BitVec.ofNat 64 21) (h13 : regs .x13 = C * BitVec.ofNat 64 22)
    (hpost : ∀ r : Reg → Word, (r .x10, r .x11) = rounds 21 4 (regs .x10, regs .x11) →
      r .x12 = C * BitVec.ofNat 64 25 → r .x13 = C * BitVec.ofNat 64 26 → Kept r regs →
      LSafeN fns G N Q ⟨⟨0, 440, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 368, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 31 (by decide)
  have l1 := htbl 18 (by decide)
  have l2 := htbl 19 (by decide)
  have l3 := htbl 14 (by decide)
  simp [order, C] at l0 l1 l2 l3 h12 h13
  lsym f0_eq stop [440] with [l0, l1, l2, l3, h12, h13]
  refine hpost _ ?_ ?_ ?_ ?_
  · simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · simp [lsym_simp, C]
  · simp [lsym_simp, C]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-- **Rounds 25 to 28** [440 to 512]. -/
theorem rounds_25_28 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (h12 : regs .x12 = C * BitVec.ofNat 64 25) (h13 : regs .x13 = C * BitVec.ofNat 64 26)
    (hpost : ∀ r : Reg → Word, (r .x10, r .x11) = rounds 25 4 (regs .x10, regs .x11) →
      r .x12 = C * BitVec.ofNat 64 29 → r .x13 = C * BitVec.ofNat 64 30 → Kept r regs →
      LSafeN fns G N Q ⟨⟨0, 512, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 440, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 16 (by decide)
  have l1 := htbl 4 (by decide)
  have l2 := htbl 17 (by decide)
  have l3 := htbl 20 (by decide)
  simp [order, C] at l0 l1 l2 l3 h12 h13
  lsym f0_eq stop [512] with [l0, l1, l2, l3, h12, h13]
  refine hpost _ ?_ ?_ ?_ ?_
  · simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · simp [lsym_simp, C]
  · simp [lsym_simp, C]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-- **Rounds 29 to 32** [512 to the end], then `x ^ y` and the return. -/
theorem rounds_29_32 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (htbl : TableAt m)
    (h12 : regs .x12 = C * BitVec.ofNat 64 29) (h13 : regs .x13 = C * BitVec.ofNat 64 30)
    (h1 : regs .x1 = ret) (h2 : regs .x2 = top)
    (hpost : ∀ r : Reg → Word,
      r .x10 = (rounds 29 4 (regs .x10, regs .x11)).1 ^^^ (rounds 29 4 (regs .x10, regs .x11)).2 →
      Kept r regs → LSafeN fns G N Q ⟨rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨0, 512, ret, top⟩ :: rest, regs, m⟩ := by
  have l0 := htbl 21 (by decide)
  have l1 := htbl 25 (by decide)
  simp [order, C] at l0 l1 h12 h13
  lsym f0_eq with [l0, l1, h12, h13, h1, h2]
  refine hpost _ ?_ ?_
  · rw [xor_swap]
    simp only [rounds, List.range', List.foldl, round_eq, mround, C, lsym_simp, BitVec.reduceMul,
      Nat.reduceAdd]
  · intro q hq
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [lsym_simp, hq]

/-! ## `mix` -/

/-- `mix(x, y)`: the C's thirty-two rounds and `x ^ y` in `x10`; every register but
    `x10`..`x13`, and the memory, kept. -/
theorem mix_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧ TableAt m)
    (fun _ _ regs m r' m' => r' .x10 = mix (regs .x10) (regs .x11) ∧ Kept r' regs ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, htbl⟩ hk
  refine rounds_1_4 regs htbl fun r1 e1 c1 d1 k1 => ?_
  refine rounds_5_8 r1 htbl c1 d1 fun r2 e2 c2 d2 k2 => ?_
  refine rounds_9_12 r2 htbl c2 d2 fun r3 e3 c3 d3 k3 => ?_
  refine rounds_13_16 r3 htbl c3 d3 fun r4 e4 c4 d4 k4 => ?_
  refine rounds_17_20 r4 htbl c4 d4 fun r5 e5 c5 d5 k5 => ?_
  refine rounds_21_24 r5 htbl c5 d5 fun r6 e6 c6 d6 k6 => ?_
  refine rounds_25_28 r6 htbl c6 d6 fun r7 e7 c7 d7 k7 => ?_
  have k : Kept r7 regs := k7.trans (k6.trans (k5.trans (k4.trans (k3.trans (k2.trans k1)))))
  refine rounds_29_32 r7 htbl c7 d7 ((k .x1 (by decide)).trans hra) ((k .x2 (by decide)).trans hsp)
    fun r8 e8 k8 => hk _ _ ⟨?_, k8.trans k, rfl⟩
  rw [e8, e7, e6, e5, e4, e3, e2, e1, mix, rounds_split]

/-- **`mix` on the machine.** With the table of products in memory, it returns with
    `mix(x, y)` in `x10`, every register but `x10`..`x13` and the memory as they were. -/
theorem mix_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s) (htbl : TableAt s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = mix (s.getReg .x10) (s.getReg .x11) →
      (∀ r, r ∉ clobbered → t.getReg r = s.getReg r) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode mix_contract ⟨rfl, rfl, htbl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, hkept, rfl⟩
  refine hk t hpc' ?_ (fun r hr => ?_) fun a => (hag.mem a).symm
  · rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10
  · rw [← hag.regs, getReg_ofParts]; split
    · subst_vars; rfl
    · simp [regsOf, hkept r hr]

end Examples.Big.RiscV
