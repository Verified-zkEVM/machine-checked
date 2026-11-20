/-
  Examples.ChaCha20.RiscV.Proofs

  `quarter_round(s)` and `chacha20_block(out, in)` of `src/c/chacha20.c`, compiled by clang:
  ChaCha20's quarter round on the four 32-bit words at `s`, and its block function. Their
  contracts at Lprog, proved with `lsym`, and the same statements over riscv-zkvm's machine
  (`quarter_round_correct`, `chacha20_block_correct`).

  The specification is `qr` (`Examples/Spec.lean`), the quarter round on four `BitVec 32` with
  `BitVec.rotateLeft`. The code computes in 64-bit registers (`lw` sign-extends, a rotation is
  `slli`, `srliw` and `or`) and stores the low 32 bits; that these are `qr`'s words is
  `bv_decide`'s work. Memory is doublewords, so a 32-bit word is half of one: the lemmas of
  `Examples/Kit.lean` read a word and a byte after a word was written. No byte outside the
  sixteen at `s` changes.

  `chacha20_block` is 226 instructions. It keeps the state `x` in a frame of 112 bytes, with `s0`,
  …, `s4` saved at its top, and runs three loops: `in` copied into `x`, the ten double rounds with
  the state in sixteen registers, and `out[i] = x[i] + in[i]`. The specification is RFC 8439's
  (`block`, in `Spec.lean`): twenty rounds, as ten double rounds of `quarterRound`, added to the
  state they started from. Each loop is a lemma at its head, by induction on what is left; the
  code between them is stepped by lemmas of its own. The body of the double rounds, 162
  instructions, is stepped in four pieces of about forty (`col1`, `col2`, `diag1`, `diag2`), each
  within the default limits; each is half of the column or the diagonal round, checked by
  `bv_decide` against half of `qr`. Until the last loop, memory outside the frame is as it was on
  entry (`Kept`). The precondition asks that `out` and `in` be outside the frame, and that no word
  of `out` be a word of `in` that the last loop reads after writing it; `out` may be `in`.
-/

import Examples.ChaCha20.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.ChaCha20.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.ChaCha20.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-! ## The four words in memory -/

/-- **Four words written** at `s`, `s + 4`, `s + 8` and `s + 12`: they read back, and no byte
    outside the sixteen changes. -/
theorem four_words (m : MachineState) (s : Word) (A B C D : BitVec 32)
    (h : alignedFor 4 s = true) :
    let m' := (((m.setWord32 s A).setWord32 (s + 4#64) B).setWord32 (s + 8#64) C).setWord32
      (s + 12#64) D
    m'.getWord32 s = A ∧ m'.getWord32 (s + 4#64) = B ∧ m'.getWord32 (s + 8#64) = C ∧
      m'.getWord32 (s + 12#64) = D ∧
      (∀ x, 16 ≤ (x - s).toNat → m'.getByte x = m.getByte x) ∧ m'.code = m.code := by
  have h4 := aligned4_add h 4#64 (by decide)
  have h8 := aligned4_add h 8#64 (by decide)
  have h12 := aligned4_add h 12#64 (by decide)
  refine ⟨?_, ?_, ?_, ?_, fun x hx => ?_, rfl⟩
  · rw [getWord32_setWord32 _ _ _ _ h12 h, getWord32_setWord32 _ _ _ _ h8 h,
      getWord32_setWord32 _ _ _ _ h4 h, getWord32_setWord32 _ _ _ _ h h]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h4, getWord32_setWord32 _ _ _ _ h8 h4,
      getWord32_setWord32 _ _ _ _ h4 h4]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h8, getWord32_setWord32 _ _ _ _ h8 h8]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h12]
    simp
  · rw [getByte_setWord32 _ _ _ _ h12 (by bv_omega), getByte_setWord32 _ _ _ _ h8 (by bv_omega),
      getByte_setWord32 _ _ _ _ h4 (by bv_omega), getByte_setWord32 _ _ _ _ h (by bv_omega)]

/-! ## `quarter_round` -/

/-- The registers `quarter_round` may change. -/
def clobbered : List Reg := [.x11, .x12, .x13, .x14, .x15]

/-- `quarter_round(s)`: the four words at `s` become `qr` of what they were; no byte outside
    them changes, nor the code, nor a register outside `x11`..`x15`. -/
theorem quarter_round_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧ Writable m (regs .x10) 4)
    (fun _ _ regs m r' m' =>
      (m'.getWord32 (regs .x10), m'.getWord32 (regs .x10 + 4#64), m'.getWord32 (regs .x10 + 8#64),
        m'.getWord32 (regs .x10 + 12#64)) =
        qr (m.getWord32 (regs .x10)) (m.getWord32 (regs .x10 + 4#64))
          (m.getWord32 (regs .x10 + 8#64)) (m.getWord32 (regs .x10 + 12#64)) ∧
      (∀ x, 16 ≤ (x - regs .x10).toNat → m'.getByte x = m.getByte x) ∧ m'.code = m.code ∧
      (∀ r, r ∉ clobbered → r' r = regs r)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hal, hw⟩ hk
  have h4 := aligned4_add hal 4#64 (by decide)
  have h8 := aligned4_add hal 8#64 (by decide)
  have h12 := aligned4_add hal 12#64 (by decide)
  have w0 := hw 0 (by decide); have w1 := hw 1 (by decide)
  have w2 := hw 2 (by decide); have w3 := hw 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.add_zero] at w0 w1 w2 w3
  lsym f0_eq with [hra, hsp, hal, h4, h8, h12, w0, w1, w2, w3, noCodeAt_setWord32]
  apply hk
  refine ⟨?_, (four_words m _ _ _ _ _ hal).2.2.2.2.1, (four_words m _ _ _ _ _ hal).2.2.2.2.2, ?_⟩
  · simp only [qr, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [(four_words m _ _ _ _ _ hal).1]; bv_decide
    · rw [(four_words m _ _ _ _ _ hal).2.1]; bv_decide
    · rw [(four_words m _ _ _ _ _ hal).2.2.1]; bv_decide
    · rw [(four_words m _ _ _ _ _ hal).2.2.2.1]; bv_decide
  · intro r hr
    simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [lsym_simp, hr]

/-- **`quarter_round` on the machine.** -/
theorem quarter_round_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s) (hw : Writable s (s.getReg .x10) 4)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      (t.getWord32 (s.getReg .x10), t.getWord32 (s.getReg .x10 + 4#64),
        t.getWord32 (s.getReg .x10 + 8#64), t.getWord32 (s.getReg .x10 + 12#64)) =
        qr (s.getWord32 (s.getReg .x10)) (s.getWord32 (s.getReg .x10 + 4#64))
          (s.getWord32 (s.getReg .x10 + 8#64)) (s.getWord32 (s.getReg .x10 + 12#64)) →
      (∀ x, 16 ≤ (x - s.getReg .x10).toNat → t.getByte x = s.getByte x) → t.code = s.code →
      SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode quarter_round_contract ⟨rfl, rfl, hw⟩ ?_
  rintro t r' m' hag hpc' ⟨hqr, hfr, hc, -⟩
  refine hk t hpc' ?_ (fun x hx => ?_) ?_
  · simp only [getWord32_of_agree hag]; exact hqr
  · rw [getByte_of_agree hag]; exact hfr x hx
  · rw [← hag.code]; exact hc

/-! ## `chacha20_block`: the double rounds, in registers

The loop of the double rounds keeps the sixteen words of the state in sixteen registers and does
not touch memory: 161 instructions and a branch per iteration, which clang interleaves, four
quarter rounds at a time. The body is stepped in four pieces of about forty instructions, each a
lemma of its own that stops `lsym` at the next (`col1`, `col2`, `diag1`, `diag2`): the first and
second halves of the column round, then of the diagonal round. Each piece relates the registers
after it to those before it by a function on the state (`colWith halfA`, …) that `bv_decide`
checks word by word, and `columnRound_halves`/`diagonalRound_halves` put the halves back
together into the specification's rounds. -/

/-- The register the loop keeps word `i` of the state in. -/
def regOf : Fin 16 → Reg
  | 0 => .x8 | 1 => .x18 | 2 => .x19 | 3 => .x9
  | 4 => .x31 | 5 => .x5 | 6 => .x6 | 7 => .x28
  | 8 => .x15 | 9 => .x16 | 10 => .x13 | 11 => .x14
  | 12 => .x7 | 13 => .x29 | 14 => .x30 | _ => .x17

/-- The state in the registers: the low halves of those `regOf` names. -/
def regs16 (r : Reg → Word) : ChaCha20.State := fun i => (r (regOf i)).setWidth 32

/-- Two states are equal if their sixteen words are. -/
theorem state_ext {s t : ChaCha20.State} (h0 : s 0 = t 0) (h1 : s 1 = t 1) (h2 : s 2 = t 2)
    (h3 : s 3 = t 3) (h4 : s 4 = t 4) (h5 : s 5 = t 5) (h6 : s 6 = t 6) (h7 : s 7 = t 7)
    (h8 : s 8 = t 8) (h9 : s 9 = t 9) (h10 : s 10 = t 10) (h11 : s 11 = t 11) (h12 : s 12 = t 12)
    (h13 : s 13 = t 13) (h14 : s 14 = t 14) (h15 : s 15 = t 15) : s = t := by
  funext i
  match i with
  | 0 => exact h0 | 1 => exact h1 | 2 => exact h2 | 3 => exact h3 | 4 => exact h4
  | 5 => exact h5 | 6 => exact h6 | 7 => exact h7 | 8 => exact h8 | 9 => exact h9
  | 10 => exact h10 | 11 => exact h11 | 12 => exact h12 | 13 => exact h13 | 14 => exact h14
  | 15 => exact h15
  | ⟨n + 16, h⟩ => exact absurd h (by omega)

/-- Four words: what a quarter round, or half of one, gives. -/
abbrev Quad := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- `f` on the words at `a`, `b`, `c`, `d` of the state: `quarterRound` with `f` for `qr`. -/
def qstep (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → Quad) (a b c d : Fin 16)
    (s : ChaCha20.State) : ChaCha20.State :=
  let (a', b', c', d') := f (s a) (s b) (s c) (s d)
  fun i => if i = a then a' else if i = b then b' else if i = c then c' else if i = d then d'
    else s i

/-- `f` on each column, as `columnRound` does with `qr`. -/
def colWith (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → Quad) (s : ChaCha20.State) :
    ChaCha20.State :=
  qstep f 3 7 11 15 (qstep f 2 6 10 14 (qstep f 1 5 9 13 (qstep f 0 4 8 12 s)))

/-- `f` on each diagonal, as `diagonalRound` does with `qr`. -/
def diagWith (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → Quad) (s : ChaCha20.State) :
    ChaCha20.State :=
  qstep f 3 4 9 14 (qstep f 2 7 8 13 (qstep f 1 6 11 12 (qstep f 0 5 10 15 s)))

/-- The first half of `qr`: the rotations by 16 and 12. -/
def halfA (a b c d : BitVec 32) : Quad :=
  let a := a + b
  let d := (d ^^^ a).rotateLeft 16
  let c := c + d
  let b := (b ^^^ c).rotateLeft 12
  (a, b, c, d)

/-- The second half of `qr`: the rotations by 8 and 7. -/
def halfB (a b c d : BitVec 32) : Quad :=
  let a := a + b
  let d := (d ^^^ a).rotateLeft 8
  let c := c + d
  let b := (b ^^^ c).rotateLeft 7
  (a, b, c, d)

/-- The words of `colWith f s`. -/
theorem colWith_apply (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → Quad)
    (s : ChaCha20.State) :
    colWith f s 0 = (f (s 0) (s 4) (s 8) (s 12)).1 ∧
    colWith f s 4 = (f (s 0) (s 4) (s 8) (s 12)).2.1 ∧
    colWith f s 8 = (f (s 0) (s 4) (s 8) (s 12)).2.2.1 ∧
    colWith f s 12 = (f (s 0) (s 4) (s 8) (s 12)).2.2.2 ∧
    colWith f s 1 = (f (s 1) (s 5) (s 9) (s 13)).1 ∧
    colWith f s 5 = (f (s 1) (s 5) (s 9) (s 13)).2.1 ∧
    colWith f s 9 = (f (s 1) (s 5) (s 9) (s 13)).2.2.1 ∧
    colWith f s 13 = (f (s 1) (s 5) (s 9) (s 13)).2.2.2 ∧
    colWith f s 2 = (f (s 2) (s 6) (s 10) (s 14)).1 ∧
    colWith f s 6 = (f (s 2) (s 6) (s 10) (s 14)).2.1 ∧
    colWith f s 10 = (f (s 2) (s 6) (s 10) (s 14)).2.2.1 ∧
    colWith f s 14 = (f (s 2) (s 6) (s 10) (s 14)).2.2.2 ∧
    colWith f s 3 = (f (s 3) (s 7) (s 11) (s 15)).1 ∧
    colWith f s 7 = (f (s 3) (s 7) (s 11) (s 15)).2.1 ∧
    colWith f s 11 = (f (s 3) (s 7) (s 11) (s 15)).2.2.1 ∧
    colWith f s 15 = (f (s 3) (s 7) (s 11) (s 15)).2.2.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The words of `diagWith f s`. -/
theorem diagWith_apply (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → Quad)
    (s : ChaCha20.State) :
    diagWith f s 0 = (f (s 0) (s 5) (s 10) (s 15)).1 ∧
    diagWith f s 5 = (f (s 0) (s 5) (s 10) (s 15)).2.1 ∧
    diagWith f s 10 = (f (s 0) (s 5) (s 10) (s 15)).2.2.1 ∧
    diagWith f s 15 = (f (s 0) (s 5) (s 10) (s 15)).2.2.2 ∧
    diagWith f s 1 = (f (s 1) (s 6) (s 11) (s 12)).1 ∧
    diagWith f s 6 = (f (s 1) (s 6) (s 11) (s 12)).2.1 ∧
    diagWith f s 11 = (f (s 1) (s 6) (s 11) (s 12)).2.2.1 ∧
    diagWith f s 12 = (f (s 1) (s 6) (s 11) (s 12)).2.2.2 ∧
    diagWith f s 2 = (f (s 2) (s 7) (s 8) (s 13)).1 ∧
    diagWith f s 7 = (f (s 2) (s 7) (s 8) (s 13)).2.1 ∧
    diagWith f s 8 = (f (s 2) (s 7) (s 8) (s 13)).2.2.1 ∧
    diagWith f s 13 = (f (s 2) (s 7) (s 8) (s 13)).2.2.2 ∧
    diagWith f s 3 = (f (s 3) (s 4) (s 9) (s 14)).1 ∧
    diagWith f s 4 = (f (s 3) (s 4) (s 9) (s 14)).2.1 ∧
    diagWith f s 9 = (f (s 3) (s 4) (s 9) (s 14)).2.2.1 ∧
    diagWith f s 14 = (f (s 3) (s 4) (s 9) (s 14)).2.2.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `qr` is its two halves. -/
theorem qr_halves (a b c d : BitVec 32) :
    qr a b c d = halfB (halfA a b c d).1 (halfA a b c d).2.1 (halfA a b c d).2.2.1
      (halfA a b c d).2.2.2 := by
  simp only [qr, halfA, halfB]

theorem quarterRound_eq : quarterRound = qstep qr := rfl

/-- The column round is its two halves. -/
theorem columnRound_halves (s : ChaCha20.State) :
    columnRound s = colWith halfB (colWith halfA s) := by
  have e : columnRound s = colWith qr s := by rw [columnRound, quarterRound_eq]; rfl
  rw [e]
  refine state_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [colWith_apply, qr_halves]

/-- The diagonal round is its two halves. -/
theorem diagonalRound_halves (s : ChaCha20.State) :
    diagonalRound s = diagWith halfB (diagWith halfA s) := by
  have e : diagonalRound s = diagWith qr s := by rw [diagonalRound, quarterRound_eq]; rfl
  rw [e]
  refine state_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [diagWith_apply, qr_halves]

/-- The registers the double-round loop does not touch but its context needs. -/
def Same (r regs : Reg → Word) : Prop :=
  r .x1 = regs .x1 ∧ r .x2 = regs .x2 ∧ r .x10 = regs .x10 ∧ r .x11 = regs .x11

/-- **The first half of the column round** [62 to 144], and the loop's counter decremented. -/
theorem col1 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (hpost : ∀ r : Reg → Word, regs16 r = colWith halfA (regs16 regs) →
      r .x12 = BitVec.signExtend 64 (BitVec.setWidth 32 (regs .x12 + 18446744073709551615#64)) →
      Same r regs → LSafeN fns G N Q ⟨⟨1, 144, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨1, 62, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq stop [144]
  refine hpost _ (state_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [regs16, regOf, lsym_simp, colWith_apply, halfA]
  all_goals bv_decide

/-- **The second half of the column round** [144 to 224]. -/
theorem col2 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (hpost : ∀ r : Reg → Word, regs16 r = colWith halfB (regs16 regs) → r .x12 = regs .x12 →
      Same r regs → LSafeN fns G N Q ⟨⟨1, 224, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨1, 144, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq stop [224]
  refine hpost _ (state_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [regs16, regOf, lsym_simp, colWith_apply, halfB]
  all_goals bv_decide

/-- **The first half of the diagonal round** [224 to 304]. -/
theorem diag1 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (hpost : ∀ r : Reg → Word, regs16 r = diagWith halfA (regs16 regs) → r .x12 = regs .x12 →
      Same r regs → LSafeN fns G N Q ⟨⟨1, 304, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨1, 224, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq stop [304]
  refine hpost _ (state_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [regs16, regOf, lsym_simp, diagWith_apply, halfA]
  all_goals bv_decide

/-- **The second half of the diagonal round** [304 to 384], up to the branch. -/
theorem diag2 {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} (regs : Reg → Word)
    (hpost : ∀ r : Reg → Word, regs16 r = diagWith halfB (regs16 regs) → r .x12 = regs .x12 →
      Same r regs → LSafeN fns G N Q ⟨⟨1, 384, ret, top⟩ :: rest, r, m⟩) :
    LSafeN fns G N Q ⟨⟨1, 304, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq stop [384]
  refine hpost _ (state_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ⟨?_, ?_, ?_, ?_⟩
  all_goals simp only [regs16, regOf, lsym_simp, diagWith_apply, halfB]
  all_goals bv_decide

theorem ctr_more {t : Nat} (ht : t < 10) (h : ¬BitVec.ofNat 64 (9 - t) = 0#64) : t + 1 < 10 := by
  bv_omega

theorem ctr_last {t : Nat} (ht : t < 10) (h : BitVec.ofNat 64 (9 - t) = 0#64) : t = 9 := by
  bv_omega

/-- The loop's counter `a2`, `10 - t` after `t` double rounds, decremented by `addiw`. -/
theorem ctr_step {t : Nat} (ht : t < 10) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (10 - t) + 18446744073709551615#64)) =
      BitVec.ofNat 64 (10 - (t + 1)) := by
  match t, ht with
  | 0, _ => decide | 1, _ => decide | 2, _ => decide | 3, _ => decide | 4, _ => decide
  | 5, _ => decide | 6, _ => decide | 7, _ => decide | 8, _ => decide | 9, _ => decide
  | n + 10, h => exact absurd h (by omega)

/-- The end of a double round: the branch back to the loop's head, or out of the loop after the
    tenth. -/
theorem round_branch {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} {S : ChaCha20.State}
    {sp out inp : Word}
    (hpost : ∀ r : Reg → Word, regs16 r = rounds20 S → r .x1 = ret → r .x2 = sp → r .x10 = out →
      r .x11 = inp → LSafeN fns G N Q ⟨⟨1, 386, ret, top⟩ :: rest, r, m⟩) {t : Nat} (ht : t < 10)
    (next : ∀ r : Reg → Word, t + 1 < 10 → regs16 r = Nat.repeat doubleRound (t + 1) S →
      r .x12 = BitVec.ofNat 64 (10 - (t + 1)) → r .x1 = ret → r .x2 = sp → r .x10 = out →
      r .x11 = inp → LSafeN fns G N Q ⟨⟨1, 62, ret, top⟩ :: rest, r, m⟩)
    (regs : Reg → Word) (h16 : regs16 regs = Nat.repeat doubleRound (t + 1) S)
    (h12 : regs .x12 = BitVec.ofNat 64 (10 - (t + 1))) (hra : regs .x1 = ret) (hsp : regs .x2 = sp)
    (h10 : regs .x10 = out) (h11 : regs .x11 = inp) :
    LSafeN fns G N Q ⟨⟨1, 384, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq stop [62, 386] with [h12]
  · exact next _ (ctr_more ht hc) h16 h12 hra hsp h10 h11
  · obtain rfl := ctr_last ht hc
    exact hpost _ h16 hra hsp h10 h11

/-- **The loop of the double rounds**, at its head after `t` of them: the state is in the
    registers `regOf` names, and memory is not touched. -/
theorem round_loop {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {m : MachineState} {S : ChaCha20.State}
    {sp out inp : Word}
    (hpost : ∀ r : Reg → Word, regs16 r = rounds20 S → r .x1 = ret → r .x2 = sp → r .x10 = out →
      r .x11 = inp → LSafeN fns G N Q ⟨⟨1, 386, ret, top⟩ :: rest, r, m⟩) :
    ∀ k t (regs : Reg → Word), 10 - t = k → t < 10 → regs16 regs = Nat.repeat doubleRound t S →
      regs .x12 = BitVec.ofNat 64 (10 - t) → regs .x1 = ret → regs .x2 = sp → regs .x10 = out →
      regs .x11 = inp → LSafeN fns G N Q ⟨⟨1, 62, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ hk ht; omega
  | succ k ih =>
    intro t regs hk ht h16 h12 hra hsp h10 h11
    refine col1 regs fun r1 e1 c1 s1 => col2 r1 fun r2 e2 c2 s2 => diag1 r2 fun r3 e3 c3 s3 =>
      diag2 r3 fun r4 e4 c4 s4 => round_branch hpost ht
        (fun r hlt => ih (t + 1) r (by omega) hlt) r4 ?_ ?_ ?_ ?_ ?_ ?_
    · rw [e4, e3, ← diagonalRound_halves, e2, e1, ← columnRound_halves, h16]; rfl
    · rw [c4, c3, c2, c1, h12, ctr_step ht]
    · rw [s4.1, s3.1, s2.1, s1.1, hra]
    · rw [s4.2.1, s3.2.1, s2.2.1, s1.2.1, hsp]
    · rw [s4.2.2.1, s3.2.2.1, s2.2.2.1, s1.2.2.1, h10]
    · rw [s4.2.2.2, s3.2.2.2, s2.2.2.2, s1.2.2.2, h11]

/-! ## `chacha20_block`: the frame

`chacha20_block` keeps a frame of 112 bytes below the stack pointer `top` it is called with: the
sixteen words of `x` at `v = top - 104`, and `s0`, `s1`, `s2`, `s3`, `s4` in the doublewords at
`top - 8`, …, `top - 40`. It runs three loops (positions in the lifted body in brackets): `in`
copied to `x` [18], the ten double rounds, in registers [62], and `out[i] = x[i] + in[i]` [422].
Addresses are written as `lsym` writes them: `top + 18446744073709551504#64` is `top - 112`. -/

/-- The sixteen words at `a`, as a ChaCha20 state. -/
def words16 (m : MachineState) (a : Word) : ChaCha20.State :=
  fun i => m.getWord32 (a + BitVec.ofNat 64 (4 * i.val))

/-- A word read after a doubleword written in another doubleword. -/
theorem getWord32_setMem (m : MachineState) (c w a : Word) (h : alignToDword a ≠ c) :
    (m.setMem c w).getWord32 a = m.getWord32 a := by
  simp only [MachineState.getWord32, MachineState.getMem_setMem_ne h]

/-- A doubleword read after a word written in another doubleword. -/
theorem getMem_setWord32 (m : MachineState) (a c : Word) (v : BitVec 32) (h : c ≠ alignToDword a) :
    (m.setWord32 a v).getMem c = m.getMem c := by
  simp only [MachineState.setWord32, MachineState.getMem_setMem_ne h]

theorem aligned4_ofNat {w : Word} (h : alignedFor 4 w = true) (i : Nat) :
    alignedFor 4 (w + BitVec.ofNat 64 (4 * i)) = true := by
  refine aligned4_add h _ ?_
  have : BitVec.ofNat 64 (4 * i) = 4#64 * BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_decide

theorem aligned8_iff (a : Word) : alignedFor 8 a = true ↔ a &&& 7#64 = 0#64 := by
  have e : a.toNat % 8 = (a &&& 7#64).toNat := by
    rw [BitVec.toNat_and]; exact (Nat.and_two_pow_sub_one_eq_mod _ 3).symm
  simp [alignedFor, isAligned8, e, BitVec.toNat_eq]

/-- A word at `a` is outside the 112 bytes below `top`, `chacha20_block`'s frame. -/
def Out (top a : Word) : Prop := 112#64 ≤ a - (top - 112#64)

/-- A word at `b` is in the frame's array `x`, below the saved registers. -/
def InFrame (top b : Word) : Prop := 8#64 ≤ b - (top - 112#64) ∧ b - (top - 112#64) < 72#64

/-- Where `x` is: at `v`, below a `top` aligned to a doubleword. -/
def Layout (top v : Word) : Prop := top &&& 7#64 = 0#64 ∧ v = top + 18446744073709551512#64

theorem out_ne {top a b : Word} (ha : Out top a) (hb : InFrame top b) : b ≠ a := by
  unfold Out at ha; unfold InFrame at hb; bv_omega

/-- The five doublewords the prologue saves registers in. -/
def Saved (top d : Word) : Prop :=
  top + 18446744073709551608#64 ≠ d ∧ top + 18446744073709551600#64 ≠ d ∧
    top + 18446744073709551592#64 ≠ d ∧ top + 18446744073709551584#64 ≠ d ∧
    top + 18446744073709551576#64 ≠ d

theorem dword_in {top b : Word} (ht : top &&& 7#64 = 0#64) (hb : InFrame top b) :
    Saved top (alignToDword b) := by
  unfold InFrame at hb; unfold Saved alignToDword; bv_decide

theorem dword_out {top a : Word} (ht : top &&& 7#64 = 0#64) (ha : Out top a) :
    Saved top (alignToDword a) := by
  unfold Out at ha; unfold Saved alignToDword; bv_decide

theorem layout_v {top v : Word} (h : Layout top v) {t : Nat} (ht : t < 16) :
    InFrame top (v + BitVec.ofNat 64 (4 * t)) := by
  obtain ⟨-, rfl⟩ := h; unfold InFrame; bv_omega

theorem layout_aligned {top v : Word} (h : Layout top v) : alignedFor 4 v = true := by
  obtain ⟨ht, rfl⟩ := h
  rw [aligned4_iff]; bv_decide

/-- What the saved doublewords hold. -/
def SavedAre (top : Word) (m : MachineState) (s0 s1 s2 s3 s4 : Word) : Prop :=
  m.getMem (top + 18446744073709551608#64) = s0 ∧ m.getMem (top + 18446744073709551600#64) = s1 ∧
    m.getMem (top + 18446744073709551592#64) = s2 ∧ m.getMem (top + 18446744073709551584#64) = s3 ∧
    m.getMem (top + 18446744073709551576#64) = s4

/-- A word stored outside the saved doublewords keeps them. -/
theorem savedAre_store {top : Word} {m : MachineState} {s0 s1 s2 s3 s4 : Word}
    (h : SavedAre top m s0 s1 s2 s3 s4) {b : Word} (hb : Saved top (alignToDword b)) (x : BitVec 32) :
    SavedAre top (m.setWord32 b x) s0 s1 s2 s3 s4 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  obtain ⟨d0, d1, d2, d3, d4⟩ := hb
  exact ⟨by rw [getMem_setWord32 _ _ _ _ d0, h0], by rw [getMem_setWord32 _ _ _ _ d1, h1],
    by rw [getMem_setWord32 _ _ _ _ d2, h2], by rw [getMem_setWord32 _ _ _ _ d3, h3],
    by rw [getMem_setWord32 _ _ _ _ d4, h4]⟩

/-- What the body keeps of memory until the last loop: every aligned word outside the frame
    reads as in `m0`, and the saved doublewords hold `s0`, …, `s4`. -/
def Kept (top : Word) (m0 m : MachineState) (s0 s1 s2 s3 s4 : Word) : Prop :=
  (∀ a, alignedFor 4 a = true → Out top a → m.getWord32 a = m0.getWord32 a) ∧
    SavedAre top m s0 s1 s2 s3 s4

/-- The prologue's five stores keep what `Kept` asks. -/
theorem kept_init {top : Word} (ht : top &&& 7#64 = 0#64) (m0 : MachineState)
    (s0 s1 s2 s3 s4 : Word) :
    Kept top m0 (((((m0.setMem (top + 18446744073709551608#64) s0).setMem
      (top + 18446744073709551600#64) s1).setMem (top + 18446744073709551592#64) s2).setMem
      (top + 18446744073709551584#64) s3).setMem (top + 18446744073709551576#64) s4)
      s0 s1 s2 s3 s4 := by
  refine ⟨fun a _ ha => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨d0, d1, d2, d3, d4⟩ := dword_out ht ha
    rw [getWord32_setMem _ _ _ _ d4.symm, getWord32_setMem _ _ _ _ d3.symm,
      getWord32_setMem _ _ _ _ d2.symm, getWord32_setMem _ _ _ _ d1.symm,
      getWord32_setMem _ _ _ _ d0.symm]
  all_goals simp

/-- A word stored in the frame keeps what `Kept` asks. -/
theorem kept_store {top : Word} {m0 m : MachineState} {s0 s1 s2 s3 s4 : Word}
    (ht : top &&& 7#64 = 0#64) (h : Kept top m0 m s0 s1 s2 s3 s4) {b : Word} (hb : InFrame top b)
    (hal : alignedFor 4 b = true) (x : BitVec 32) : Kept top m0 (m.setWord32 b x) s0 s1 s2 s3 s4 := by
  refine ⟨fun a ha hout => ?_, savedAre_store h.2 (dword_in ht hb) x⟩
  rw [getWord32_setWord32 _ _ _ _ hal ha, ite_eq_right (out_ne hout hb).symm]
  exact h.1 a ha hout

/-- **A word stored after the first `t` of an array**: the first `t + 1` read as they should. -/
theorem words_store {b : Word} (hal : alignedFor 4 b = true) {m : MachineState}
    {f : Nat → BitVec 32} {t : Nat} (ht : t < 16)
    (inv : ∀ i < t, m.getWord32 (b + BitVec.ofNat 64 (4 * i)) = f i) (x : BitVec 32) (hx : x = f t) :
    ∀ i < t + 1, (m.setWord32 (b + BitVec.ofNat 64 (4 * t)) x).getWord32
      (b + BitVec.ofNat 64 (4 * i)) = f i := by
  intro i hi
  rw [getWord32_setWord32 _ _ _ _ (aligned4_ofNat hal t) (aligned4_ofNat hal i)]
  by_cases h : i = t
  · subst h; simp [hx]
  · have hne : b + BitVec.ofNat 64 (4 * i) ≠ b + BitVec.ofNat 64 (4 * t) := by bv_omega
    rw [ite_eq_right hne]; exact inv i (by omega)

/-- A word loaded (sign-extended) and stored again. -/
theorem sext_trunc (x : BitVec 32) : (BitVec.signExtend 64 x).setWidth 32 = x := by bv_decide

theorem copy_more {t : Nat} (ht : t < 16) (h : ¬BitVec.ofNat 64 (4 * t) + 4#64 = 64#64) :
    t + 1 < 16 := by bv_omega

theorem copy_last {t : Nat} (ht : t < 16) (h : BitVec.ofNat 64 (4 * t) + 4#64 = 64#64) :
    t = 15 := by bv_omega

theorem next_addr (b : Word) (t : Nat) :
    b + (BitVec.ofNat 64 (4 * t) + 4#64) = b + BitVec.ofNat 64 (4 * (t + 1)) := by bv_omega

/-! ### The last loop: `out[i] = x[i] + in[i]` -/

/-- One word of `out` written: what the last loop keeps of `x`, of the words of `in` it has yet
    to read, and of the words of `out` it has written. -/
theorem out_step {top v out inp : Word} (hL : Layout top v) (hoal : alignedFor 4 out = true)
    (hial : alignedFor 4 inp = true) (hoo : ∀ i < 16, Out top (out + BitVec.ofNat 64 (4 * i)))
    (hov : ∀ i j, i < j → j < 16 → out + BitVec.ofNat 64 (4 * i) ≠ inp + BitVec.ofNat 64 (4 * j))
    {X S : ChaCha20.State} {m : MachineState} {t : Nat} (ht : t < 16)
    (hv : ∀ i (h : i < 16), m.getWord32 (v + BitVec.ofNat 64 (4 * i)) = X ⟨i, h⟩)
    (hin : ∀ j (h : j < 16), t ≤ j → m.getWord32 (inp + BitVec.ofNat 64 (4 * j)) = S ⟨j, h⟩)
    (hout : ∀ i (h : i < 16), i < t →
      m.getWord32 (out + BitVec.ofNat 64 (4 * i)) = X ⟨i, h⟩ + S ⟨i, h⟩)
    (x : BitVec 32) (hx : x = X ⟨t, ht⟩ + S ⟨t, ht⟩) :
    let m' := m.setWord32 (out + BitVec.ofNat 64 (4 * t)) x
    (∀ i (h : i < 16), m'.getWord32 (v + BitVec.ofNat 64 (4 * i)) = X ⟨i, h⟩) ∧
    (∀ j (h : j < 16), t + 1 ≤ j → m'.getWord32 (inp + BitVec.ofNat 64 (4 * j)) = S ⟨j, h⟩) ∧
    (∀ i (h : i < 16), i < t + 1 →
      m'.getWord32 (out + BitVec.ofNat 64 (4 * i)) = X ⟨i, h⟩ + S ⟨i, h⟩) := by
  have ha := aligned4_ofNat hoal t
  refine ⟨fun i h => ?_, fun j h hj => ?_, fun i h hi => ?_⟩
  · rw [getWord32_setWord32 _ _ _ _ ha (aligned4_ofNat (layout_aligned hL) i),
      ite_eq_right (out_ne (hoo t ht) (layout_v hL h))]
    exact hv i h
  · rw [getWord32_setWord32 _ _ _ _ ha (aligned4_ofNat hial j),
      ite_eq_right (hov t j (by omega) h).symm]
    exact hin j h (by omega)
  · rw [getWord32_setWord32 _ _ _ _ ha (aligned4_ofNat hoal i)]
    by_cases e : i = t
    · subst e; simp [hx]
    · have hne : out + BitVec.ofNat 64 (4 * i) ≠ out + BitVec.ofNat 64 (4 * t) := by bv_omega
      rw [ite_eq_right hne]; exact hout i h (by omega)

/-- **Loop 3, `out[i] = x[i] + in[i]`**, at its head with `t` words written; it ends in the
    epilogue, which restores `s0`, …, `s4` and returns. -/
theorem out_loop {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {v out inp s0 s1 s2 s3 s4 : Word} {X S : ChaCha20.State}
    (hL : Layout top v) (hoal : alignedFor 4 out = true) (hial : alignedFor 4 inp = true)
    (hoo : ∀ i < 16, Out top (out + BitVec.ofNat 64 (4 * i)))
    (hov : ∀ i j, i < j → j < 16 → out + BitVec.ofNat 64 (4 * i) ≠ inp + BitVec.ofNat 64 (4 * j))
    (hpost : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x19 = s3 → r' .x20 = s4 → r' .x2 = top →
      (∀ i (h : i < 16), m'.getWord32 (out + BitVec.ofNat 64 (4 * i)) = X ⟨i, h⟩ + S ⟨i, h⟩) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k t (regs : Reg → Word) (m : MachineState), 16 - t = k → t < 16 →
      regs .x10 = out + BitVec.ofNat 64 (4 * t) → regs .x11 = inp + BitVec.ofNat 64 (4 * t) →
      regs .x12 = out + 64#64 → regs .x13 = v + BitVec.ofNat 64 (4 * t) → regs .x1 = ret →
      regs .x2 = top + 18446744073709551504#64 → SavedAre top m s0 s1 s2 s3 s4 →
      (∀ i (h : i < 16), m.getWord32 (v + BitVec.ofNat 64 (4 * i)) = X ⟨i, h⟩) →
      (∀ j (h : j < 16), t ≤ j → m.getWord32 (inp + BitVec.ofNat 64 (4 * j)) = S ⟨j, h⟩) →
      (∀ i (h : i < 16), i < t →
        m.getWord32 (out + BitVec.ofNat 64 (4 * i)) = X ⟨i, h⟩ + S ⟨i, h⟩) →
      LSafeN fns G N Q ⟨⟨1, 422, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ _ hk ht; omega
  | succ k ih =>
    intro t regs m hk ht h10 h11 h12 h13 hra hsp hs hv hin hout
    have hvt := hv t ht
    have hit := hin t ht (Nat.le_refl t)
    have hsv := savedAre_store hs (dword_out hL.1 (hoo t ht))
    lsym f1_eq stop [422] with [h10, h11, h12, h13, hra, hsp, hvt, hit]
    all_goals
      have hsum : BitVec.setWidth 32 (BitVec.signExtend 64 (S ⟨t, ht⟩) +
          BitVec.signExtend 64 (X ⟨t, ht⟩)) = X ⟨t, ht⟩ + S ⟨t, ht⟩ := by bv_decide
    all_goals have hnew := out_step hL hoal hial hoo hov ht hv hin hout _ hsum
    · refine ih (t + 1) _ _ (by omega) (copy_more ht hc) ?_ ?_ ?_ ?_ ?_ ?_ (hsv _) hnew.1 hnew.2.1
        hnew.2.2
      · simp only [lsym_simp]; exact next_addr out t
      · simp only [lsym_simp]; exact next_addr inp t
      · simp [lsym_simp, h12]
      · simp only [lsym_simp]; exact next_addr v t
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
    · obtain rfl := copy_last ht hc
      obtain ⟨e0, e1, e2, e3, e4⟩ := hsv (BitVec.setWidth 32 (BitVec.signExtend 64 (S ⟨15, ht⟩) +
          BitVec.signExtend 64 (X ⟨15, ht⟩)))
      refine hpost _ _ ?_ ?_ ?_ ?_ ?_ ?_ fun i h => hnew.2.2 i h (by omega)
      · simp only [lsym_simp]; exact e0
      · simp only [lsym_simp]; exact e1
      · simp only [lsym_simp]; exact e2
      · simp only [lsym_simp]; exact e3
      · simp only [lsym_simp]; exact e4
      · simp [lsym_simp]

theorem frame_aligned {top : Word} (ht : top &&& 7#64 = 0#64) (c : Word) (hc : c &&& 3#64 = 0#64) :
    alignedFor 4 (top + c) = true := by
  rw [aligned4_iff]; bv_decide

/-- **The sixteen words of `x` stored back** after the rounds, in the order the binary stores
    them: they read back, and what `Kept` asks is kept. -/
theorem v_stores {top : Word} (ht : top &&& 7#64 = 0#64) {m0 m : MachineState}
    {s0 s1 s2 s3 s4 : Word} (hk : Kept top m0 m s0 s1 s2 s3 s4) (x : ChaCha20.State) :
    let m' := (((((((((((((((m.setWord32 (top + 18446744073709551528#64) (x 4)).setWord32
      (top + 18446744073709551532#64) (x 5)).setWord32 (top + 18446744073709551536#64) (x 6)).setWord32
      (top + 18446744073709551540#64) (x 7)).setWord32 (top + 18446744073709551512#64) (x 0)).setWord32
      (top + 18446744073709551516#64) (x 1)).setWord32 (top + 18446744073709551520#64) (x 2)).setWord32
      (top + 18446744073709551524#64) (x 3)).setWord32 (top + 18446744073709551560#64) (x 12)).setWord32
      (top + 18446744073709551564#64) (x 13)).setWord32 (top + 18446744073709551568#64) (x 14)).setWord32
      (top + 18446744073709551572#64) (x 15)).setWord32 (top + 18446744073709551544#64) (x 8)).setWord32
      (top + 18446744073709551548#64) (x 9)).setWord32 (top + 18446744073709551552#64) (x 10)).setWord32
      (top + 18446744073709551556#64) (x 11)
    Kept top m0 m' s0 s1 s2 s3 s4 ∧ ∀ i (h : i < 16), m'.getWord32 (top + 18446744073709551512#64 +
      BitVec.ofNat 64 (4 * i)) = x ⟨i, h⟩ := by
  refine ⟨?_, fun i h => ?_⟩
  · have st : ∀ {m : MachineState} (c : Word), 8#64 ≤ c + 112#64 → c + 112#64 < 72#64 →
        c &&& 3#64 = 0#64 → Kept top m0 m s0 s1 s2 s3 s4 → ∀ y : BitVec 32,
        Kept top m0 (m.setWord32 (top + c) y) s0 s1 s2 s3 s4 :=
      fun c h1 h2 h3 hk y => kept_store ht hk (by unfold InFrame; bv_omega) (frame_aligned ht c h3) y
    iterate 16 refine st _ (by decide) (by decide) (by decide) ?_ _
    exact hk
  · match i, h with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
    | 12, _ | 13, _ | 14, _ | 15, _ =>
      simp [BitVec.add_assoc, getWord32_setWord32, frame_aligned ht]
    | n + 16, h => exact absurd h (by omega)

/-- After the double rounds [386]: the state stored back into `x`, then the last loop and the
    return. -/
theorem after_rounds {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {v out inp s0 s1 s2 s3 s4 : Word} {m0 : MachineState}
    {S : ChaCha20.State} (hL : Layout top v) (hoal : alignedFor 4 out = true)
    (hial : alignedFor 4 inp = true) (hoo : ∀ i < 16, Out top (out + BitVec.ofNat 64 (4 * i)))
    (hio : ∀ i < 16, Out top (inp + BitVec.ofNat 64 (4 * i)))
    (hov : ∀ i j, i < j → j < 16 → out + BitVec.ofNat 64 (4 * i) ≠ inp + BitVec.ofNat 64 (4 * j))
    (hS : ∀ j (h : j < 16), m0.getWord32 (inp + BitVec.ofNat 64 (4 * j)) = S ⟨j, h⟩)
    (hfin : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x19 = s3 → r' .x20 = s4 → r' .x2 = top →
      (∀ i (h : i < 16), m'.getWord32 (out + BitVec.ofNat 64 (4 * i)) =
        rounds20 S ⟨i, h⟩ + S ⟨i, h⟩) →
      LSafeN fns G N Q ⟨rest, r', m'⟩)
    (regs : Reg → Word) (m : MachineState) (h16 : regs16 regs = rounds20 S)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top + 18446744073709551504#64) (h10 : regs .x10 = out)
    (h11 : regs .x11 = inp) (hk : Kept top m0 m s0 s1 s2 s3 s4) :
    LSafeN fns G N Q ⟨⟨1, 386, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq stop [422] with [h10, h11, hra, hsp]
  obtain ⟨hk', hv⟩ := v_stores hL.1 hk (regs16 regs)
  have hL' := hL
  obtain ⟨-, rfl⟩ := hL'
  refine out_loop (X := rounds20 S) (S := S) hL hoal hial hoo hov hfin 16 0 _ _ rfl (by decide)
    ?_ ?_ ?_ ?_ ?_ ?_ hk'.2 (fun i h => (hv i h).trans (congrFun h16 ⟨i, h⟩))
    (fun j h _ => (hk'.1 _ (aligned4_ofNat hial j) (hio j h)).trans (hS j h))
    (fun i _ hi => absurd hi (Nat.not_lt_zero i))
  · simp [lsym_simp, h10]
  · simp [lsym_simp, h11]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, hra]
  · simp [lsym_simp, hsp]
/-- The words of `x` read at the addresses `lsym` writes. -/
theorem v_reads {top v : Word} (hL : Layout top v) {m : MachineState} {f : Nat → BitVec 32}
    (h : ∀ i < 16, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) = f i) :
    m.getWord32 (top + 18446744073709551512#64) = f 0 ∧
      m.getWord32 (top + 18446744073709551516#64) = f 1 ∧
      m.getWord32 (top + 18446744073709551520#64) = f 2 ∧
      m.getWord32 (top + 18446744073709551524#64) = f 3 ∧
      m.getWord32 (top + 18446744073709551528#64) = f 4 ∧
      m.getWord32 (top + 18446744073709551532#64) = f 5 ∧
      m.getWord32 (top + 18446744073709551536#64) = f 6 ∧
      m.getWord32 (top + 18446744073709551540#64) = f 7 ∧
      m.getWord32 (top + 18446744073709551544#64) = f 8 ∧
      m.getWord32 (top + 18446744073709551548#64) = f 9 ∧
      m.getWord32 (top + 18446744073709551552#64) = f 10 ∧
      m.getWord32 (top + 18446744073709551556#64) = f 11 ∧
      m.getWord32 (top + 18446744073709551560#64) = f 12 ∧
      m.getWord32 (top + 18446744073709551564#64) = f 13 ∧
      m.getWord32 (top + 18446744073709551568#64) = f 14 ∧
      m.getWord32 (top + 18446744073709551572#64) = f 15 := by
  obtain ⟨-, rfl⟩ := hL
  have e := fun i hi => h i hi
  simp only [BitVec.add_assoc] at e
  exact ⟨e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide), e 8 (by decide), e 9 (by decide),
    e 10 (by decide), e 11 (by decide), e 12 (by decide), e 13 (by decide), e 14 (by decide),
    e 15 (by decide)⟩

/-- Between loops 1 and 2 [28]: the state loaded into registers, then the double rounds. -/
theorem after_copy {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {v out inp s0 s1 s2 s3 s4 : Word} {m0 : MachineState}
    (hL : Layout top v) (hoal : alignedFor 4 out = true)
    (hial : alignedFor 4 inp = true) (hoo : ∀ i < 16, Out top (out + BitVec.ofNat 64 (4 * i)))
    (hio : ∀ i < 16, Out top (inp + BitVec.ofNat 64 (4 * i)))
    (hov : ∀ i j, i < j → j < 16 → out + BitVec.ofNat 64 (4 * i) ≠ inp + BitVec.ofNat 64 (4 * j))
    (hfin : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x19 = s3 → r' .x20 = s4 → r' .x2 = top →
      (∀ i (h : i < 16), m'.getWord32 (out + BitVec.ofNat 64 (4 * i)) =
        rounds20 (words16 m0 inp) ⟨i, h⟩ + words16 m0 inp ⟨i, h⟩) →
      LSafeN fns G N Q ⟨rest, r', m'⟩)
    (regs : Reg → Word) (m : MachineState) (h10 : regs .x10 = out) (h11 : regs .x11 = inp)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top + 18446744073709551504#64)
    (hk : Kept top m0 m s0 s1 s2 s3 s4)
    (hw : ∀ i < 16, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) =
      m0.getWord32 (inp + BitVec.ofNat 64 (4 * i))) :
    LSafeN fns G N Q ⟨⟨1, 28, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f1_eq stop [62] with [h10, h11, hra, hsp]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := v_reads hL hw
  refine round_loop (S := words16 m0 inp)
    (fun r h16 hra' hsp' h10' h11' => after_rounds hL hoal hial hoo hio hov (fun _ _ => rfl) hfin
      r m h16 hra' hsp' h10' h11' hk) 10 0 _ rfl (by decide) ?_ ?_ ?_ ?_ ?_ ?_
  · show _ = words16 m0 inp
    refine state_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [regs16, regOf, lsym_simp, sext_trunc, e0, e1, e2, e3, e4, e5, e6, e7, e8,
      e9, e10, e11, e12, e13, e14, e15]
    all_goals rfl
  · simp [lsym_simp]
  · simp [lsym_simp, hra]
  · simp [lsym_simp, hsp]
  · simp [lsym_simp, h10]
  · simp [lsym_simp, h11]

/-- **Loop 1, `in` copied into `x`**, at its head with `t` words copied. -/
theorem copy_loop {G : Lprog.State rvIsa → Prop} {N : Nat} {Q : Lprog.State rvIsa → Prop}
    {ret top : Word} {rest : List Frame} {v out inp : Word} {m0 : MachineState}
    {s0 s1 s2 s3 s4 : Word} (hL : Layout top v) (hial : alignedFor 4 inp = true)
    (hio : ∀ i < 16, Out top (inp + BitVec.ofNat 64 (4 * i)))
    (hpost : ∀ (regs : Reg → Word) m, regs .x10 = out → regs .x11 = inp → regs .x1 = ret →
      regs .x2 = top + 18446744073709551504#64 → Kept top m0 m s0 s1 s2 s3 s4 →
      (∀ i < 16, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (inp + BitVec.ofNat 64 (4 * i))) →
      LSafeN fns G N Q ⟨⟨1, 28, ret, top⟩ :: rest, regs, m⟩) :
    ∀ k t (regs : Reg → Word) (m : MachineState), 16 - t = k → t < 16 →
      regs .x14 = inp + BitVec.ofNat 64 (4 * t) → regs .x12 = inp + 64#64 →
      regs .x13 = v + BitVec.ofNat 64 (4 * t) → regs .x10 = out → regs .x11 = inp →
      regs .x1 = ret → regs .x2 = top + 18446744073709551504#64 → Kept top m0 m s0 s1 s2 s3 s4 →
      (∀ i < t, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (inp + BitVec.ofNat 64 (4 * i))) →
      LSafeN fns G N Q ⟨⟨1, 18, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ _ hk ht; omega
  | succ k ih =>
    intro t regs m hk ht h14 h12 h13 h10 h11 hra hsp hkept inv
    have hread : m.getWord32 (inp + BitVec.ofNat 64 (4 * t)) =
        m0.getWord32 (inp + BitVec.ofNat 64 (4 * t)) :=
      hkept.1 _ (aligned4_ofNat hial t) (hio t ht)
    lsym f1_eq stop [18, 28] with [h14, h12, h13, h10, h11, hra, hsp, hread]
    all_goals
      have hk' := kept_store hL.1 hkept (layout_v hL ht) (aligned4_ofNat (layout_aligned hL) t)
    all_goals have hnew := words_store (layout_aligned hL) ht inv
    · refine ih (t + 1) _ _ (by omega) (copy_more ht hc) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hk' _) (hnew _ ?_)
      · simp only [lsym_simp]; exact next_addr inp t
      · simp [lsym_simp, h12]
      · simp only [lsym_simp]; exact next_addr v t
      · simp [lsym_simp, h10]
      · simp [lsym_simp, h11]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact sext_trunc _
    · obtain rfl := copy_last ht hc
      refine hpost _ _ ?_ ?_ ?_ ?_ (hk' _) (hnew _ ?_)
      · simp [lsym_simp, h10]
      · simp [lsym_simp, h11]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact sext_trunc _

/-- `chacha20_block(out, in)`: the sixteen words at `out` become the ChaCha20 block function
    (`block`, RFC 8439 2.3) of the sixteen words at `in`; `s0`, …, `s4` and the stack pointer are
    as they were.

    Assumed: the stack pointer `top` is aligned to a doubleword, `out` and `in` to a word; the
    words at `out` and at `in` are outside the 112 bytes below `top` that the function's frame
    takes (`Out`); and no word of `out` is a word of `in` that comes later
    (`out + 4 i ≠ in + 4 j` for `i < j`), since the last loop reads `in[j]` after it has
    written `out[i]`. So `out` may be `in`, or any array before it or disjoint from it. No access
    is assumed valid: an access that is not traps, and a trap is safe. -/
theorem chacha20_block_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ alignedFor 8 top = true ∧
      alignedFor 4 (regs .x10) = true ∧ alignedFor 4 (regs .x11) = true ∧
      (∀ i < 16, Out top (regs .x10 + BitVec.ofNat 64 (4 * i))) ∧
      (∀ i < 16, Out top (regs .x11 + BitVec.ofNat 64 (4 * i))) ∧
      (∀ i j, i < j → j < 16 →
        regs .x10 + BitVec.ofNat 64 (4 * i) ≠ regs .x11 + BitVec.ofNat 64 (4 * j)))
    (fun _ top regs m r' m' =>
      words16 m' (regs .x10) = block (words16 m (regs .x11)) ∧
      r' .x8 = regs .x8 ∧ r' .x9 = regs .x9 ∧ r' .x18 = regs .x18 ∧ r' .x19 = regs .x19 ∧
      r' .x20 = regs .x20 ∧ r' .x2 = top) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, ht8, hoal, hial, hoo, hio, hov⟩ hk
  have hL : Layout top (top + 18446744073709551512#64) := ⟨(aligned8_iff top).1 ht8, rfl⟩
  lsym f1_eq stop [18] with [hra, hsp]
  refine copy_loop hL hial hio
    (fun r m' h10 h11 hra' hsp' hk' hw => after_copy hL hoal hial hoo hio hov
      (fun r' m'' h8 h9 h18 h19 h20 h2 hout =>
        hk r' m'' ⟨funext fun ⟨i, h⟩ => hout i h, h8, h9, h18, h19, h20, h2⟩)
      r m' h10 h11 hra' hsp' hk' hw)
    16 0 _ _ rfl (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (kept_init hL.1 m _ _ _ _ _)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, hra]
  · simp [lsym_simp]

/-- **`chacha20_block` on the machine.** -/
theorem chacha20_block_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10074#64) (hcode : Loaded fns s) (ht : alignedFor 8 (s.getReg .x2) = true)
    (hoal : alignedFor 4 (s.getReg .x10) = true) (hial : alignedFor 4 (s.getReg .x11) = true)
    (hoo : ∀ i < 16, Out (s.getReg .x2) (s.getReg .x10 + BitVec.ofNat 64 (4 * i)))
    (hio : ∀ i < 16, Out (s.getReg .x2) (s.getReg .x11 + BitVec.ofNat 64 (4 * i)))
    (hov : ∀ i j, i < j → j < 16 →
      s.getReg .x10 + BitVec.ofNat 64 (4 * i) ≠ s.getReg .x11 + BitVec.ofNat 64 (4 * j))
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      words16 t (s.getReg .x10) = block (words16 s (s.getReg .x11)) →
      t.getReg .x8 = s.getReg .x8 → t.getReg .x9 = s.getReg .x9 →
      t.getReg .x18 = s.getReg .x18 → t.getReg .x19 = s.getReg .x19 →
      t.getReg .x20 = s.getReg .x20 → t.getReg .x2 = s.getReg .x2 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x10074#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode chacha20_block_contract
    ⟨rfl, rfl, ht, hoal, hial, hoo, hio, hov⟩ ?_
  rintro t r' m' hag hpc' ⟨hwords, h8, h9, h18, h19, h20, h2⟩
  refine hk t hpc' ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (funext fun i => getWord32_of_agree hag _).trans hwords
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h8
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h9
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h18
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h19
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h20
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h2


end Examples.ChaCha20.RiscV
