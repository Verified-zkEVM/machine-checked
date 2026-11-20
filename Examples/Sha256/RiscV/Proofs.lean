/-
  Examples.Sha256.RiscV.Proofs

  `sha256_round`, `sha256_schedule` and `sha256_compress` of `src/c/sha256.c`, compiled by
  clang: one round of SHA-256 on the eight working variables in memory, the message schedule,
  and the compression function. Their contracts at Lprog, proved with `lsym`, and the same
  statements over riscv-zkvm's machine (`sha256_round_correct`, `sha256_schedule_correct`,
  `sha256_compress_correct`).

  The round is 57 instructions with no branch. It keeps `s0` in a frame of its own, so the
  precondition asks that the doubleword it saves `s0` in is none of those the eight words are
  in. The specification is the round of FIPS 180-4 (`round`), with `rotateRight`; `bv_decide`
  relates it to the shifts the binary has.

  The schedule is a loop of forty-eight words, each from four before it; its lemma is at the
  loop's head, by induction on the words left (`sched_loop`). The facts about its addresses are
  theorems of their own, used after `lsym` has stepped: as hypotheses before it, `lsym`'s `simp`
  takes them as rewrite rules and does not end.

  The compression function is 130 instructions: clang inlined both the schedule and the round.
  It keeps the schedule and the working variables in a frame of 320 bytes, with `s0`, `s1`, `s2`
  saved at its top, and runs five loops: the block copied into the schedule, the schedule, the
  hash value copied into the working variables, the sixty-four rounds with the working variables
  in registers, and the working variables added into the hash value. Each loop is a lemma at its
  head, by induction on what is left; the code between them is stepped by lemmas of its own.
  The specification is FIPS 180-4's (`compress`, in `Spec.lean`). Until the last loop, memory
  outside the frame is as it was on entry (`Kept`); the precondition asks that the hash value,
  the block and the table of constants `K` the binary reads are outside the frame. The round
  loop's body is stepped to its branch and the branch is a lemma of its own (`round_branch`),
  which keeps each within the default limits.
-/

import Examples.Sha256.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Sha256.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Sha256.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-- **Eight words written** at `s + 16`, …, `s + 28`, then `s`, …, `s + 12`, the order the round
    stores them in: they read back. -/
theorem eight_words (m : MachineState) (s : Word) (A B C D E F G H : BitVec 32)
    (h : alignedFor 4 s = true) :
    let m' := ((((((((m.setWord32 (s + 16#64) E).setWord32 (s + 20#64) F).setWord32 (s + 24#64) G).setWord32 (s + 28#64) H).setWord32 s A).setWord32 (s + 4#64) B).setWord32 (s + 8#64) C).setWord32 (s + 12#64) D)
    m'.getWord32 s = A ∧
      m'.getWord32 (s + 4#64) = B ∧
      m'.getWord32 (s + 8#64) = C ∧
      m'.getWord32 (s + 12#64) = D ∧
      m'.getWord32 (s + 16#64) = E ∧
      m'.getWord32 (s + 20#64) = F ∧
      m'.getWord32 (s + 24#64) = G ∧
      m'.getWord32 (s + 28#64) = H := by
  have h4 := aligned4_add h 4#64 (by decide)
  have h8 := aligned4_add h 8#64 (by decide)
  have h12 := aligned4_add h 12#64 (by decide)
  have h16 := aligned4_add h 16#64 (by decide)
  have h20 := aligned4_add h 20#64 (by decide)
  have h24 := aligned4_add h 24#64 (by decide)
  have h28 := aligned4_add h 28#64 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getWord32_setWord32 _ _ _ _ h12 h, getWord32_setWord32 _ _ _ _ h8 h, getWord32_setWord32 _ _ _ _ h4 h, getWord32_setWord32 _ _ _ _ h h]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h4, getWord32_setWord32 _ _ _ _ h8 h4, getWord32_setWord32 _ _ _ _ h4 h4]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h8, getWord32_setWord32 _ _ _ _ h8 h8]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h12]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h16, getWord32_setWord32 _ _ _ _ h8 h16, getWord32_setWord32 _ _ _ _ h4 h16, getWord32_setWord32 _ _ _ _ h h16, getWord32_setWord32 _ _ _ _ h28 h16, getWord32_setWord32 _ _ _ _ h24 h16, getWord32_setWord32 _ _ _ _ h20 h16, getWord32_setWord32 _ _ _ _ h16 h16]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h20, getWord32_setWord32 _ _ _ _ h8 h20, getWord32_setWord32 _ _ _ _ h4 h20, getWord32_setWord32 _ _ _ _ h h20, getWord32_setWord32 _ _ _ _ h28 h20, getWord32_setWord32 _ _ _ _ h24 h20, getWord32_setWord32 _ _ _ _ h20 h20]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h24, getWord32_setWord32 _ _ _ _ h8 h24, getWord32_setWord32 _ _ _ _ h4 h24, getWord32_setWord32 _ _ _ _ h h24, getWord32_setWord32 _ _ _ _ h28 h24, getWord32_setWord32 _ _ _ _ h24 h24]
    simp
  · rw [getWord32_setWord32 _ _ _ _ h12 h28, getWord32_setWord32 _ _ _ _ h8 h28, getWord32_setWord32 _ _ _ _ h4 h28, getWord32_setWord32 _ _ _ _ h h28, getWord32_setWord32 _ _ _ _ h28 h28]
    simp

/-! ## The round, as FIPS 180-4 has it -/

/-- The eight words at `v`. -/
def words8 (m : MachineState) (v : Word) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  (m.getWord32 v, m.getWord32 (v + 4#64), m.getWord32 (v + 8#64), m.getWord32 (v + 12#64),
    m.getWord32 (v + 16#64), m.getWord32 (v + 20#64), m.getWord32 (v + 24#64),
    m.getWord32 (v + 28#64))

/-- `sha256_round(v, k, w)`: the eight words at `v` become the round of what they were, with
    `k` and `w` the low halves of `a1` and `a2`; `s0` and the stack pointer are as they were. -/
theorem sha256_round_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧ Writable m (regs .x10) 8 ∧
      isValidDwordAccessSp1 (top - 8#64) = true ∧ noCodeAt m (top - 8#64) 8 = true ∧
      ∀ i < 8, alignToDword (regs .x10 + BitVec.ofNat 64 (4 * i)) ≠ top - 8#64)
    (fun _ top regs m r' m' =>
      words8 m' (regs .x10) =
        (let (a, b, c, d, e, f, g, h) := words8 m (regs .x10)
         round a b c d e f g h ((regs .x11).setWidth 32) ((regs .x12).setWidth 32)) ∧
      r' .x8 = regs .x8 ∧ r' .x2 = top) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, ⟨hal, hw⟩, hsv, hsc, hd⟩ hk
  have d0 := hd 0 (by decide); have d1 := hd 1 (by decide); have d2 := hd 2 (by decide)
  have d3 := hd 3 (by decide); have d4 := hd 4 (by decide); have d5 := hd 5 (by decide)
  have d6 := hd 6 (by decide); have d7 := hd 7 (by decide)
  have a4 := aligned4_add hal 4#64 (by decide)
  have hs : top - 8#64 = top + 18446744073709551608#64 := by bv_omega
  rw [hs] at hsv hsc d0 d1 d2 d3 d4 d5 d6 d7
  have w0 := hw 0 (by decide); have w1 := hw 1 (by decide); have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide); have w4 := hw 4 (by decide); have w5 := hw 5 (by decide)
  have w6 := hw 6 (by decide); have w7 := hw 7 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.add_zero] at w0 w1 w2 w3 w4 w5 w6 w7 d0 d1 d2 d3 d4 d5 d6 d7
  have a8 := aligned4_add hal 8#64 (by decide); have a12 := aligned4_add hal 12#64 (by decide)
  have a16 := aligned4_add hal 16#64 (by decide); have a20 := aligned4_add hal 20#64 (by decide)
  have a24 := aligned4_add hal 24#64 (by decide); have a28 := aligned4_add hal 28#64 (by decide)
  lsym f0_eq with [hra, hsp, hsv, hsc, hal, a4, a8, a12, a16, a20, a24, a28, w0, w1, w2, w3, w4,
    w5, w6, w7, noCodeAt_setWord32]
  apply hk
  refine ⟨?_, ?_, ?_⟩
  · simp only [getWord32_setMem _ _ _ _ d0, getWord32_setMem _ _ _ _ d1,
      getWord32_setMem _ _ _ _ d2, getWord32_setMem _ _ _ _ d3, getWord32_setMem _ _ _ _ d4,
      getWord32_setMem _ _ _ _ d5, getWord32_setMem _ _ _ _ d6, getWord32_setMem _ _ _ _ d7]
    simp only [words8, round, bsig0, bsig1, ch, maj, rotr, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- The SAT solver's timeout is raised from its 10 s default for these eight words: the
    -- slowest takes about 2.6 s here, and over 10 s on a loaded CI runner. Splitting them
    -- into pieces, as `round_loop` does, overruns this declaration's heartbeats.
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).1]; bv_decide (config := { timeout := 60 })
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.1]; bv_decide (config := { timeout := 60 })
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.1]; bv_decide (config := { timeout := 60 })
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.1]; bv_decide (config := { timeout := 60 })
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.1]; bv_decide (config := { timeout := 60 })
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.2.1]; bv_decide (config := { timeout := 60 })
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.2.2.1]; bv_decide (config := { timeout := 60 })
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.2.2.2]; bv_decide (config := { timeout := 60 })
  · simp only [lsym_simp]
    rw [getMem_setWord32 _ _ _ _ d3.symm, getMem_setWord32 _ _ _ _ d2.symm,
      getMem_setWord32 _ _ _ _ d1.symm, getMem_setWord32 _ _ _ _ d0.symm,
      getMem_setWord32 _ _ _ _ d7.symm, getMem_setWord32 _ _ _ _ d6.symm,
      getMem_setWord32 _ _ _ _ d5.symm, getMem_setWord32 _ _ _ _ d4.symm,
      MachineState.getMem_setMem_eq]
  · simp [lsym_simp]

/-! ## The message schedule -/

/-- **One word of the schedule**: with the words before `t` in memory, the word the loop's body
    stores at `t` is the schedule's, and the words before it stay. -/
theorem sched_step (w : Word) (init : Nat → BitVec 32) (hal : alignedFor 4 w = true)
    (m : MachineState) {t : Nat} (ht : 16 ≤ t) (ht' : t < 64)
    (inv : ∀ i < t, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W init i) (v : BitVec 32)
    (hv : v = W init t) :
    ∀ i < t + 1, (m.setWord32 (w + BitVec.ofNat 64 (4 * t)) v).getWord32
      (w + BitVec.ofNat 64 (4 * i)) = W init i := by
  intro i hi
  rw [getWord32_setWord32 _ _ _ _ (aligned4_ofNat hal t) (aligned4_ofNat hal i)]
  by_cases h : i = t
  · subst h; simp [hv]
  · have hne : w + BitVec.ofNat 64 (4 * i) ≠ w + BitVec.ofNat 64 (4 * t) := by bv_omega
    rw [ite_eq_right hne]; exact inv i (by omega)

/-- The addresses the loop's body reads, and the next it writes, as words of the array. -/
theorem sched_addr (w : Word) {t : Nat} (ht : 16 ≤ t) (ht' : t < 64) :
    w + (BitVec.ofNat 64 (4 * t) + 18446744073709551608#64) = w + BitVec.ofNat 64 (4 * (t - 2)) ∧
    w + (BitVec.ofNat 64 (4 * t) + 18446744073709551588#64) = w + BitVec.ofNat 64 (4 * (t - 7)) ∧
    w + (BitVec.ofNat 64 (4 * t) + 18446744073709551556#64) = w + BitVec.ofNat 64 (4 * (t - 15)) ∧
    w + (BitVec.ofNat 64 (4 * t) + 18446744073709551552#64) = w + BitVec.ofNat 64 (4 * (t - 16)) ∧
    w + (BitVec.ofNat 64 (4 * t) + 4#64) = w + BitVec.ofNat 64 (4 * (t + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem sched_more {t : Nat} (ht' : t < 64) (h : ¬BitVec.ofNat 64 (4 * t) + 4#64 = 256#64) :
    t + 1 < 64 := by bv_omega

theorem sched_last {t : Nat} (ht' : t < 64) (h : BitVec.ofNat 64 (4 * t) + 4#64 = 256#64) :
    t = 63 := by bv_omega

/-- **The loop of the schedule**, at its head with the words before `t` written. -/
theorem sched_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (w : Word) (init : Nat → BitVec 32) (hal : alignedFor 4 w = true)
    (hpost : ∀ r' m', (∀ i < 64, m'.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W init i) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k t (regs : Reg → BitVec 64) (m : MachineState), 64 - t = k → 16 ≤ t → t < 64 →
      regs .x11 = w + BitVec.ofNat 64 (4 * t) → regs .x10 = w + 256#64 →
      regs .x1 = ret → regs .x2 = top →
      (∀ i < t, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W init i) →
      LSafeN fns G N Q ⟨⟨1, 4, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ _ hk _ ht'; omega
  | succ k ih =>
    intro t regs m hk ht ht' h11 h10 hra hsp inv
    lsym f1_eq stop [4] with [h11, h10, hra, hsp]
    all_goals obtain ⟨e2, e7, e15, e16, enext⟩ := sched_addr w ht ht'
    all_goals have hnew := sched_step w init hal m ht ht' inv
    · -- words are left: the back edge
      refine ih (t + 1) _ _ (by omega) (by omega) (sched_more ht' hc) ?_ ?_ ?_ ?_ (hnew _ ?_)
      · simp only [lsym_simp]
        exact enext
      · simp [lsym_simp, h10]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · simp only [e2, e7, e15, e16, inv (t - 2) (by omega), inv (t - 7) (by omega),
          inv (t - 15) (by omega), inv (t - 16) (by omega), W_step init ht, ssig0, ssig1, rotr]
        bv_decide
    · -- the last word
      obtain rfl := sched_last ht' (by simpa using hc)
      apply hpost
      refine hnew _ ?_
      simp only [e2, e7, e15, e16, inv (63 - 2) (by omega), inv (63 - 7) (by omega),
        inv (63 - 15) (by omega), inv (63 - 16) (by omega), W_step init ht, ssig0, ssig1, rotr]
      bv_decide

/-- `sha256_schedule(w)`: with the block in the first sixteen words at `w`, the sixty-four
    words at `w` become the message schedule of the block. -/
theorem sha256_schedule_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧ alignedFor 4 (regs .x10) = true)
    (fun _ _ regs m _ m' => ∀ i < 64, m'.getWord32 (regs .x10 + BitVec.ofNat 64 (4 * i)) =
      W (fun j => m.getWord32 (regs .x10 + BitVec.ofNat 64 (4 * j))) i) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hal⟩ hk
  lsym f1_eq stop [4] with [hra, hsp]
  refine sched_loop (regs .x10) (fun j => m.getWord32 (regs .x10 + BitVec.ofNat 64 (4 * j))) hal
    (fun r' m' h => hk r' m' h) 48 16 _ _ rfl (by decide) (by decide) ?_ ?_ ?_ ?_
    fun i hi => (W_init (fun j => m.getWord32 (regs .x10 + BitVec.ofNat 64 (4 * j))) hi).symm
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, hra]
  · simp [lsym_simp, hsp]

/-- **`sha256_schedule` on the machine.** -/
theorem sha256_schedule_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x100e4#64) (hcode : Loaded fns s) (hal : alignedFor 4 (s.getReg .x10) = true)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      (∀ i < 64, t.getWord32 (s.getReg .x10 + BitVec.ofNat 64 (4 * i)) =
        W (fun j => s.getWord32 (s.getReg .x10 + BitVec.ofNat 64 (4 * j))) i) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x100e4#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sha256_schedule_contract
    ⟨rfl, rfl, hal⟩ ?_
  rintro t r' m' hag hpc' h
  exact hk t hpc' fun i hi => by rw [getWord32_of_agree hag]; exact h i hi

/-- **`sha256_round` on the machine.** -/
theorem sha256_round_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s) (hw : Writable s (s.getReg .x10) 8)
    (hsv : isValidDwordAccessSp1 (s.getReg .x2 - 8#64) = true)
    (hsc : noCodeAt s (s.getReg .x2 - 8#64) 8 = true)
    (hd : ∀ i < 8, alignToDword (s.getReg .x10 + BitVec.ofNat 64 (4 * i)) ≠ s.getReg .x2 - 8#64)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      words8 t (s.getReg .x10) =
        (let (a, b, c, d, e, f, g, h) := words8 s (s.getReg .x10)
         round a b c d e f g h ((s.getReg .x11).setWidth 32) ((s.getReg .x12).setWidth 32)) →
      t.getReg .x8 = s.getReg .x8 → t.getReg .x2 = s.getReg .x2 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sha256_round_contract
    ⟨rfl, rfl, hw, hsv, hsc, hd⟩ ?_
  rintro t r' m' hag hpc' ⟨hwords, h8, h2⟩
  refine hk t hpc' ?_ ?_ ?_
  · simpa only [words8, getWord32_of_agree hag, regsOf] using hwords
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h8
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h2

/-! ## The compression function

`sha256_compress` keeps a frame of 320 bytes below the stack pointer `top` it is called with:
the eight working variables at `v = top - 312`, the sixty-four words of the schedule at
`w = top - 280`, and `s0`, `s1`, `s2` in the doublewords at `top - 8`, `top - 16`, `top - 24`.
It runs five loops (positions in the lifted body in brackets): the block copied to `w` [12], the
schedule [26], the hash value copied to `v` [88], the sixty-four rounds, in registers [122], and
the working variables added into the hash value [236]. Each has a lemma at its head, by induction
on what is left; `after_copy`, `after_sched`, `after_hcopy` and `after_rounds` step the code
between them. Addresses are written as `lsym` writes them: `top + 18446744073709551296#64` is
`top - 320`. -/

/-- Memory holds `K` at `0x10368`, where the binary's `.rodata` has it. -/
def TableAt (m : MachineState) : Prop :=
  ∀ i < 64, m.getWord32 (0x10368#64 + BitVec.ofNat 64 (4 * i)) = K.getD i 0

/-- A word at `a` is outside the 320 bytes below `top`, `sha256_compress`'s frame. -/
def Out (top a : Word) : Prop := 320#64 ≤ a - (top - 320#64)

/-- A word at `b` is in the frame, between the saved registers and its lowest doubleword. -/
def InFrame (top b : Word) : Prop := 8#64 ≤ b - (top - 320#64) ∧ b - (top - 320#64) < 296#64

/-- Where the frame's arrays are: the schedule at `w`, the working variables at `v`, below a
    `top` aligned to a doubleword. -/
def Layout (top w v : Word) : Prop :=
  top &&& 7#64 = 0#64 ∧ w = top + 18446744073709551336#64 ∧ v = top + 18446744073709551304#64

theorem out_ne {top a b : Word} (ha : Out top a) (hb : InFrame top b) : b ≠ a := by
  unfold Out at ha; unfold InFrame at hb; bv_omega

theorem dword_in {top b : Word} (ht : top &&& 7#64 = 0#64) (hb : InFrame top b) :
    top + 18446744073709551608#64 ≠ alignToDword b ∧ top + 18446744073709551600#64 ≠ alignToDword b ∧
      top + 18446744073709551592#64 ≠ alignToDword b := by
  unfold InFrame at hb; unfold alignToDword; bv_decide

theorem dword_out {top a : Word} (ht : top &&& 7#64 = 0#64) (ha : Out top a) :
    top + 18446744073709551608#64 ≠ alignToDword a ∧ top + 18446744073709551600#64 ≠ alignToDword a ∧
      top + 18446744073709551592#64 ≠ alignToDword a := by
  unfold Out at ha; unfold alignToDword; bv_decide

theorem layout_w {top w v : Word} (h : Layout top w v) {t : Nat} (ht : t < 64) :
    InFrame top (w + BitVec.ofNat 64 (4 * t)) := by
  obtain ⟨-, rfl, -⟩ := h; unfold InFrame; bv_omega

theorem layout_v {top w v : Word} (h : Layout top w v) {t : Nat} (ht : t < 8) :
    InFrame top (v + BitVec.ofNat 64 (4 * t)) := by
  obtain ⟨-, -, rfl⟩ := h; unfold InFrame; bv_omega

theorem layout_wv {top w v : Word} (h : Layout top w v) {i j : Nat} (hi : i < 64) (hj : j < 8) :
    w + BitVec.ofNat 64 (4 * i) ≠ v + BitVec.ofNat 64 (4 * j) := by
  obtain ⟨-, rfl, rfl⟩ := h; bv_omega

theorem layout_aligned {top w v : Word} (h : Layout top w v) :
    alignedFor 4 w = true ∧ alignedFor 4 v = true := by
  obtain ⟨ht, rfl, rfl⟩ := h
  rw [aligned4_iff, aligned4_iff]; constructor <;> bv_decide

/-- What the body keeps of memory until the last loop: every aligned word outside the frame
    reads as in `m0`, and the three doublewords the prologue saved `s0`, `s1`, `s2` in. -/
def Kept (top : Word) (m0 m : MachineState) (s0 s1 s2 : Word) : Prop :=
  (∀ a, alignedFor 4 a = true → Out top a → m.getWord32 a = m0.getWord32 a) ∧
    m.getMem (top + 18446744073709551608#64) = s0 ∧ m.getMem (top + 18446744073709551600#64) = s1 ∧
    m.getMem (top + 18446744073709551592#64) = s2

/-- The prologue's three stores keep what `Kept` asks. -/
theorem kept_init {top : Word} (ht : top &&& 7#64 = 0#64) (m0 : MachineState) (s0 s1 s2 : Word) :
    Kept top m0 (((m0.setMem (top + 18446744073709551608#64) s0).setMem
      (top + 18446744073709551600#64) s1).setMem (top + 18446744073709551592#64) s2) s0 s1 s2 := by
  refine ⟨fun a _ ha => ?_, ?_, ?_, ?_⟩
  · obtain ⟨d0, d1, d2⟩ := dword_out ht ha
    rw [getWord32_setMem _ _ _ _ d2.symm, getWord32_setMem _ _ _ _ d1.symm,
      getWord32_setMem _ _ _ _ d0.symm]
  all_goals simp

/-- A word stored in the frame keeps what `Kept` asks. -/
theorem kept_store {top : Word} {m0 m : MachineState} {s0 s1 s2 : Word} (ht : top &&& 7#64 = 0#64)
    (h : Kept top m0 m s0 s1 s2) {b : Word} (hb : InFrame top b) (hal : alignedFor 4 b = true)
    (x : BitVec 32) : Kept top m0 (m.setWord32 b x) s0 s1 s2 := by
  obtain ⟨hw, h0, h1, h2⟩ := h
  obtain ⟨d0, d1, d2⟩ := dword_in ht hb
  refine ⟨fun a ha hout => ?_, ?_, ?_, ?_⟩
  · rw [getWord32_setWord32 _ _ _ _ hal ha, ite_eq_right (out_ne hout hb).symm]
    exact hw a ha hout
  · rw [getMem_setWord32 _ _ _ _ d0, h0]
  · rw [getMem_setWord32 _ _ _ _ d1, h1]
  · rw [getMem_setWord32 _ _ _ _ d2, h2]

/-- **A word stored after the first `t` of an array**: the first `t + 1` read as they should. -/
theorem words_store {b : Word} (hal : alignedFor 4 b = true) {m : MachineState} {f : Nat → BitVec 32}
    {t : Nat} (ht : t < 64) (inv : ∀ i < t, m.getWord32 (b + BitVec.ofNat 64 (4 * i)) = f i)
    (x : BitVec 32) (hx : x = f t) :
    ∀ i < t + 1, (m.setWord32 (b + BitVec.ofNat 64 (4 * t)) x).getWord32
      (b + BitVec.ofNat 64 (4 * i)) = f i := by
  intro i hi
  rw [getWord32_setWord32 _ _ _ _ (aligned4_ofNat hal t) (aligned4_ofNat hal i)]
  by_cases h : i = t
  · subst h; simp [hx]
  · have hne : b + BitVec.ofNat 64 (4 * i) ≠ b + BitVec.ofNat 64 (4 * t) := by bv_omega
    rw [ite_eq_right hne]; exact inv i (by omega)

/-- The words of an array, after a word stored elsewhere. -/
theorem words_keep {b c : Word} (hal : alignedFor 4 b = true) (hc : alignedFor 4 c = true)
    {m : MachineState} {f : Nat → BitVec 32} {n : Nat}
    (inv : ∀ i < n, m.getWord32 (b + BitVec.ofNat 64 (4 * i)) = f i)
    (hne : ∀ i < n, b + BitVec.ofNat 64 (4 * i) ≠ c) (x : BitVec 32) :
    ∀ i < n, (m.setWord32 c x).getWord32 (b + BitVec.ofNat 64 (4 * i)) = f i := by
  intro i hi
  rw [getWord32_setWord32 _ _ _ _ hc (aligned4_ofNat hal i), ite_eq_right (hne i hi)]
  exact inv i hi

/-- Word `i` of eight. -/
def get8 (s : Words8) : Nat → BitVec 32
  | 0 => s.1
  | 1 => s.2.1
  | 2 => s.2.2.1
  | 3 => s.2.2.2.1
  | 4 => s.2.2.2.2.1
  | 5 => s.2.2.2.2.2.1
  | 6 => s.2.2.2.2.2.2.1
  | _ => s.2.2.2.2.2.2.2

/-- The low halves of the eight registers the round loop keeps `a`, …, `h` in. -/
def regs8 (r : Reg → Word) : Words8 :=
  ((r .x7).setWidth 32, (r .x12).setWidth 32, (r .x13).setWidth 32, (r .x28).setWidth 32,
    (r .x29).setWidth 32, (r .x14).setWidth 32, (r .x15).setWidth 32, (r .x16).setWidth 32)

/-- **Loop 1, the block copied into the schedule's first sixteen words**, at its head with `t`
    words copied. -/
theorem copy_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v mp hp : Word} {m0 : MachineState} {s0 s1 s2 : Word}
    (hL : Layout top w v) (hmal : alignedFor 4 mp = true)
    (hmo : ∀ i < 16, Out top (mp + BitVec.ofNat 64 (4 * i)))
    (hpost : ∀ (regs : Reg → Word) m, regs .x10 = hp → regs .x1 = ret →
      regs .x2 = top + 18446744073709551296#64 → Kept top m0 m s0 s1 s2 →
      (∀ i < 16, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (mp + BitVec.ofNat 64 (4 * i))) →
      LSafeN fns G N Q ⟨⟨2, 22, ret, top⟩ :: rest, regs, m⟩) :
    ∀ k t (regs : Reg → Word) (m : MachineState), 16 - t = k → t < 16 →
      regs .x11 = mp + BitVec.ofNat 64 (4 * t) → regs .x12 = mp + 64#64 →
      regs .x13 = w + BitVec.ofNat 64 (4 * t) → regs .x10 = hp → regs .x1 = ret →
      regs .x2 = top + 18446744073709551296#64 → Kept top m0 m s0 s1 s2 →
      (∀ i < t, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (mp + BitVec.ofNat 64 (4 * i))) →
      LSafeN fns G N Q ⟨⟨2, 12, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ _ hk ht; omega
  | succ k ih =>
    intro t regs m hk ht h11 h12 h13 h10 hra hsp hkept inv
    have hread : m.getWord32 (mp + BitVec.ofNat 64 (4 * t)) =
        m0.getWord32 (mp + BitVec.ofNat 64 (4 * t)) :=
      hkept.1 _ (aligned4_ofNat hmal t) (hmo t ht)
    lsym f2_eq stop [12, 22] with [h11, h12, h13, h10, hra, hsp, hread]
    all_goals
      have hk' := kept_store hL.1 hkept (layout_w hL (t := t) (by omega))
        (aligned4_ofNat (layout_aligned hL).1 t)
    all_goals have hnew := words_store (layout_aligned hL).1 (by omega) inv
    · refine ih (t + 1) _ _ (by omega) (copy_more ht hc) ?_ ?_ ?_ ?_ ?_ ?_ (hk' _) (hnew _ ?_)
      · simp only [lsym_simp]; exact next_addr mp t
      · simp [lsym_simp, h12]
      · simp only [lsym_simp]; exact next_addr w t
      · simp [lsym_simp, h10]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact sext_trunc _
    · obtain rfl := copy_last ht hc
      refine hpost _ _ ?_ ?_ ?_ (hk' _) (hnew _ ?_)
      · simp [lsym_simp, h10]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact sext_trunc _

/-- **Loop 2, the message schedule** (`sha256_schedule`, inlined), at its head with the words
    before `t` written. -/
theorem sched2_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v hp : Word} {m0 : MachineState} {s0 s1 s2 : Word}
    (hL : Layout top w v) (M : Nat → BitVec 32)
    (hpost : ∀ (regs : Reg → Word) m, regs .x10 = hp → regs .x1 = ret →
      regs .x2 = top + 18446744073709551296#64 → Kept top m0 m s0 s1 s2 →
      (∀ i < 64, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W M i) →
      LSafeN fns G N Q ⟨⟨2, 82, ret, top⟩ :: rest, regs, m⟩) :
    ∀ k t (regs : Reg → Word) (m : MachineState), 64 - t = k → 16 ≤ t → t < 64 →
      regs .x11 = w + BitVec.ofNat 64 (4 * t) → regs .x12 = w + 256#64 →
      regs .x10 = hp → regs .x1 = ret → regs .x2 = top + 18446744073709551296#64 →
      Kept top m0 m s0 s1 s2 → (∀ i < t, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W M i) →
      LSafeN fns G N Q ⟨⟨2, 26, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ _ hk _ ht'; omega
  | succ k ih =>
    intro t regs m hk ht ht' h11 h12 h10 hra hsp hkept inv
    lsym f2_eq stop [26, 82] with [h11, h12, h10, hra, hsp]
    all_goals obtain ⟨e2, e7, e15, e16, enext⟩ := sched_addr w ht ht'
    all_goals have hnew := sched_step w M (layout_aligned hL).1 m ht ht' inv
    all_goals have hk' := kept_store hL.1 hkept (layout_w hL ht') (aligned4_ofNat (layout_aligned hL).1 t)
    · refine ih (t + 1) _ _ (by omega) (by omega) (sched_more ht' hc) ?_ ?_ ?_ ?_ ?_ (hk' _)
        (hnew _ ?_)
      · simp only [lsym_simp]; exact enext
      · simp [lsym_simp, h12]
      · simp [lsym_simp, h10]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · simp only [e2, e7, e15, e16, inv (t - 2) (by omega), inv (t - 7) (by omega),
          inv (t - 15) (by omega), inv (t - 16) (by omega), W_step M ht, ssig0, ssig1, rotr]
        bv_decide
    · obtain rfl := sched_last ht' (by simpa using hc)
      refine hpost _ _ ?_ ?_ ?_ (hk' _) (hnew _ ?_)
      · simp [lsym_simp, h10]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · simp only [e2, e7, e15, e16, inv (63 - 2) (by omega), inv (63 - 7) (by omega),
          inv (63 - 15) (by omega), inv (63 - 16) (by omega), W_step M ht, ssig0, ssig1, rotr]
        bv_decide

theorem hcopy_more {t : Nat} (ht : t < 8) (h : ¬BitVec.ofNat 64 (4 * t) + 4#64 = 32#64) :
    t + 1 < 8 := by bv_omega

theorem hcopy_last {t : Nat} (ht : t < 8) (h : BitVec.ofNat 64 (4 * t) + 4#64 = 32#64) :
    t = 7 := by bv_omega

/-- **Loop 3, the hash value copied into the working variables**, at its head with `t` words
    copied. -/
theorem hcopy_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v hp : Word} {m0 : MachineState} {s0 s1 s2 : Word} {M : Nat → BitVec 32}
    (hL : Layout top w v) (hhal : alignedFor 4 hp = true)
    (hho : ∀ i < 8, Out top (hp + BitVec.ofNat 64 (4 * i)))
    (hpost : ∀ (regs : Reg → Word) m, regs .x10 = hp → regs .x11 = hp + 32#64 → regs .x1 = ret →
      regs .x2 = top + 18446744073709551296#64 → Kept top m0 m s0 s1 s2 →
      (∀ i < 64, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W M i) →
      (∀ i < 8, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (hp + BitVec.ofNat 64 (4 * i))) →
      LSafeN fns G N Q ⟨⟨2, 98, ret, top⟩ :: rest, regs, m⟩) :
    ∀ k t (regs : Reg → Word) (m : MachineState), 8 - t = k → t < 8 →
      regs .x13 = hp + BitVec.ofNat 64 (4 * t) → regs .x11 = hp + 32#64 →
      regs .x12 = v + BitVec.ofNat 64 (4 * t) → regs .x10 = hp → regs .x1 = ret →
      regs .x2 = top + 18446744073709551296#64 → Kept top m0 m s0 s1 s2 →
      (∀ i < 64, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W M i) →
      (∀ i < t, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (hp + BitVec.ofNat 64 (4 * i))) →
      LSafeN fns G N Q ⟨⟨2, 88, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ _ hk ht; omega
  | succ k ih =>
    intro t regs m hk ht h13 h11 h12 h10 hra hsp hkept hw inv
    have hread : m.getWord32 (hp + BitVec.ofNat 64 (4 * t)) =
        m0.getWord32 (hp + BitVec.ofNat 64 (4 * t)) :=
      hkept.1 _ (aligned4_ofNat hhal t) (hho t ht)
    lsym f2_eq stop [88, 98] with [h13, h11, h12, h10, hra, hsp, hread]
    all_goals have hk' := kept_store hL.1 hkept (layout_v hL ht) (aligned4_ofNat (layout_aligned hL).2 t)
    all_goals
      have hw' := words_keep (layout_aligned hL).1 (aligned4_ofNat (layout_aligned hL).2 t) hw
        (fun i hi => layout_wv hL hi ht)
    all_goals have hnew := words_store (layout_aligned hL).2 (by omega) inv
    · refine ih (t + 1) _ _ (by omega) (hcopy_more ht hc) ?_ ?_ ?_ ?_ ?_ ?_ (hk' _) (hw' _)
        (hnew _ ?_)
      · simp only [lsym_simp]; exact next_addr hp t
      · simp [lsym_simp, h11]
      · simp only [lsym_simp]; exact next_addr v t
      · simp [lsym_simp, h10]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact sext_trunc _
    · obtain rfl := hcopy_last ht hc
      refine hpost _ _ ?_ ?_ ?_ ?_ (hk' _) (hw' _) (hnew _ ?_)
      · simp [lsym_simp, h10]
      · simp [lsym_simp, h11]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact sext_trunc _

theorem round_more {t : Nat} (ht : t < 64)
    (h : ¬66408#64 + (BitVec.ofNat 64 (4 * t) + 4#64) = 66664#64) : t + 1 < 64 := by bv_omega

theorem round_last {t : Nat} (ht : t < 64)
    (h : 66408#64 + (BitVec.ofNat 64 (4 * t) + 4#64) = 66664#64) : t = 63 := by bv_omega

theorem k_next (t : Nat) :
    66408#64 + (BitVec.ofNat 64 (4 * t) + 4#64) = 66408#64 + BitVec.ofNat 64 (4 * (t + 1)) := by
  bv_omega

/-- The end of a round: the branch back to the loop's head, or out of the loop after the last. -/
theorem round_branch {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w hp : Word} {m : MachineState} {H : Words8} {M : Nat → BitVec 32}
    (hpost : ∀ (regs : Reg → Word), regs8 regs = rounds H M 64 → regs .x10 = hp →
      regs .x11 = hp + 32#64 → regs .x1 = ret → regs .x2 = top + 18446744073709551296#64 →
      LSafeN fns G N Q ⟨⟨2, 218, ret, top⟩ :: rest, regs, m⟩) {t : Nat} (ht : t < 64)
    (next : ∀ (regs : Reg → Word), t + 1 < 64 → regs8 regs = rounds H M (t + 1) →
      regs .x17 = 66408#64 + BitVec.ofNat 64 (4 * (t + 1)) → regs .x6 = 66664#64 →
      regs .x5 = w + BitVec.ofNat 64 (4 * (t + 1)) → regs .x10 = hp → regs .x11 = hp + 32#64 →
      regs .x1 = ret → regs .x2 = top + 18446744073709551296#64 →
      LSafeN fns G N Q ⟨⟨2, 122, ret, top⟩ :: rest, regs, m⟩)
    (regs : Reg → Word) (h8 : regs8 regs = rounds H M (t + 1))
    (h17 : regs .x17 = 66408#64 + (BitVec.ofNat 64 (4 * t) + 4#64)) (h6 : regs .x6 = 66664#64)
    (h5 : regs .x5 = w + (BitVec.ofNat 64 (4 * t) + 4#64)) (h10 : regs .x10 = hp)
    (h11 : regs .x11 = hp + 32#64) (hra : regs .x1 = ret)
    (hsp : regs .x2 = top + 18446744073709551296#64) :
    LSafeN fns G N Q ⟨⟨2, 216, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f2_eq stop [122, 218] with [h17, h6, h5, h10, h11, hra, hsp]
  · refine next _ (round_more ht hc) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h8
    · rw [h17]; exact k_next t
    · exact h6
    · rw [h5]; exact next_addr w t
    · exact h10
    · exact h11
    · exact hra
    · exact hsp
  · obtain rfl := round_last ht hc
    refine hpost _ ?_ ?_ ?_ ?_ ?_
    · exact h8
    · exact h10
    · exact h11
    · exact hra
    · exact hsp

/-! ### One round in registers, piece by piece

The round's two new words are sums of `Σ0`, `Σ1`, `ch`, `maj`, the constant and the word of
the schedule. Each piece is checked on its own by `bv_decide`, which is quick; the sums are then
equal by associativity and commutativity. One `bv_decide` over a whole word takes seconds of
SAT solving, on the edge of its default timeout. -/

/-- `Σ1` as the binary computes it, on a register holding the word in its low half. -/
theorem bsig1_regs (x : Word) :
    BitVec.setWidth 32
      ((x <<< 26 ||| BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) >>> 6))) ^^^
        (x <<< 21 ||| BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) >>> 11))) ^^^
        (x <<< 7 ||| BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) >>> 25)))) =
      (BitVec.setWidth 32 x).rotateRight 6 ^^^ (BitVec.setWidth 32 x).rotateRight 11 ^^^
        (BitVec.setWidth 32 x).rotateRight 25 := by
  bv_decide

/-- `Σ0` as the binary computes it. -/
theorem bsig0_regs (x : Word) :
    BitVec.setWidth 32
      ((x <<< 30 ||| BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) >>> 2))) ^^^
        (x <<< 19 ||| BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) >>> 13))) ^^^
        (x <<< 10 ||| BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 x) >>> 22)))) =
      (BitVec.setWidth 32 x).rotateRight 2 ^^^ (BitVec.setWidth 32 x).rotateRight 13 ^^^
        (BitVec.setWidth 32 x).rotateRight 22 := by
  bv_decide

/-- `ch` as the binary computes it: `((f ^ g) & e) ^ g`. -/
theorem ch_regs (e f g : Word) :
    BitVec.setWidth 32 ((f ^^^ g) &&& e ^^^ g) =
      (BitVec.setWidth 32 e &&& BitVec.setWidth 32 f ^^^ ~~~BitVec.setWidth 32 e &&& BitVec.setWidth 32 g) := by
  bv_decide

/-- `maj` as the binary computes it: `((c ^ b) & a) ^ (c & b)`. -/
theorem maj_regs (a b c : Word) :
    BitVec.setWidth 32 ((c ^^^ b) &&& a ^^^ c &&& b) =
      (BitVec.setWidth 32 a &&& BitVec.setWidth 32 b ^^^ BitVec.setWidth 32 a &&& BitVec.setWidth 32 c ^^^
        BitVec.setWidth 32 b &&& BitVec.setWidth 32 c) := by
  bv_decide

/-- **Loop 4, the sixty-four rounds**, at its head after `t` of them: the working variables are
    in registers, and memory is read, not written. -/
theorem round_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w hp : Word} {m : MachineState} {H : Words8} {M : Nat → BitVec 32}
    (hK : ∀ i < 64, m.getWord32 (66408#64 + BitVec.ofNat 64 (4 * i)) = K.getD i 0)
    (hW : ∀ i < 64, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W M i)
    (hpost : ∀ (regs : Reg → Word), regs8 regs = rounds H M 64 → regs .x10 = hp →
      regs .x11 = hp + 32#64 → regs .x1 = ret → regs .x2 = top + 18446744073709551296#64 →
      LSafeN fns G N Q ⟨⟨2, 218, ret, top⟩ :: rest, regs, m⟩) :
    ∀ k t (regs : Reg → Word), 64 - t = k → t < 64 →
      regs8 regs = rounds H M t → regs .x17 = 66408#64 + BitVec.ofNat 64 (4 * t) →
      regs .x6 = 66664#64 → regs .x5 = w + BitVec.ofNat 64 (4 * t) → regs .x10 = hp →
      regs .x11 = hp + 32#64 → regs .x1 = ret → regs .x2 = top + 18446744073709551296#64 →
      LSafeN fns G N Q ⟨⟨2, 122, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ hk ht; omega
  | succ k ih =>
    intro t regs hk ht inv h17 h6 h5 h10 h11 hra hsp
    have hkt := hK t ht
    have hwt := hW t ht
    generalize hkd : K.getD t 0 = kt at hkt
    generalize hwd : W M t = wt at hwt
    lsym f2_eq stop [216] with [h17, h6, h5, h10, h11, hra, hsp, hkt, hwt]
    refine round_branch hpost ht (fun r hlt h8 => ih (t + 1) r (by omega) hlt h8) _ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_
    · rw [rounds, ← inv, hkd, hwd]
      simp only [regs8, lsym_simp, round, bsig0, bsig1, ch, maj, rotr, Prod.mk.injEq]
      repeat' apply And.intro
      all_goals
        simp only [BitVec.setWidth_add _ _ (show 32 ≤ 64 by decide), sext_trunc,
          bsig0_regs, bsig1_regs, ch_regs, maj_regs]
      all_goals ac_rfl
    · simp [lsym_simp]
    · simp [lsym_simp, h6]
    · simp [lsym_simp]
    · simp [lsym_simp, h10]
    · simp [lsym_simp, h11]
    · simp [lsym_simp, hra]
    · simp [lsym_simp, hsp]

/-- The words of `h` after the `t`-th has been added to. -/
theorem add_step {hp : Word} (hal : alignedFor 4 hp = true) {m : MachineState}
    {Hf Vf : Nat → BitVec 32} {t : Nat} (ht : t < 8)
    (inv : ∀ i < 8, m.getWord32 (hp + BitVec.ofNat 64 (4 * i)) = if i < t then Hf i + Vf i else Hf i)
    (x : BitVec 32) (hx : x = Hf t + Vf t) :
    ∀ i < 8, (m.setWord32 (hp + BitVec.ofNat 64 (4 * t)) x).getWord32
      (hp + BitVec.ofNat 64 (4 * i)) = if i < t + 1 then Hf i + Vf i else Hf i := by
  intro i hi
  rw [getWord32_setWord32 _ _ _ _ (aligned4_ofNat hal t) (aligned4_ofNat hal i)]
  by_cases h : i = t
  · subst h; simp [hx]
  · have hne : hp + BitVec.ofNat 64 (4 * i) ≠ hp + BitVec.ofNat 64 (4 * t) := by bv_omega
    rw [ite_eq_right hne, inv i hi]
    by_cases h' : i < t
    · rw [ite_eq_left h', ite_eq_left (by omega)]
    · rw [ite_eq_right h', ite_eq_right (by omega)]

/-- **Loop 5, the working variables added into the hash value**, at its head with `t` words
    added; it ends in the epilogue, which restores `s0`, `s1`, `s2` and returns. -/
theorem add_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v hp : Word} {s0 s1 s2 : Word} {Hf Vf : Nat → BitVec 32}
    (hL : Layout top w v) (hhal : alignedFor 4 hp = true)
    (hho : ∀ i < 8, Out top (hp + BitVec.ofNat 64 (4 * i)))
    (hpost : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x2 = top → (∀ i < 8, m'.getWord32 (hp + BitVec.ofNat 64 (4 * i)) = Hf i + Vf i) →
      LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k t (regs : Reg → Word) (m : MachineState), 8 - t = k → t < 8 →
      regs .x10 = hp + BitVec.ofNat 64 (4 * t) → regs .x11 = hp + 32#64 →
      regs .x12 = v + BitVec.ofNat 64 (4 * t) → regs .x1 = ret →
      regs .x2 = top + 18446744073709551296#64 →
      m.getMem (top + 18446744073709551608#64) = s0 → m.getMem (top + 18446744073709551600#64) = s1 →
      m.getMem (top + 18446744073709551592#64) = s2 →
      (∀ i < 8, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) = Vf i) →
      (∀ i < 8, m.getWord32 (hp + BitVec.ofNat 64 (4 * i)) = if i < t then Hf i + Vf i else Hf i) →
      LSafeN fns G N Q ⟨⟨2, 236, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro t _ _ hk ht; omega
  | succ k ih =>
    intro t regs m hk ht h10 h11 h12 hra hsp hs0 hs1 hs2 hv hh
    have hvt := hv t ht
    have hht : m.getWord32 (hp + BitVec.ofNat 64 (4 * t)) = Hf t := by
      rw [hh t ht, ite_eq_right (by omega)]
    obtain ⟨d0, d1, d2⟩ := dword_out hL.1 (hho t ht)
    lsym f2_eq stop [236] with [h10, h11, h12, hra, hsp, hvt, hht]
    all_goals
      have hv' := words_keep (layout_aligned hL).2 (aligned4_ofNat hhal t) hv
        (fun i hi => out_ne (hho t ht) (layout_v hL hi))
    all_goals have hnew := add_step hhal ht hh
    all_goals
      have hsum : BitVec.setWidth 32 (BitVec.signExtend 64 (Hf t) + BitVec.signExtend 64 (Vf t)) =
          Hf t + Vf t := by bv_decide
    · refine ih (t + 1) _ _ (by omega) (hcopy_more ht hc) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hv' _)
        (hnew _ hsum)
      · simp only [lsym_simp]; exact next_addr hp t
      · simp [lsym_simp, h11]
      · simp only [lsym_simp]; exact next_addr v t
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · rw [getMem_setWord32 _ _ _ _ d0, hs0]
      · rw [getMem_setWord32 _ _ _ _ d1, hs1]
      · rw [getMem_setWord32 _ _ _ _ d2, hs2]
    · obtain rfl := hcopy_last ht hc
      refine hpost _ _ ?_ ?_ ?_ ?_ fun i hi => ?_
      · simp [lsym_simp, getMem_setWord32 _ _ _ _ d0, hs0]
      · simp [lsym_simp, getMem_setWord32 _ _ _ _ d1, hs1]
      · simp [lsym_simp, getMem_setWord32 _ _ _ _ d2, hs2]
      · simp [lsym_simp]
      · rw [hnew _ hsum i hi, ite_eq_left (by omega)]

/-- **The eight working variables stored back** into `v` after the rounds: they read back, and
    what `Kept` asks is kept. -/
theorem v_stores {top : Word} (ht : top &&& 7#64 = 0#64) {m0 m : MachineState} {s0 s1 s2 : Word}
    (hk : Kept top m0 m s0 s1 s2) (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 32) :
    let m' := (((((((m.setWord32 (top + 18446744073709551304#64) x0).setWord32
      (top + 18446744073709551308#64) x1).setWord32 (top + 18446744073709551312#64) x2).setWord32
      (top + 18446744073709551316#64) x3).setWord32 (top + 18446744073709551320#64) x4).setWord32
      (top + 18446744073709551324#64) x5).setWord32 (top + 18446744073709551328#64) x6).setWord32
      (top + 18446744073709551332#64) x7
    Kept top m0 m' s0 s1 s2 ∧ ∀ i < 8, m'.getWord32 (top + 18446744073709551304#64 +
      BitVec.ofNat 64 (4 * i)) = get8 (x0, x1, x2, x3, x4, x5, x6, x7) i := by
  have a0 := frame_aligned ht 18446744073709551304#64 (by decide)
  have a1 := frame_aligned ht 18446744073709551308#64 (by decide)
  have a2 := frame_aligned ht 18446744073709551312#64 (by decide)
  have a3 := frame_aligned ht 18446744073709551316#64 (by decide)
  have a4 := frame_aligned ht 18446744073709551320#64 (by decide)
  have a5 := frame_aligned ht 18446744073709551324#64 (by decide)
  have a6 := frame_aligned ht 18446744073709551328#64 (by decide)
  have a7 := frame_aligned ht 18446744073709551332#64 (by decide)
  have f : ∀ c : Word, 8#64 ≤ c + 320#64 → c + 320#64 < 296#64 → InFrame top (top + c) :=
    fun c h1 h2 => by unfold InFrame; bv_omega
  refine ⟨?_, fun i hi => ?_⟩
  · refine kept_store ht (kept_store ht (kept_store ht (kept_store ht (kept_store ht (kept_store ht
      (kept_store ht (kept_store ht hk (f _ (by decide) (by decide)) a0 _) (f _ (by decide)
      (by decide)) a1 _) (f _ (by decide) (by decide)) a2 _) (f _ (by decide) (by decide)) a3 _)
      (f _ (by decide) (by decide)) a4 _) (f _ (by decide) (by decide)) a5 _)
      (f _ (by decide) (by decide)) a6 _) (f _ (by decide) (by decide)) a7 _
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals try omega
    all_goals simp [BitVec.add_assoc, getWord32_setWord32, a0, a1, a2, a3, a4, a5, a6, a7, get8]

/-- The eight words at `h` from what loop 5 leaves: the compression function. -/
theorem words8_compress {m m' : MachineState} {hp : Word} {M : Nat → BitVec 32}
    (h : ∀ i < 8, m'.getWord32 (hp + BitVec.ofNat 64 (4 * i)) =
      m.getWord32 (hp + BitVec.ofNat 64 (4 * i)) + get8 (rounds (words8 m hp) M 64) i) :
    words8 m' hp = compress (words8 m hp) M := by
  have e0 := h 0 (by decide); have e1 := h 1 (by decide); have e2 := h 2 (by decide)
  have e3 := h 3 (by decide); have e4 := h 4 (by decide); have e5 := h 5 (by decide)
  have e6 := h 6 (by decide); have e7 := h 7 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.add_zero]
    at e0 e1 e2 e3 e4 e5 e6 e7
  unfold compress
  generalize rounds (words8 m hp) M 64 = s at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  obtain ⟨a, b, c, d, e, f, g, k⟩ := s
  simp only [get8] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [words8, e0, e1, e2, e3, e4, e5, e6, e7]

/-- After loop 4 [218]: the working variables stored back, then loop 5 and the return. -/
theorem after_rounds {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v hp s0 s1 s2 : Word} {m0 : MachineState} {H : Words8}
    {M : Nat → BitVec 32} (hL : Layout top w v) (hhal : alignedFor 4 hp = true)
    (hho : ∀ i < 8, Out top (hp + BitVec.ofNat 64 (4 * i)))
    (hfin : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x2 = top → (∀ i < 8, m'.getWord32 (hp + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (hp + BitVec.ofNat 64 (4 * i)) + get8 (rounds H M 64) i) →
      LSafeN fns G N Q ⟨rest, r', m'⟩)
    (regs : Reg → Word) (m : MachineState) (h8 : regs8 regs = rounds H M 64)
    (h10 : regs .x10 = hp) (h11 : regs .x11 = hp + 32#64) (hra : regs .x1 = ret)
    (hsp : regs .x2 = top + 18446744073709551296#64) (hk : Kept top m0 m s0 s1 s2) :
    LSafeN fns G N Q ⟨⟨2, 218, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f2_eq stop [236] with [h10, h11, hra, hsp]
  obtain ⟨hk', hv⟩ := v_stores hL.1 hk ((regs .x7).setWidth 32) ((regs .x12).setWidth 32)
    ((regs .x13).setWidth 32) ((regs .x28).setWidth 32) ((regs .x29).setWidth 32)
    ((regs .x14).setWidth 32) ((regs .x15).setWidth 32) ((regs .x16).setWidth 32)
  have hL' := hL
  obtain ⟨-, rfl, rfl⟩ := hL'
  refine add_loop (Hf := fun i => m0.getWord32 (hp + BitVec.ofNat 64 (4 * i)))
    (Vf := fun i => get8 (rounds H M 64) i) hL hhal hho hfin 8 0 _ _ rfl (by decide) ?_ ?_ ?_ ?_ ?_
    hk'.2.1 hk'.2.2.1 hk'.2.2.2 (fun i hi => ?_) (fun i hi => ?_)
  · simp [lsym_simp, h10]
  · simp [lsym_simp, h11]
  · simp [lsym_simp]
  · simp [lsym_simp, hra]
  · simp [lsym_simp, hsp]
  · rw [hv i hi, ← h8]; rfl
  · rw [hk'.1 _ (aligned4_ofNat hhal i) (hho i hi), ite_eq_right (Nat.not_lt_zero i)]

/-- The words at `v` read at the addresses `lsym` writes. -/
theorem v_reads {top w v : Word} (hL : Layout top w v) {m : MachineState} {f : Nat → BitVec 32}
    (h : ∀ i < 8, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) = f i) :
    m.getWord32 (top + 18446744073709551304#64) = f 0 ∧
      m.getWord32 (top + 18446744073709551308#64) = f 1 ∧
      m.getWord32 (top + 18446744073709551312#64) = f 2 ∧
      m.getWord32 (top + 18446744073709551316#64) = f 3 ∧
      m.getWord32 (top + 18446744073709551320#64) = f 4 ∧
      m.getWord32 (top + 18446744073709551324#64) = f 5 ∧
      m.getWord32 (top + 18446744073709551328#64) = f 6 ∧
      m.getWord32 (top + 18446744073709551332#64) = f 7 := by
  obtain ⟨-, -, rfl⟩ := hL
  have e := fun i hi => h i hi
  simp only [BitVec.add_assoc] at e
  exact ⟨e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)⟩

/-- Between loops 3 and 4 [98]: the working variables loaded into registers, then the rounds. -/
theorem after_hcopy {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v hp s0 s1 s2 : Word} {m0 : MachineState} {M : Nat → BitVec 32}
    (hL : Layout top w v) (hhal : alignedFor 4 hp = true)
    (hho : ∀ i < 8, Out top (hp + BitVec.ofNat 64 (4 * i))) (htab : TableAt m0)
    (hko : ∀ i < 64, Out top (0x10368#64 + BitVec.ofNat 64 (4 * i)))
    (hfin : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x2 = top → (∀ i < 8, m'.getWord32 (hp + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (hp + BitVec.ofNat 64 (4 * i)) + get8 (rounds (words8 m0 hp) M 64) i) →
      LSafeN fns G N Q ⟨rest, r', m'⟩)
    (regs : Reg → Word) (m : MachineState) (h10 : regs .x10 = hp) (h11 : regs .x11 = hp + 32#64)
    (hra : regs .x1 = ret) (hsp : regs .x2 = top + 18446744073709551296#64)
    (hk : Kept top m0 m s0 s1 s2) (hw : ∀ i < 64, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W M i)
    (hv : ∀ i < 8, m.getWord32 (v + BitVec.ofNat 64 (4 * i)) =
      m0.getWord32 (hp + BitVec.ofNat 64 (4 * i))) :
    LSafeN fns G N Q ⟨⟨2, 98, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f2_eq stop [122] with [h10, h11, hra, hsp]
  have hK : ∀ i < 64, m.getWord32 (66408#64 + BitVec.ofNat 64 (4 * i)) = K.getD i 0 :=
    fun i hi => by rw [hk.1 _ (aligned4_ofNat (by decide) i) (hko i hi)]; exact htab i hi
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := v_reads hL hv
  have hL' := hL
  obtain ⟨-, rfl, rfl⟩ := hL'
  refine round_loop (H := words8 m0 hp) hK hw
    (fun r h8 h10' h11' hra' hsp' => after_rounds hL hhal hho hfin r m h8 h10' h11' hra' hsp' hk) 64 0 _
    rfl (by decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7
    simp only [regs8, lsym_simp, sext_trunc, e0, e1, e2, e3, e4, e5, e6, e7, rounds, words8]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, h10]
  · simp [lsym_simp, h11]
  · simp [lsym_simp, hra]
  · simp [lsym_simp, hsp]

/-- Between loops 2 and 3 [82]: the pointers of loop 3 set up. -/
theorem after_sched {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v hp s0 s1 s2 : Word} {m0 : MachineState} {M : Nat → BitVec 32}
    (hL : Layout top w v) (hhal : alignedFor 4 hp = true)
    (hho : ∀ i < 8, Out top (hp + BitVec.ofNat 64 (4 * i))) (htab : TableAt m0)
    (hko : ∀ i < 64, Out top (0x10368#64 + BitVec.ofNat 64 (4 * i)))
    (hfin : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x2 = top → (∀ i < 8, m'.getWord32 (hp + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (hp + BitVec.ofNat 64 (4 * i)) + get8 (rounds (words8 m0 hp) M 64) i) →
      LSafeN fns G N Q ⟨rest, r', m'⟩)
    (regs : Reg → Word) (m : MachineState) (h10 : regs .x10 = hp) (hra : regs .x1 = ret)
    (hsp : regs .x2 = top + 18446744073709551296#64) (hk : Kept top m0 m s0 s1 s2)
    (hw : ∀ i < 64, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) = W M i) :
    LSafeN fns G N Q ⟨⟨2, 82, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f2_eq stop [88] with [h10, hra, hsp]
  have hL' := hL
  obtain ⟨-, -, rfl⟩ := hL'
  refine hcopy_loop hL hhal hho
    (fun r m' h10' h11' hra' hsp' hk' hw' hv' =>
      after_hcopy hL hhal hho htab hko hfin r m' h10' h11' hra' hsp' hk' hw' hv')
    8 0 _ _ rfl (by decide) ?_ ?_ ?_ ?_ ?_ ?_ hk hw (fun i hi => absurd hi (Nat.not_lt_zero i))
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, h10]
  · simp [lsym_simp, hra]
  · simp [lsym_simp, hsp]

/-- Between loops 1 and 2 [22]: the pointers of loop 2 set up. -/
theorem after_copy {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {w v hp mp s0 s1 s2 : Word} {m0 : MachineState}
    (hL : Layout top w v) (hhal : alignedFor 4 hp = true)
    (hho : ∀ i < 8, Out top (hp + BitVec.ofNat 64 (4 * i))) (htab : TableAt m0)
    (hko : ∀ i < 64, Out top (0x10368#64 + BitVec.ofNat 64 (4 * i)))
    (hfin : ∀ (r' : Reg → Word) (m' : MachineState), r' .x8 = s0 → r' .x9 = s1 → r' .x18 = s2 →
      r' .x2 = top → (∀ i < 8, m'.getWord32 (hp + BitVec.ofNat 64 (4 * i)) =
        m0.getWord32 (hp + BitVec.ofNat 64 (4 * i)) +
          get8 (rounds (words8 m0 hp) (fun j => m0.getWord32 (mp + BitVec.ofNat 64 (4 * j))) 64) i) →
      LSafeN fns G N Q ⟨rest, r', m'⟩)
    (regs : Reg → Word) (m : MachineState) (h10 : regs .x10 = hp) (hra : regs .x1 = ret)
    (hsp : regs .x2 = top + 18446744073709551296#64) (hk : Kept top m0 m s0 s1 s2)
    (hw : ∀ i < 16, m.getWord32 (w + BitVec.ofNat 64 (4 * i)) =
      m0.getWord32 (mp + BitVec.ofNat 64 (4 * i))) :
    LSafeN fns G N Q ⟨⟨2, 22, ret, top⟩ :: rest, regs, m⟩ := by
  lsym f2_eq stop [26] with [h10, hra, hsp]
  have hL' := hL
  obtain ⟨-, rfl, -⟩ := hL'
  refine sched2_loop hL (fun j => m0.getWord32 (mp + BitVec.ofNat 64 (4 * j)))
    (fun r m' h10' hra' hsp' hk' hw' => after_sched hL hhal hho htab hko hfin r m' h10' hra' hsp' hk' hw')
    48 16 _ _ rfl (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ hk
    (fun i hi => (hw i hi).trans
      (W_init (fun j => m0.getWord32 (mp + BitVec.ofNat 64 (4 * j))) hi).symm)
  · simp [lsym_simp, BitVec.add_assoc]
  · simp [lsym_simp, BitVec.add_assoc]
  · simp [lsym_simp, h10]
  · simp [lsym_simp, hra]
  · simp [lsym_simp, hsp]

/-- `sha256_compress(h, m)`: the eight words at `h` become the compression function of FIPS
    180-4 (`compress`) of the hash value they held and the block of sixteen words at `m`;
    `s0`, `s1`, `s2` and the stack pointer are as they were.

    Assumed: the stack pointer `top` is aligned to a doubleword, `h` and `m` to a word; memory
    holds `K` where the binary reads it (`TableAt`); and the words at `h` and `m` and the table
    are outside the 320 bytes below `top` that the function's frame takes (`Out`). `h` and `m`
    may overlap. No access is assumed valid: an access that is not traps, and a trap is safe. -/
theorem sha256_compress_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧ alignedFor 8 top = true ∧
      alignedFor 4 (regs .x10) = true ∧ alignedFor 4 (regs .x11) = true ∧ TableAt m ∧
      (∀ i < 8, Out top (regs .x10 + BitVec.ofNat 64 (4 * i))) ∧
      (∀ i < 16, Out top (regs .x11 + BitVec.ofNat 64 (4 * i))) ∧
      (∀ i < 64, Out top (0x10368#64 + BitVec.ofNat 64 (4 * i))))
    (fun _ top regs m r' m' =>
      words8 m' (regs .x10) = compress (words8 m (regs .x10))
        (fun j => m.getWord32 (regs .x11 + BitVec.ofNat 64 (4 * j))) ∧
      r' .x8 = regs .x8 ∧ r' .x9 = regs .x9 ∧ r' .x18 = regs .x18 ∧ r' .x2 = top) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, ht8, hhal, hmal, htab, hho, hmo, hko⟩ hk
  have hL : Layout top (top + 18446744073709551336#64) (top + 18446744073709551304#64) :=
    ⟨(aligned8_iff top).1 ht8, rfl, rfl⟩
  lsym f2_eq stop [12] with [hra, hsp]
  refine copy_loop hL hmal hmo
    (fun r m' h10 hra' hsp' hk' hw => after_copy hL hhal hho htab hko
      (fun r' m'' h8 h9 h18 h2 hwords => hk r' m'' ⟨words8_compress hwords, h8, h9, h18, h2⟩)
      r m' h10 hra' hsp' hk' hw)
    16 0 _ _ rfl (by decide) ?_ ?_ ?_ ?_ ?_ ?_ (kept_init hL.1 m _ _ _)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp]
  · simp [lsym_simp, hra]
  · simp [lsym_simp]

/-- **`sha256_compress` on the machine.** -/
theorem sha256_compress_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10160#64) (hcode : Loaded fns s) (ht : alignedFor 8 (s.getReg .x2) = true)
    (hhal : alignedFor 4 (s.getReg .x10) = true) (hmal : alignedFor 4 (s.getReg .x11) = true)
    (htab : TableAt s)
    (hho : ∀ i < 8, Out (s.getReg .x2) (s.getReg .x10 + BitVec.ofNat 64 (4 * i)))
    (hmo : ∀ i < 16, Out (s.getReg .x2) (s.getReg .x11 + BitVec.ofNat 64 (4 * i)))
    (hko : ∀ i < 64, Out (s.getReg .x2) (0x10368#64 + BitVec.ofNat 64 (4 * i)))
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      words8 t (s.getReg .x10) = compress (words8 s (s.getReg .x10))
        (fun j => s.getWord32 (s.getReg .x11 + BitVec.ofNat 64 (4 * j))) →
      t.getReg .x8 = s.getReg .x8 → t.getReg .x9 = s.getReg .x9 →
      t.getReg .x18 = s.getReg .x18 → t.getReg .x2 = s.getReg .x2 → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x10160#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode sha256_compress_contract
    ⟨rfl, rfl, ht, hhal, hmal, htab, hho, hmo, hko⟩ ?_
  rintro t r' m' hag hpc' ⟨hwords, h8, h9, h18, h2⟩
  refine hk t hpc' ?_ ?_ ?_ ?_ ?_
  · simpa only [words8, getWord32_of_agree hag, regsOf] using hwords
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h8
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h9
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h18
  · rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h2

end Examples.Sha256.RiscV
