/-
  Examples.Sha256

  `sha256_round` of `src/c/sha256.c`, compiled by clang: one round of SHA-256 on the eight
  working variables in memory. Its contract at Lprog, proved with `lsym`, and the same statement
  over riscv-zkvm's machine (`sha256_round_correct`).

  The function is 57 instructions with no branch. It keeps `s0` in a frame of its own, so the
  precondition asks that the doubleword it saves `s0` in is none of those the eight words are
  in. The specification is the round of FIPS 180-4 (`round`), with `rotateRight`; `bv_decide`
  relates it to the shifts the binary has.

  `sha256_schedule` and `sha256_compress` are lifted (`Gen/Sha256/F1.lean`, `F2.lean`) and not
  proved.
-/

import Examples.Gen.Sha256
import Examples.ChaCha20

namespace Examples.Sha256

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Gen.Sha256 Examples.ChaCha20

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-- A word read after a doubleword written in another doubleword. -/
theorem getWord32_setMem (m : MachineState) (c w a : Word) (h : alignToDword a ≠ c) :
    (m.setMem c w).getWord32 a = m.getWord32 a := by
  simp only [MachineState.getWord32, MachineState.getMem_setMem_ne h]

/-- A doubleword read after a word written in another doubleword. -/
theorem getMem_setWord32 (m : MachineState) (a c : Word) (v : BitVec 32) (h : c ≠ alignToDword a) :
    (m.setWord32 a v).getMem c = m.getMem c := by
  simp only [MachineState.setWord32, MachineState.getMem_setMem_ne h]

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

def rotr (x : BitVec 32) (n : Nat) : BitVec 32 := x.rotateRight n
def ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : BitVec 32) : BitVec 32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : BitVec 32) : BitVec 32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- One round of SHA-256 (FIPS 180-4, 6.2.2 step 3) on the working variables `a`..`h`, with the
    round's constant `k` and word `w`. -/
def round (a b c d e f g h k w : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let t1 := h + bsig1 e + ch e f g + k + w
  let t2 := bsig0 a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

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
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).1]; bv_decide
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.1]; bv_decide
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.1]; bv_decide
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.1]; bv_decide
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.1]; bv_decide
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.2.1]; bv_decide
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.2.2.1]; bv_decide
    · rw [(eight_words _ _ _ _ _ _ _ _ _ _ hal).2.2.2.2.2.2.2]; bv_decide
  · simp only [lsym_simp]
    rw [getMem_setWord32 _ _ _ _ d3.symm, getMem_setWord32 _ _ _ _ d2.symm,
      getMem_setWord32 _ _ _ _ d1.symm, getMem_setWord32 _ _ _ _ d0.symm,
      getMem_setWord32 _ _ _ _ d7.symm, getMem_setWord32 _ _ _ _ d6.symm,
      getMem_setWord32 _ _ _ _ d5.symm, getMem_setWord32 _ _ _ _ d4.symm,
      MachineState.getMem_setMem_eq]
  · simp [lsym_simp]

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

end Examples.Sha256
