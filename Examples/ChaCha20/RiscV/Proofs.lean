/-
  Examples.ChaCha20.RiscV.Proofs

  `quarter_round(s)` of `src/c/chacha20.c`, compiled by clang: ChaCha20's quarter round on the
  four 32-bit words at `s`. Its contract at Lprog, proved with `lsym`, and the same statement
  over riscv-zkvm's machine (`quarter_round_correct`).

  The specification is `qr` (`Examples/Spec.lean`), the quarter round on four `BitVec 32` with
  `BitVec.rotateLeft`. The code computes in 64-bit registers (`lw` sign-extends, a rotation is
  `slli`, `srliw` and `or`) and stores the low 32 bits; that these are `qr`'s words is
  `bv_decide`'s work. Memory is doublewords, so a 32-bit word is half of one: the lemmas of
  `Examples/Kit.lean` read a word and a byte after a word was written. No byte outside the
  sixteen at `s` changes.

  `chacha20_block` is not proved here.
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

end Examples.ChaCha20.RiscV
