/-
  Examples.Bytes.RiscV.Proofs

  `src/c/bytes.c`, compiled by clang (`elf/bytes.elf`): three loops over bytes and bits, each
  with its contract at Lprog, proved with `lsym`, and the same statement over riscv-zkvm's
  machine, through `SafeN.of_isa_contract`.

  * `str_len(s)`: the length of the string at `s`, for a string of any length (`StrAt`). The
    loop reads a byte and counts it before it tests it, so the result is the count less one.
  * `fill(p, n, v)`: the `n` bytes from `p` are `v`'s low byte, every other byte and the code
    are kept. A walk of `p` to an end pointer; that the addresses can be written is asked of
    each byte, and nothing else is: the walk meets its end after `n` steps whether or not
    `p + n` wraps.
  * `count_ones(x)`: the number of one bits of `x` (`ones`), by a loop that takes the lowest bit
    and shifts until nothing is left; the induction is on a bound of `x`.

  Each loop is a lemma at its head, on the register file, by induction on what is left.
-/

import Examples.Bytes.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Bytes.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Bytes.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-! ## `str_len` -/

/-- **The loop of `str_len`**, at its head with `j ≤ n` bytes counted. -/
theorem str_len_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (s : Word) (n : Nat) (hstr : StrAt m s n)
    (hv : ∀ i ≤ n, isValidMemAddrSp1 (s + BitVec.ofNat 64 i) = true)
    (hpost : ∀ r', r' .x10 = BitVec.ofNat 64 n →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m⟩) :
    ∀ k j (regs : Reg → BitVec 64), n - j = k → j ≤ n →
      regs .x10 = s → regs .x11 = BitVec.ofNat 64 j → regs .x1 = ret → regs .x2 = top →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨0, 2, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro j regs hk hj h10 h11 hra hsp
    obtain rfl : j = n := by omega
    lsym f0_eq stop [2] with [h10, h11, hra, hsp, hv j hj]
    · exact absurd ((zext_byte_eq_zero _).mpr hstr.2.2) hc
    · apply hpost; simp [lsym_simp]
  | succ k ih =>
    intro j regs hk hj h10 h11 hra hsp
    lsym f0_eq stop [2] with [h10, h11, hra, hsp, hv j hj]
    · -- the byte is not zero: the back edge
      apply ih (j + 1) _ (by omega) (by omega)
      all_goals simp [lsym_simp, ofNat_succ, h10, hra, hsp]
    · -- the byte is zero, before the string's end
      exact absurd ((zext_byte_eq_zero _).mp hc) (hstr.2.1 j (by omega))

/-- `str_len(s)`: the length of the string at `s`, the memory kept. -/
theorem str_len_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧
      ∃ n, StrAt m (regs .x10) n ∧ ∀ i ≤ n, isValidMemAddrSp1 (regs .x10 + BitVec.ofNat 64 i) = true)
    (fun _ _ regs m r' m' =>
      (∀ n, StrAt m (regs .x10) n → r' .x10 = BitVec.ofNat 64 n) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, n, hstr, hv⟩ hk
  lsym f0_eq stop [2] with [hra, hsp]
  refine str_len_loop m (regs .x10) n hstr hv
    (fun r' h => hk r' m ⟨fun n' h' => by rw [h, hstr.unique h'], rfl⟩) n 0 _ (by omega)
    (by omega) ?_ ?_ ?_ ?_
  all_goals simp [lsym_simp, hra, hsp]

/-- **`str_len` on the machine.** -/
theorem str_len_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s) (n : Nat)
    (hstr : StrAt s (s.getReg .x10) n)
    (hv : ∀ i ≤ n, isValidMemAddrSp1 (s.getReg .x10 + BitVec.ofNat 64 i) = true)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 → t.getReg .x10 = BitVec.ofNat 64 n →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode str_len_contract ⟨rfl, rfl, n, hstr, hv⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10 n hstr

/-! ## `fill` -/

/-- **The loop of `fill`**, at its head with `k` bytes left from `p`. -/
theorem fill_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (v : Word) :
    ∀ k (regs : Reg → BitVec 64) (m : MachineState) (p : Word), k + 1 < 2 ^ 64 →
      regs .x10 = p → regs .x11 = p + BitVec.ofNat 64 (k + 1) → regs .x12 = v →
      regs .x1 = ret → regs .x2 = top →
      (∀ i < k + 1, isValidMemAddrSp1 (p + BitVec.ofNat 64 i) = true ∧
        noCodeAt m (p + BitVec.ofNat 64 i) 1 = true) →
      (∀ r' m', (∀ i < k + 1, m'.getByte (p + BitVec.ofNat 64 i) = v.setWidth 8) →
        (∀ a, (∀ i < k + 1, a ≠ p + BitVec.ofNat 64 i) → m'.getByte a = m.getByte a) →
        m'.code = m.code → rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m'⟩) →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨1, 4, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro regs m p hk h10 h11 h12 hra hsp hv hpost
    have hv0 := hv 0 (by omega)
    rw [show p + BitVec.ofNat 64 0 = p by simp] at hv0
    lsym f1_eq stop [4] with [h10, h11, h12, hra, hsp, hv0.1, hv0.2]
    apply hpost
    · intro i hi; obtain rfl : i = 0 := by omega
      simp [getByte_setByte]
    · intro a ha
      have := ha 0 (by omega)
      simp at this
      simp [getByte_setByte, this]
    · rfl
  | succ k ih =>
    intro regs m p hk h10 h11 h12 hra hsp hv hpost
    have hv0 := hv 0 (by omega)
    rw [show p + BitVec.ofNat 64 0 = p by simp] at hv0
    lsym f1_eq stop [4] with [h10, h11, h12, hra, hsp, hv0.1, hv0.2]
    · -- more bytes: the back edge
      refine ih _ _ (p + 1#64) (by omega) (by simp [lsym_simp]) ?_ (by simp [lsym_simp, h12])
        (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp]) ?_ ?_
      · simp [lsym_simp, h11, add_one_add]
      · intro i hi
        rw [add_one_add]
        exact hv (i + 1) (by omega)
      · intro r' m' hb hf hcd
        apply hpost
        · intro i hi
          rcases i with _ | i
          · have := hf p (fun i hi => by rw [add_one_add]; exact ne_add_succ p (by omega))
            simpa [getByte_setByte] using this
          · rw [← add_one_add]; exact hb i (by omega)
        · intro a ha
          have h0 := ha 0 (by omega)
          simp only [BitVec.add_zero] at h0
          rw [hf a (fun i hi => by rw [add_one_add]; exact ha (i + 1) (by omega))]
          simp [getByte_setByte, h0]
        · exact hcd
    · -- the end pointer one byte on: `k + 1 = 0`
      exact absurd (end_next hk hc) (by omega)

/-- `fill(p, n, v)`: the `n` bytes from `p` are `v`'s low byte; every other byte and the code
    are kept. -/
theorem fill_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧
      ∀ i < (regs .x11).toNat, isValidMemAddrSp1 (regs .x10 + BitVec.ofNat 64 i) = true ∧
        noCodeAt m (regs .x10 + BitVec.ofNat 64 i) 1 = true)
    (fun _ _ regs m _ m' =>
      (∀ i < (regs .x11).toNat, m'.getByte (regs .x10 + BitVec.ofNat 64 i) = (regs .x12).setWidth 8) ∧
      (∀ a, (∀ i < (regs .x11).toNat, a ≠ regs .x10 + BitVec.ofNat 64 i) →
        m'.getByte a = m.getByte a) ∧ m'.code = m.code) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hv⟩ hk
  lsym f1_eq stop [4] with [hra, hsp]
  · -- no bytes
    apply hk
    exact ⟨fun i hi => by simp [hc] at hi, fun _ _ => rfl, rfl⟩
  · -- some bytes: the loop, with `n - 1` after the first
    have hn : (regs .x11).toNat - 1 + 1 = (regs .x11).toNat := by
      have : (regs .x11).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
      omega
    have hlt := (regs .x11).isLt
    refine fill_loop (regs .x12) ((regs .x11).toNat - 1) _ m (regs .x10) (by omega) ?_ ?_ ?_ ?_ ?_
      (by rw [hn]; exact hv) (fun r' m' hb hf hcd => hk r' m' ?_)
    · simp [lsym_simp]
    · simp [lsym_simp, hn]
    · simp [lsym_simp]
    · simp [lsym_simp, hra]
    · simp [lsym_simp, hsp]
    · rw [hn] at hb hf; exact ⟨hb, hf, hcd⟩

/-- **`fill` on the machine.** -/
theorem fill_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1001c#64) (hcode : Loaded fns s)
    (hv : ∀ i < (s.getReg .x11).toNat,
      isValidMemAddrSp1 (s.getReg .x10 + BitVec.ofNat 64 i) = true ∧
        noCodeAt s (s.getReg .x10 + BitVec.ofNat 64 i) 1 = true)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      (∀ i < (s.getReg .x11).toNat,
        t.getByte (s.getReg .x10 + BitVec.ofNat 64 i) = (s.getReg .x12).setWidth 8) →
      (∀ a, (∀ i < (s.getReg .x11).toNat, a ≠ s.getReg .x10 + BitVec.ofNat 64 i) →
        t.getByte a = s.getByte a) →
      t.code = s.code → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x1001c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode fill_contract ⟨rfl, rfl, hv⟩ ?_
  rintro t r' m' hag hpc' ⟨hb, hf, hcd⟩
  have hbyte : ∀ a, t.getByte a = m'.getByte a := fun a => by
    simp [MachineState.getByte, ← hag.mem]
  refine hk t hpc' (fun i hi => ?_) (fun a ha => ?_) ?_
  · rw [hbyte]; exact hb i hi
  · rw [hbyte]; exact hf a ha
  · rw [← hag.code]; exact hcd

/-! ## `count_ones` -/

theorem and_one (x : Word) : x &&& 1#64 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.and_one_is_mod]; omega

/-- The lowest bit and the bits above it. -/
theorem ones_step (x : Word) :
    BitVec.ofNat 64 (ones x.toNat) = (x &&& 1#64) + BitVec.ofNat 64 (ones (x >>> 1).toNat) := by
  rw [ones_eq x.toNat, BitVec.ofNat_add, and_one, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem half_le {x : Word} {k : Nat} (h : x.toNat ≤ k + 1) : (x >>> 1).toNat ≤ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

/-- **The loop of `count_ones`**, at its head with `x ≠ 0` left and the bits so far in `a1`:
    their sum is `t` throughout. -/
theorem count_ones_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (t : Word)
    (hpost : ∀ r', r' .x10 = t → rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m⟩) :
    ∀ k (regs : Reg → BitVec 64), (regs .x10).toNat ≤ k → regs .x10 ≠ 0#64 →
      regs .x11 + BitVec.ofNat 64 (ones (regs .x10).toNat) = t → regs .x1 = ret → regs .x2 = top →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨2, 4, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro regs hle hne; exact absurd (BitVec.eq_of_toNat_eq (by simpa using hle)) hne
  | succ k ih =>
    intro regs hle hne hinv hra hsp
    rw [ones_step, ← BitVec.add_assoc] at hinv
    lsym f2_eq stop [4] with [hra, hsp]
    · -- bits are left: the back edge
      refine ih _ (by simpa only [lsym_simp] using half_le hle) (by simpa only [lsym_simp] using hc)
        (by simpa only [lsym_simp] using hinv) (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp])
    · -- none are left
      apply hpost
      rw [hc] at hinv
      simpa [lsym_simp, ones] using hinv

/-- `count_ones(x)`: the number of one bits of `x`, the memory kept. -/
theorem count_ones_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = BitVec.ofNat 64 (ones (regs .x10).toNat) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq stop [4] with [hra, hsp]
  · -- zero
    apply hk
    exact ⟨by simp [lsym_simp, hc, ones], rfl⟩
  · -- not zero: the loop, with no bits counted
    apply count_ones_loop m _ (fun r' h => hk r' m ⟨h, rfl⟩) (regs .x10).toNat
    all_goals simp [lsym_simp, hc, hra, hsp]

/-- **`count_ones` on the machine.** -/
theorem count_ones_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10034#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (ones (s.getReg .x10).toNat) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x10034#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode count_ones_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

end Examples.Bytes.RiscV
