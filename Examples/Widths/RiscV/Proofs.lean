/-
  Examples.Widths.RiscV.Proofs

  `src/c/widths.c`, compiled by clang at -O2 (`elf/widths.elf`): every load and store width,
  signed and not, three byte loops, an unaligned little-endian read and a swap. Each function
  has its contract at Lprog, proved with `lsym`, and the same statement over riscv-zkvm's
  machine, through `SafeN.of_isa_contract`.

  * `set_bytes(p, v, n)`: the `n` bytes from `p` are `v`'s low byte; every other byte and the
    code are kept.
  * `copy_bytes(d, s, n)`: the `n` bytes at `d` become those at `s` (`bytesAt`), and no other
    byte changes, when no address is in both regions.
  * `str_len(s)`: the length of the string at `s` (`StrAt`).
  * `load_s8` … `load_u32`: the byte, halfword or 32-bit word at `p`, sign- or zero-extended
    as C converts a `signed char`, `short`, `int` or their unsigned kinds to `long`.
  * `store_widths(p, v)`: the low 1, 2, 4 and 8 bytes of `v` at `p`, `p + 2`, `p + 4` and
    `p + 8`; the byte `p + 1` and every byte outside the sixteen from `p` are kept.
  * `read_le32(p)`: the little-endian 32-bit value of the four bytes at `p` (`le32`), in `a0`
    sign-extended to 64 bits as the RV64 calling convention keeps an `unsigned int`.
  * `swap(a, b)`: the doublewords at `a` and `b` exchanged, whether or not `a = b`; every other
    doubleword of memory kept.

  No precondition asks that an address be valid, aligned, or not code: an access that is not
  traps, and a machine that traps does not return, so a contract, which speaks of the states the
  function returns in, holds of it. `lsym` gives each access's check as a hypothesis on the path
  after it (so `store_widths` learns that `p + 8`, hence `p`, is 8-aligned).

  `_start` loops forever by design (`for (;;);`): it never returns, and has no contract here.
-/

import Examples.Widths.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Widths.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Widths.RiscV.Image

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-! ## `set_bytes` -/

/-- **The loop of `set_bytes`**, at its head with `k + 1` bytes left from `p`. -/
theorem set_bytes_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (v : Word) :
    ∀ k (regs : Reg → BitVec 64) (m : MachineState) (p : Word), k + 1 < 2 ^ 64 →
      regs .x10 = p → regs .x12 = p + BitVec.ofNat 64 (k + 1) → regs .x11 = v →
      regs .x1 = ret → regs .x2 = top →
      (∀ r' m', (∀ i < k + 1, m'.getByte (p + BitVec.ofNat 64 i) = v.setWidth 8) →
        (∀ a, (∀ i < k + 1, a ≠ p + BitVec.ofNat 64 i) → m'.getByte a = m.getByte a) →
        m'.code = m.code → rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m'⟩) →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨0, 4, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro regs m p hk h10 h12 h11 hra hsp hpost
    lsym f0_eq stop [4] with [h10, h11, h12, hra, hsp]
    apply hpost
    · intro i hi; obtain rfl : i = 0 := by omega
      simp [getByte_setByte]
    · intro a ha
      have := ha 0 (by omega)
      simp at this
      simp [getByte_setByte, this]
    · simp
  | succ k ih =>
    intro regs m p hk h10 h12 h11 hra hsp hpost
    lsym f0_eq stop [4] with [h10, h11, h12, hra, hsp]
    · -- more bytes: the back edge
      refine ih _ _ (p + 1#64) (by omega) (by simp [lsym_simp]) ?_ (by simp [lsym_simp, h11])
        (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp]) ?_
      · simp [lsym_simp, h12, add_one_add]
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
        · simpa using hcd
    · -- the end pointer one byte on: `k + 1 = 0`
      exact absurd (end_next hk hc) (by omega)

/-- `set_bytes(p, v, n)`: the `n` bytes from `p` are `v`'s low byte; every other byte and the
    code are kept. -/
theorem set_bytes_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m _ m' =>
      (∀ i < (regs .x12).toNat, m'.getByte (regs .x10 + BitVec.ofNat 64 i) = (regs .x11).setWidth 8) ∧
      (∀ a, (∀ i < (regs .x12).toNat, a ≠ regs .x10 + BitVec.ofNat 64 i) →
        m'.getByte a = m.getByte a) ∧ m'.code = m.code) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq stop [4] with [hra, hsp]
  · -- no bytes
    apply hk
    exact ⟨fun i hi => by simp [hc] at hi, fun _ _ => rfl, rfl⟩
  · -- some bytes: the loop, with `n - 1` after the first
    have hn : (regs .x12).toNat - 1 + 1 = (regs .x12).toNat := by
      have : (regs .x12).toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq h)
      omega
    have hlt := (regs .x12).isLt
    refine set_bytes_loop (regs .x11) ((regs .x12).toNat - 1) _ m (regs .x10) (by omega) ?_ ?_ ?_
      ?_ ?_ (fun r' m' hb hf hcd => hk r' m' ?_)
    · simp [lsym_simp]
    · simp [lsym_simp, hn]
    · simp [lsym_simp]
    · simp [lsym_simp, hra]
    · simp [lsym_simp, hsp]
    · rw [hn] at hb hf; exact ⟨hb, hf, hcd⟩

/-- **`set_bytes` on the machine.** -/
theorem set_bytes_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      (∀ i < (s.getReg .x12).toNat,
        t.getByte (s.getReg .x10 + BitVec.ofNat 64 i) = (s.getReg .x11).setWidth 8) →
      (∀ a, (∀ i < (s.getReg .x12).toNat, a ≠ s.getReg .x10 + BitVec.ofNat 64 i) →
        t.getByte a = s.getByte a) →
      t.code = s.code → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode set_bytes_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨hb, hf, hcd⟩
  refine hk t hpc' (fun i hi => ?_) (fun a ha => ?_) ?_
  · rw [getByte_of_agree hag]; exact hb i hi
  · rw [getByte_of_agree hag]; exact hf a ha
  · rw [← hag.code]; exact hcd

/-! ## `copy_bytes` -/

/-- **The copy loop**, at its head with `j < n` bytes copied, on the register file. -/
theorem copy_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m0 : MachineState) (dst src : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hdis : ∀ i < n, ∀ j < n, dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hpost : ∀ r' m', Copied m0 dst src n m' → rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : MachineState), n - j = k → j < n →
      regs .x10 = dst + BitVec.ofNat 64 j → regs .x11 = src + BitVec.ofNat 64 j →
      regs .x12 = dst + BitVec.ofNat 64 n → regs .x1 = ret → regs .x2 = top →
      m.code = m0.code →
      (∀ i < j, m.getByte (dst + BitVec.ofNat 64 i) = m0.getByte (src + BitVec.ofNat 64 i)) →
      (∀ x, (∀ i < j, x ≠ dst + BitVec.ofNat 64 i) → m.getByte x = m0.getByte x) →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨1, 4, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ hk hj; omega
  | succ k ih =>
    intro j regs m hk hj h10 h11 h12 hra hsp hcode hdone hkept
    -- the byte read is the one that was there on entry: no byte written so far is at `src + j`
    have hsrc : m.getByte (src + BitVec.ofNat 64 j) = m0.getByte (src + BitVec.ofNat 64 j) :=
      hkept _ fun i hi => (hdis i (by omega) j hj).symm
    -- the memory after this byte: `j + 1` bytes copied, the others as they were
    have hdone' : ∀ i < j + 1,
        (m.setByte (dst + BitVec.ofNat 64 j) (m.getByte (src + BitVec.ofNat 64 j))).getByte
          (dst + BitVec.ofNat 64 i) = m0.getByte (src + BitVec.ofNat 64 i) := by
      intro i hi
      rw [getByte_setByte]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · have hne : dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j := fun h' => by
          have := add_ofNat_inj dst (by omega) (by omega) h'; omega
        simp only [hne, ↓reduceIte]; exact hdone i h
      · simp only [↓reduceIte]; exact hsrc
    have hkept' : ∀ x, (∀ i < j + 1, x ≠ dst + BitVec.ofNat 64 i) →
        (m.setByte (dst + BitVec.ofNat 64 j) (m.getByte (src + BitVec.ofNat 64 j))).getByte x =
          m0.getByte x := by
      intro x hx
      rw [getByte_setByte]
      simp only [hx j (by omega), ↓reduceIte]
      exact hkept x fun i hi => hx i (by omega)
    lsym f1_eq stop [4] with [h10, h11, h12, hra, hsp]
    · -- the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · obtain rfl : n = j + 1 := by omega
          exact absurd (ofNat_succ j) hc
      apply ih (j + 1) _ _ (by omega) hlt
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, h12]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · simpa using hcode
      · exact hdone'
      · exact hkept'
    · -- the exit: every byte is copied
      have hjn : j + 1 = n := by
        rw [ofNat_succ] at hc
        exact ofNat_inj (by omega) hn hc
      subst hjn
      apply hpost
      exact ⟨(bytesAt_eq_iff _ _ _ _ _).mpr hdone', hkept', by simpa using hcode⟩

/-- **`copy_bytes(dst, src, n)`**: the `n` bytes at `dst` become those at `src`, and no other
    byte changes, when no address is in both regions. -/
theorem copy_bytes_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧
      (∀ i < (regs .x12).toNat, ∀ j < (regs .x12).toNat,
        regs .x10 + BitVec.ofNat 64 i ≠ regs .x11 + BitVec.ofNat 64 j))
    (fun _ _ regs m _ m' => Copied m (regs .x10) (regs .x11) (regs .x12).toNat m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hdis⟩ hk
  lsym f1_eq stop [4] with [hra, hsp]
  · -- no bytes
    apply hk
    exact ⟨by simp [bytesAt, hc], fun _ _ => rfl, rfl⟩
  · -- some bytes: the loop
    have hpos : 0 < (regs .x12).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x12).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hc
      · exact h
    exact copy_loop m (regs .x10) (regs .x11) _ (regs .x12).isLt hdis hk _ 0 _ m rfl hpos
      (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp, hra])
      (by simp [lsym_simp, hsp]) rfl (fun i hi => absurd hi (Nat.not_lt_zero i)) (fun _ _ => rfl)

/-- **`copy_bytes` on the machine.** -/
theorem copy_bytes_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1018#64) (hcode : Loaded fns s)
    (hdis : ∀ i < (s.getReg .x12).toNat, ∀ j < (s.getReg .x12).toNat,
      s.getReg .x10 + BitVec.ofNat 64 i ≠ s.getReg .x11 + BitVec.ofNat 64 j)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      bytesAt t (s.getReg .x10) (s.getReg .x12).toNat =
        bytesAt s (s.getReg .x11) (s.getReg .x12).toNat →
      (∀ x, (∀ i < (s.getReg .x12).toNat, x ≠ s.getReg .x10 + BitVec.ofNat 64 i) →
        t.getByte x = s.getByte x) →
      t.code = s.code → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x1018#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode copy_bytes_contract
    ⟨rfl, rfl, hdis⟩ ?_
  rintro t r' m' hag hpc' ⟨hbytes, hkept, hcd⟩
  refine hk t hpc' ?_ (fun x hx => ?_) ?_
  · refine Eq.trans ?_ hbytes; simp only [bytesAt, getByte_of_agree hag, regsOf]
  · rw [getByte_of_agree hag]; exact hkept x hx
  · rw [← hag.code]; exact hcd

/-! ## `str_len` -/

/-- **The loop of `str_len`**, at its head with `j ≤ n` bytes counted. -/
theorem str_len_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (s : Word) (n : Nat) (hstr : StrAt m s n)
    (hpost : ∀ r', r' .x10 = BitVec.ofNat 64 n →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m⟩) :
    ∀ k j (regs : Reg → BitVec 64), n - j = k → j ≤ n →
      regs .x10 = s → regs .x11 = BitVec.ofNat 64 j → regs .x1 = ret → regs .x2 = top →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨2, 2, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero =>
    intro j regs hk hj h10 h11 hra hsp
    obtain rfl : j = n := by omega
    lsym f2_eq stop [2] with [h10, h11, hra, hsp]
    · exact absurd ((zext_byte_eq_zero _).mpr hstr.2.2) hc
    · apply hpost; simp [lsym_simp]
  | succ k ih =>
    intro j regs hk hj h10 h11 hra hsp
    lsym f2_eq stop [2] with [h10, h11, hra, hsp]
    · -- the byte is not zero: the back edge
      apply ih (j + 1) _ (by omega) (by omega)
      all_goals simp [lsym_simp, ofNat_succ, h10, hra, hsp]
    · -- the byte is zero, before the string's end
      exact absurd ((zext_byte_eq_zero _).mp hc) (hstr.2.1 j (by omega))

/-- `str_len(s)`: the length of the string at `s`, the memory kept. -/
theorem str_len_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧ ∃ n, StrAt m (regs .x10) n)
    (fun _ _ regs m r' m' =>
      (∀ n, StrAt m (regs .x10) n → r' .x10 = BitVec.ofNat 64 n) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, n, hstr⟩ hk
  lsym f2_eq stop [2] with [hra, hsp]
  refine str_len_loop m (regs .x10) n hstr
    (fun r' h => hk r' m ⟨fun n' h' => by rw [h, hstr.unique h'], rfl⟩) n 0 _ (by omega)
    (by omega) ?_ ?_ ?_ ?_
  all_goals simp [lsym_simp, hra, hsp]

/-- **`str_len` on the machine.** -/
theorem str_len_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1038#64) (hcode : Loaded fns s) (n : Nat)
    (hstr : StrAt s (s.getReg .x10) n)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 → t.getReg .x10 = BitVec.ofNat 64 n →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x1038#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode str_len_contract ⟨rfl, rfl, n, hstr⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10 n hstr

/-! ## Loads of every width -/

/-- `load_s8(p)`: the `signed char` at `p`, sign-extended to `long`; every other register and
    the memory kept. -/
theorem load_s8_contract : rvIsa.Contract (liftProg fns) sp1Ctx 3
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = (m.getByte (regs .x10)).signExtend 64 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f3_eq with [hra, hsp]
  exact hk _ _ ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`load_s8` on the machine.** -/
theorem load_s8_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1054#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (s.getByte (s.getReg .x10)).signExtend 64 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[3]? = some fn ∧ fn.base = 0x1054#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode load_s8_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `load_u8(p)`: the `unsigned char` at `p`, zero-extended to `unsigned long`; every other
    register and the memory kept. -/
theorem load_u8_contract : rvIsa.Contract (liftProg fns) sp1Ctx 4
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = (m.getByte (regs .x10)).zeroExtend 64 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f4_eq with [hra, hsp]
  exact hk _ _ ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`load_u8` on the machine.** -/
theorem load_u8_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x105c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (s.getByte (s.getReg .x10)).zeroExtend 64 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[4]? = some fn ∧ fn.base = 0x105c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode load_u8_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `load_s16(p)`: the `short` at `p`, sign-extended to `long`; every other register and the
    memory kept. -/
theorem load_s16_contract : rvIsa.Contract (liftProg fns) sp1Ctx 5
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = (m.getHalfword (regs .x10)).signExtend 64 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f5_eq with [hra, hsp]
  exact hk _ _ ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`load_s16` on the machine.** -/
theorem load_s16_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1064#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (s.getHalfword (s.getReg .x10)).signExtend 64 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[5]? = some fn ∧ fn.base = 0x1064#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode load_s16_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `load_u16(p)`: the `unsigned short` at `p`, zero-extended to `unsigned long`; every other
    register and the memory kept. -/
theorem load_u16_contract : rvIsa.Contract (liftProg fns) sp1Ctx 6
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = (m.getHalfword (regs .x10)).zeroExtend 64 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f6_eq with [hra, hsp]
  exact hk _ _ ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`load_u16` on the machine.** -/
theorem load_u16_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x106c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (s.getHalfword (s.getReg .x10)).zeroExtend 64 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[6]? = some fn ∧ fn.base = 0x106c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode load_u16_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `load_s32(p)`: the `int` at `p`, sign-extended to `long`; every other register and the
    memory kept. -/
theorem load_s32_contract : rvIsa.Contract (liftProg fns) sp1Ctx 7
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = (m.getWord32 (regs .x10)).signExtend 64 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f7_eq with [hra, hsp]
  exact hk _ _ ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`load_s32` on the machine.** -/
theorem load_s32_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1074#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (s.getWord32 (s.getReg .x10)).signExtend 64 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[7]? = some fn ∧ fn.base = 0x1074#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode load_s32_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-- `load_u32(p)`: the `unsigned` at `p`, zero-extended to `unsigned long`; every other
    register and the memory kept. -/
theorem load_u32_contract : rvIsa.Contract (liftProg fns) sp1Ctx 8
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = (m.getWord32 (regs .x10)).zeroExtend 64 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f8_eq with [hra, hsp]
  exact hk _ _ ⟨by simp [lsym_simp], fun r h => by simp [lsym_simp, h], rfl⟩

/-- **`load_u32` on the machine.** -/
theorem load_u32_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x107c#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (s.getWord32 (s.getReg .x10)).zeroExtend 64 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[8]? = some fn ∧ fn.base = 0x107c#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode load_u32_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## `store_widths` -/

/-- The doubleword at `p` after `store_widths` writes its low byte, halfword at `p + 2` and
    word at `p + 4`, from the doubleword `w` there before. -/
def stored (w v : Word) : Word :=
  replaceWord32 (replaceHalfword (replaceByte w 0 (v.setWidth 8)) 1 (v.setWidth 16)) 1 (v.setWidth 32)

theorem stored_byte0 (w v : Word) : extractByte (stored w v) 0 = v.setWidth 8 := by
  simp only [stored, extractByte, replaceByte, replaceHalfword, replaceWord32]; bv_decide

theorem stored_byte1 (w v : Word) : extractByte (stored w v) 1 = extractByte w 1 := by
  simp only [stored, extractByte, replaceByte, replaceHalfword, replaceWord32]; bv_decide

theorem stored_half1 (w v : Word) : extractHalfword (stored w v) 1 = v.setWidth 16 := by
  simp only [stored, extractHalfword, replaceByte, replaceHalfword, replaceWord32]; bv_decide

theorem stored_word1 (w v : Word) : extractWord32 (stored w v) 1 = v.setWidth 32 := by
  simp only [stored, extractWord32, replaceByte, replaceHalfword, replaceWord32]; bv_decide

theorem aligned8_of_toNat {p : Word} (h : p.toNat % 8 = 0) : p &&& 7#64 = 0#64 := by
  have e : (p &&& 7#64).toNat = p.toNat % 8 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 3
  apply BitVec.eq_of_toNat_eq; rw [e, h]; rfl

theorem align_off (p : Word) (hp : p &&& 7#64 = 0#64) :
    alignToDword p = p ∧ alignToDword (p + 1#64) = p ∧ alignToDword (p + 2#64) = p ∧
      alignToDword (p + 4#64) = p ∧ byteOffset p = 0 ∧ byteOffset (p + 1#64) = 1 ∧
      byteOffset (p + 2#64) = 2 ∧ byteOffset (p + 4#64) = 4 ∧ p ≠ p + 8#64 := by
  have h1 : (p + 1#64) &&& 7#64 = 1#64 := by bv_decide
  have h2 : (p + 2#64) &&& 7#64 = 2#64 := by bv_decide
  have h4 : (p + 4#64) &&& 7#64 = 4#64 := by bv_decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [alignToDword, byteOffset, hp, h1, h2, h4]) <;> first | rfl | bv_decide

/-- The memory after the four stores, doubleword by doubleword. -/
theorem store_widths_mem (m : MachineState) (p v : Word) (hp : p &&& 7#64 = 0#64) (x : Word) :
    ((((m.setByte p (v.setWidth 8)).setHalfword (p + 2#64) (v.setWidth 16)).setWord32 (p + 4#64)
      (v.setWidth 32)).setMem (p + 8#64) v).getMem x =
      if x = p + 8#64 then v else if x = p then stored (m.getMem p) v else m.getMem x := by
  obtain ⟨a0, -, a2, a4, o0, -, o2, o4, hne⟩ := align_off p hp
  simp only [MachineState.setByte, MachineState.setHalfword, MachineState.setWord32,
    getMem_setMem, a0, a2, a4, o0, o2, o4, ↓reduceIte, stored]
  by_cases h1 : x = p + 8#64
  · simp [h1]
  · by_cases h2 : x = p <;> simp [h1, h2]

/-- `store_widths(p, v)`: the low byte of `v` at `p`, its low halfword at `p + 2`, its low word
    at `p + 4` and `v` at `p + 8`, each as that width reads; the byte at `p + 1`, every byte
    outside the sixteen from `p`, and the code kept. -/
theorem store_widths_contract : rvIsa.Contract (liftProg fns) sp1Ctx 9
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m _ m' => let p := regs .x10; let v := regs .x11
      m'.getByte p = v.setWidth 8 ∧ m'.getByte (p + 1#64) = m.getByte (p + 1#64) ∧
      m'.getHalfword (p + 2#64) = v.setWidth 16 ∧ m'.getWord32 (p + 4#64) = v.setWidth 32 ∧
      m'.getMem (p + 8#64) = v ∧
      (∀ a, 16 ≤ (a - p).toNat → m'.getByte a = m.getByte a) ∧ m'.code = m.code) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f9_eq with [hra, hsp]
  apply hk
  obtain ⟨-, h8⟩ : isValidMemAddrSp1 (regs .x10 + 8#64) = true ∧ (regs .x10).toNat % 8 = 0 := by
    simpa [isValidDwordAccessSp1] using hm.1
  have hp := aligned8_of_toNat h8
  generalize regs .x10 = p at hp ⊢
  generalize regs .x11 = v
  obtain ⟨a0, a1, a2, a4, o0, o1, o2, o4, hne⟩ := align_off p hp
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha => ?_, by simp⟩
  · simp only [MachineState.getByte, store_widths_mem m p v hp, a0, o0, hne, ↓reduceIte,
      stored_byte0]
  · simp only [MachineState.getByte, store_widths_mem m p v hp, a1, o1, hne, ↓reduceIte,
      stored_byte1]
  · simp only [MachineState.getHalfword, store_widths_mem m p v hp, a2, o2, hne, ↓reduceIte]
    exact stored_half1 _ _
  · simp only [MachineState.getWord32, store_widths_mem m p v hp, a4, o4, hne, ↓reduceIte]
    exact stored_word1 _ _
  · simp
  · have ha' : 16#64 ≤ a - p := by bv_omega
    have e1 : alignToDword a ≠ p + 8#64 := by simp only [alignToDword]; bv_decide
    have e2 : alignToDword a ≠ p := by simp only [alignToDword]; bv_decide
    simp only [MachineState.getByte, store_widths_mem m p v hp, e1, e2, ↓reduceIte]

/-- **`store_widths` on the machine.** -/
theorem store_widths_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1084#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getByte (s.getReg .x10) = (s.getReg .x11).setWidth 8 →
      t.getByte (s.getReg .x10 + 1#64) = s.getByte (s.getReg .x10 + 1#64) →
      t.getHalfword (s.getReg .x10 + 2#64) = (s.getReg .x11).setWidth 16 →
      t.getWord32 (s.getReg .x10 + 4#64) = (s.getReg .x11).setWidth 32 →
      t.getMem (s.getReg .x10 + 8#64) = s.getReg .x11 →
      (∀ a, 16 ≤ (a - s.getReg .x10).toNat → t.getByte a = s.getByte a) →
      t.code = s.code → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[9]? = some fn ∧ fn.base = 0x1084#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode store_widths_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h0, h1, h2, h4, h8, hf, hcd⟩
  simp only [regsOf] at h0 h1 h2 h4 h8 hf
  have hmem : ∀ x, t.getMem x = m'.getMem x := fun x => by rw [← hag.mem]; simp
  refine hk t hpc' ?_ ?_ ?_ ?_ ?_ (fun a ha => ?_) ?_
  · rw [getByte_of_agree hag]; simpa using h0
  · rw [getByte_of_agree hag]; simpa using h1
  · simp only [MachineState.getHalfword, hmem]; simpa [MachineState.getHalfword] using h2
  · simp only [MachineState.getWord32, hmem]; simpa [MachineState.getWord32] using h4
  · rw [hmem]; simpa using h8
  · rw [getByte_of_agree hag]; exact hf a (by simpa using ha)
  · rw [← hag.code]; exact hcd

/-! ## `read_le32` -/

/-- The little-endian 32-bit value of four bytes, `b0` the least significant. -/
def le32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

/-- What the shifts and ors compute: the four bytes in little-endian order, sign-extended. -/
theorem le32_eq (b0 b1 b2 b3 : BitVec 8) :
    (BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b0 |||
      (BitVec.setWidth 64 b2 <<< 16 ||| BitVec.signExtend 64 (BitVec.setWidth 32 b3 <<< 24))) =
      (le32 b0 b1 b2 b3).signExtend 64 := by
  simp only [le32]; bv_decide

/-- `read_le32(p)`: the little-endian 32-bit value of the four bytes at `p`, at any alignment;
    in `a0` sign-extended to 64 bits, as the RV64 calling convention returns an `unsigned int`.
    The memory is kept. -/
theorem read_le32_contract : rvIsa.Contract (liftProg fns) sp1Ctx 10
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => let p := regs .x10
      r' .x10 = (le32 (m.getByte p) (m.getByte (p + 1#64)) (m.getByte (p + 2#64))
        (m.getByte (p + 3#64))).signExtend 64 ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f10_eq with [hra, hsp]
  exact hk _ _ ⟨by simp only [lsym_simp]; exact le32_eq _ _ _ _, rfl⟩

/-- **`read_le32` on the machine.** -/
theorem read_le32_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x1098#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = (le32 (s.getByte (s.getReg .x10)) (s.getByte (s.getReg .x10 + 1#64))
        (s.getByte (s.getReg .x10 + 2#64)) (s.getByte (s.getReg .x10 + 3#64))).signExtend 64 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[10]? = some fn ∧ fn.base = 0x1098#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode read_le32_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

/-! ## `swap` -/

/-- `swap(a, b)`: the doublewords at `a` and `b` exchanged, whether or not `a = b`; every other
    doubleword of memory kept. -/
theorem swap_contract : rvIsa.Contract (liftProg fns) sp1Ctx 11
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m _ m' => m'.getMem (regs .x10) = m.getMem (regs .x11) ∧
      m'.getMem (regs .x11) = m.getMem (regs .x10) ∧
      (∀ c, c ≠ regs .x10 → c ≠ regs .x11 → m'.getMem c = m.getMem c)) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f11_eq with [hra, hsp]
  apply hk
  refine ⟨?_, ?_, ?_⟩
  · simp only [lsym_simp, MachineState.getMem, MachineState.setMem]
    split <;> simp_all
  · simp [lsym_simp, MachineState.getMem, MachineState.setMem]
  · intro c h1 h2; simp [lsym_simp, MachineState.getMem, MachineState.setMem, h1, h2]

/-- **`swap` on the machine.** -/
theorem swap_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10c4#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getMem (s.getReg .x10) = s.getMem (s.getReg .x11) →
      t.getMem (s.getReg .x11) = s.getMem (s.getReg .x10) →
      (∀ c, c ≠ s.getReg .x10 → c ≠ s.getReg .x11 → t.getMem c = s.getMem c) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[11]? = some fn ∧ fn.base = 0x10c4#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode swap_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h1, h2, h3⟩
  simp only [regsOf] at h1 h2 h3
  refine hk t hpc' ?_ ?_ fun c hc1 hc2 => ?_
  · rw [← hag.mem]; simpa using h1
  · rw [← hag.mem]; simpa using h2
  · rw [← hag.mem]; exact h3 c (by simpa using hc1) (by simpa using hc2)

end Examples.Widths.RiscV
