/-
  Examples.Mem.RiscV.Proofs

  `copy_bytes` and `equal_bytes` of `Examples/src/c/mem.c`, compiled by clang
  (`Examples/elf/mem.elf`), for every length: each function's contract at Lprog, proved with
  `lsym`, and the same statement over riscv-zkvm's machine.

  The specification is over the list of the `n` bytes from an address (`bytesAt`):
  `copy_bytes(dst, src, n)` leaves at `dst` the bytes that were at `src` and changes no other
  byte, when no address is in both regions; `equal_bytes(a, b, n)` returns 1 if the bytes at
  `a` and at `b` are the same list and 0 otherwise, and changes no memory.

  Each function is one loop, a lemma at the loop head from an arbitrary iteration, proved by
  induction on the bytes left. Addresses are `base + i` modulo 2^64, so no condition that a
  region does not wrap is needed: the validity of each of its bytes already excludes it.
-/

import Examples.Mem.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Mem.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Mem.RiscV.Image

theorem hok : ProgOk fns := by decide

/-! ## Bytes -/

/-- Two byte lists of memory are equal when they agree byte by byte. -/
theorem bytesAt_eq_iff (m m' : MachineState) (a b : Word) (n : Nat) :
    bytesAt m a n = bytesAt m' b n ↔
      ∀ i < n, m.getByte (a + BitVec.ofNat 64 i) = m'.getByte (b + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.map_inj_left]

/-- Whether a store hits code depends on the code alone. -/
theorem noCodeAt_of_code {m m0 : MachineState} (h : m.code = m0.code) (a : Word) (w : Nat) :
    noCodeAt m a w = noCodeAt m0 a w := by
  simp [noCodeAt, h]

theorem zeroExtend_byte_inj (x y : BitVec 8) (h : BitVec.zeroExtend 64 x = BitVec.zeroExtend 64 y) :
    x = y := by
  bv_decide

/-- A machine state reads the bytes of a memory it agrees with. -/
theorem getByte_of_agree {r' : Reg → BitVec 64} {m' t : MachineState} (h : Agree (ofParts r' m') t)
    (x : Word) : t.getByte x = m'.getByte x := by
  simp only [MachineState.getByte, ← h.mem, getMem_ofParts]

theorem add_ofNat_inj (a : Word) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 j) : i = j := by
  bv_omega

theorem ofNat_inj {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : BitVec.ofNat 64 i = BitVec.ofNat 64 j) : i = j := by
  bv_omega

theorem ofNat_eq_zero {x : Nat} (hx : x < 2 ^ 64) (h : BitVec.ofNat 64 x = 0#64) : x = 0 := by
  bv_omega

theorem ofNat_add_neg_one {x : Nat} (h : 0 < x) :
    BitVec.ofNat 64 x + 18446744073709551615#64 = BitVec.ofNat 64 (x - 1) := by
  bv_omega

/-! ## `copy_bytes` -/

/-- What `copy_bytes(dst, src, n)` leaves in the memory `m'`, from the memory `m`. -/
def Copied (m : MachineState) (dst src : Word) (n : Nat) (m' : MachineState) : Prop :=
  bytesAt m' dst n = bytesAt m src n ∧
  (∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → m'.getByte x = m.getByte x) ∧
  m'.code = m.code

/-- **The copy loop**, at its head with `j < n` bytes copied, on the register file. -/
theorem copy_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m0 : MachineState) (dst src : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hvs : ∀ i < n, isValidMemAddrSp1 (src + BitVec.ofNat 64 i) = true)
    (hvd : ∀ i < n, isValidMemAddrSp1 (dst + BitVec.ofNat 64 i) = true ∧
      noCodeAt m0 (dst + BitVec.ofNat 64 i) 1 = true)
    (hdis : ∀ i < n, ∀ j < n, dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hpost : ∀ r' m', Copied m0 dst src n m' → rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : MachineState), n - j = k → j < n →
      regs .x10 = dst + BitVec.ofNat 64 j → regs .x11 = src + BitVec.ofNat 64 j →
      regs .x12 = dst + BitVec.ofNat 64 n → regs .x1 = ret → regs .x2 = top →
      m.code = m0.code →
      (∀ i < j, m.getByte (dst + BitVec.ofNat 64 i) = m0.getByte (src + BitVec.ofNat 64 i)) →
      (∀ x, (∀ i < j, x ≠ dst + BitVec.ofNat 64 i) → m.getByte x = m0.getByte x) →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨0, 4, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ hk hj; omega
  | succ k ih =>
    intro j regs m hk hj h10 h11 h12 hra hsp hcode hdone hkept
    have hnc := noCodeAt_of_code hcode (dst + BitVec.ofNat 64 j) 1
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
    lsym f0_eq stop [4] with [h10, h11, h12, hra, hsp, hvs j hj, hvd j hj, hnc]
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
    byte changes. The bytes at `src` are valid to read, those at `dst` valid to write and not
    code, and no address is in both regions. -/
theorem copy_bytes_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧
      (∀ i < (regs .x12).toNat, isValidMemAddrSp1 (regs .x11 + BitVec.ofNat 64 i) = true) ∧
      (∀ i < (regs .x12).toNat, isValidMemAddrSp1 (regs .x10 + BitVec.ofNat 64 i) = true ∧
        noCodeAt m (regs .x10 + BitVec.ofNat 64 i) 1 = true) ∧
      (∀ i < (regs .x12).toNat, ∀ j < (regs .x12).toNat,
        regs .x10 + BitVec.ofNat 64 i ≠ regs .x11 + BitVec.ofNat 64 j))
    (fun _ _ regs m _ m' => Copied m (regs .x10) (regs .x11) (regs .x12).toNat m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hvs, hvd, hdis⟩ hk
  lsym f0_eq stop [4] with [hra, hsp]
  · -- no bytes
    apply hk
    exact ⟨by simp [bytesAt, hc], fun _ _ => rfl, rfl⟩
  · -- some bytes: the loop
    have hpos : 0 < (regs .x12).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x12).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hc
      · exact h
    exact copy_loop m (regs .x10) (regs .x11) _ (regs .x12).isLt hvs hvd hdis hk _ 0 _ m rfl hpos
      (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp, hra])
      (by simp [lsym_simp, hsp]) rfl (fun i hi => absurd hi (Nat.not_lt_zero i)) (fun _ _ => rfl)

/-- **`copy_bytes` on the machine.** -/
theorem copy_bytes_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s)
    (hvs : ∀ i < (s.getReg .x12).toNat,
      isValidMemAddrSp1 (s.getReg .x11 + BitVec.ofNat 64 i) = true)
    (hvd : ∀ i < (s.getReg .x12).toNat,
      isValidMemAddrSp1 (s.getReg .x10 + BitVec.ofNat 64 i) = true ∧
        noCodeAt s (s.getReg .x10 + BitVec.ofNat 64 i) 1 = true)
    (hdis : ∀ i < (s.getReg .x12).toNat, ∀ j < (s.getReg .x12).toNat,
      s.getReg .x10 + BitVec.ofNat 64 i ≠ s.getReg .x11 + BitVec.ofNat 64 j)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      bytesAt t (s.getReg .x10) (s.getReg .x12).toNat =
        bytesAt s (s.getReg .x11) (s.getReg .x12).toNat →
      (∀ x, (∀ i < (s.getReg .x12).toNat, x ≠ s.getReg .x10 + BitVec.ofNat 64 i) →
        t.getByte x = s.getByte x) →
      SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode copy_bytes_contract
    ⟨rfl, rfl, hvs, hvd, hdis⟩ ?_
  rintro t r' m' hag hpc' ⟨hbytes, hkept, -⟩
  refine hk t hpc' ?_ fun x hx => ?_
  · refine Eq.trans ?_ hbytes; simp only [bytesAt, getByte_of_agree hag, regsOf]
  · rw [getByte_of_agree hag]; exact hkept x hx

/-! ## `equal_bytes` -/

/-- **The comparison loop**, at its head with `j < n` bytes found equal, on the register file. -/
theorem equal_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (a b : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (hpost : ∀ r', r' .x10 = equalSpec (bytesAt m a n) (bytesAt m b n) →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m⟩) :
    ∀ k j (regs : Reg → BitVec 64), n - j = k → j < n →
      regs .x13 = a + BitVec.ofNat 64 j → regs .x11 = b + BitVec.ofNat 64 j →
      regs .x12 = BitVec.ofNat 64 (n - j) → regs .x10 = 1#64 → regs .x1 = ret → regs .x2 = top →
      (∀ i < j, m.getByte (a + BitVec.ofNat 64 i) = m.getByte (b + BitVec.ofNat 64 i)) →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨1, 6, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ hk hj; omega
  | succ k ih =>
    intro j regs hk hj h13 h11 h12 h10 hra hsp hbytes
    lsym f1_eq stop [6] with [h13, h11, h12, h10, hra, hsp, hva j hj, hvb j hj]
    · -- the bytes differ
      apply hpost
      have hne : bytesAt m a n ≠ bytesAt m b n := fun h =>
        hc (congrArg _ ((bytesAt_eq_iff _ _ _ _ _).mp h j hj))
      simp [lsym_simp, equalSpec, hne]
    · -- the bytes agree and some are left: the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | hge
        · exact h
        · rw [ofNat_add_neg_one (by omega), show n - j - 1 = 0 by omega] at hc; exact absurd rfl hc
      apply ih (j + 1) _ (by omega) hlt
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, ofNat_add_neg_one (show 0 < n - j by omega),
          show n - j - 1 = n - (j + 1) by omega]
      · simp [lsym_simp, h10]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact hbytes i h
        · exact zeroExtend_byte_inj _ _ hc_1
    · -- the bytes agree and none are left
      have hz : n = j + 1 := by
        rw [ofNat_add_neg_one (by omega)] at hc
        have := ofNat_eq_zero (by omega) hc; omega
      apply hpost
      have heq : bytesAt m a n = bytesAt m b n := by
        rw [bytesAt_eq_iff]; intro i hi
        rcases Nat.lt_or_ge i j with h | h
        · exact hbytes i h
        · obtain rfl : i = j := by omega
          exact zeroExtend_byte_inj _ _ hc_1
      simp [lsym_simp, equalSpec, heq, h10]

/-- **`equal_bytes(a, b, n)`**: 1 if the `n` bytes at `a` and at `b` are the same, and 0
    otherwise; the memory is kept. The bytes of both regions are valid to read. -/
theorem equal_bytes_contract : rvIsa.Contract (liftProg fns) sp1Ctx 1
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top ∧
      (∀ i < (regs .x12).toNat, isValidMemAddrSp1 (regs .x10 + BitVec.ofNat 64 i) = true) ∧
      (∀ i < (regs .x12).toNat, isValidMemAddrSp1 (regs .x11 + BitVec.ofNat 64 i) = true))
    (fun _ _ regs m r' m' =>
      r' .x10 = equalSpec (bytesAt m (regs .x10) (regs .x12).toNat)
        (bytesAt m (regs .x11) (regs .x12).toNat) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hva, hvb⟩ hk
  lsym f1_eq stop [6] with [hra, hsp]
  · -- no bytes
    apply hk
    exact ⟨by simp [lsym_simp, equalSpec, bytesAt, hc], rfl⟩
  · -- some bytes: the loop
    have hpos : 0 < (regs .x12).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x12).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hc
      · exact h
    exact equal_loop m (regs .x10) (regs .x11) _ (regs .x12).isLt hva hvb (fun r' h => hk r' m ⟨h, rfl⟩)
      _ 0 _ rfl hpos (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp])
      (by simp [lsym_simp]) (by simp [lsym_simp, hra]) (by simp [lsym_simp, hsp])
      (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- **`equal_bytes` on the machine.** -/
theorem equal_bytes_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10020#64) (hcode : Loaded fns s)
    (hva : ∀ i < (s.getReg .x12).toNat,
      isValidMemAddrSp1 (s.getReg .x10 + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < (s.getReg .x12).toNat,
      isValidMemAddrSp1 (s.getReg .x11 + BitVec.ofNat 64 i) = true)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = equalSpec (bytesAt s (s.getReg .x10) (s.getReg .x12).toNat)
        (bytesAt s (s.getReg .x11) (s.getReg .x12).toNat) →
      (∀ x, t.getMem x = s.getMem x) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[1]? = some fn ∧ fn.base = 0x10020#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode equal_bytes_contract ⟨rfl, rfl, hva, hvb⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, rfl⟩
  refine hk t hpc' ?_ fun x => (hag.mem x).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10

end Examples.Mem.RiscV
