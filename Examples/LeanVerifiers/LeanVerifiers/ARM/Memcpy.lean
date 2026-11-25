/-
  LeanVerifiers.ARM.Memcpy

  rustc's `memcpy` of the AArch64 signature image (`Examples/elf/lean_signatures_a64.elf`), for
  every length: its contract at Lprog, proved with `lsym` on the lift.

  The code copies by doublewords when the low three bits of both addresses and of the length
  are zero, and by bytes otherwise. Each loop is a lemma at its head from an arbitrary
  iteration, by induction on what is left; one step of either is `Copied.step`.

  The lift of AArch64 is not proved yet, so nothing follows about the machine.
-/

import LeanVerifiers.ARM.Bytes
import LeanVerifiers.ARM.Signatures.F2

namespace LeanVerifiers.ARM

open Lprog Lprog.ARM LeanVerifiers.ARM.Signatures

/-- The registers `memcpy` may change: its counters, the lift's temporary and the flags. -/
def scratch : List Reg := [.x1, .x2, .x8, .x9, .t0, .nf, .zf, .cf, .vf]

/-- A register file that differs from `r0` on the scratch registers only. -/
def Kept (r0 r : Reg → BitVec 64) : Prop := ∀ x, x ∉ scratch → r x = r0 x

/-- **The byte loop**, at its head with `j < n` bytes copied. -/
theorem byte_loop {G : State armIsa → Prop} {N : Nat} {Q : State armIsa → Prop}
    {ret top : BitVec 64} {rest : List Frame} (m0 : Bytes) (r0 : Reg → BitVec 64)
    (dst src : BitVec 64) (n : Nat) (hn : n < 2 ^ 64)
    (hdis : ∀ i < n, ∀ j < n, dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hpost : ∀ r' m', Copied m0 dst src n m' → Kept r0 r' →
      armIsa.SafeN program.lift ctx G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : Bytes), n - j = k → j < n →
      regs .x8 = dst + BitVec.ofNat 64 j → regs .x1 = src + BitVec.ofNat 64 j →
      regs .x2 = BitVec.ofNat 64 (n - j) → regs .x30 = ret → regs .sp = top → Kept r0 regs →
      Copied m0 dst src j m →
      armIsa.SafeN program.lift ctx G N Q ⟨⟨2, 16, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ hk hj; omega
  | succ k ih =>
    intro j regs m hk hj h8 h1 h2 hra hsp hreg hcop
    have hstep := hcop.step 1 (by omega) (by omega) hn hdis
    lsym f2_eq stop [16] with [h8, h1, h2, hra, hsp]
    all_goals rw [ofNat_add_neg_one (by omega)] at hc
    · -- the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · exact absurd (by rw [show n - j - 1 = 0 by omega]) hc
      apply ih (j + 1) _ _ (by omega) hlt _ _ _ _ _ _ hstep
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, ofNat_add_neg_one (show 0 < n - j by omega),
          show n - j - 1 = n - (j + 1) by omega]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · intro r hr; rw [← hreg r hr]; simp [scratch] at hr; simp [updReg_apply, hr]
    · -- the exit: every byte is copied
      obtain rfl : n = j + 1 := by have := ofNat_eq_zero (by omega) hc; omega
      apply hpost _ _ hstep
      intro r hr; rw [← hreg r hr]; simp [scratch] at hr; simp [updReg_apply, hr]

/-- **The word loop**, at its head with `8 * j < n` bytes copied, `n` a multiple of 8. -/
theorem word_loop {G : State armIsa → Prop} {N : Nat} {Q : State armIsa → Prop}
    {ret top : BitVec 64} {rest : List Frame} (m0 : Bytes) (r0 : Reg → BitVec 64)
    (dst src : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) (h8 : n % 8 = 0)
    (hdis : ∀ i < n, ∀ j < n, dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hpost : ∀ r' m', Copied m0 dst src n m' → Kept r0 r' →
      armIsa.SafeN program.lift ctx G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : Bytes), n / 8 - j = k → 8 * j < n →
      regs .x8 = BitVec.ofNat 64 (8 * j) → regs .x0 = dst → regs .x1 = src →
      regs .x2 = BitVec.ofNat 64 n → regs .x30 = ret → regs .sp = top → Kept r0 regs →
      Copied m0 dst src (8 * j) m →
      armIsa.SafeN program.lift ctx G N Q ⟨⟨2, 37, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ hk hj; omega
  | succ k ih =>
    intro j regs m hk hj hx8 h0 h1 h2 hra hsp hreg hcop
    have hstep := hcop.step 8 (by omega) (by omega) hn hdis
    have hnext : BitVec.ofNat 64 (8 * j) + 8#64 = BitVec.ofNat 64 (8 * (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp [Nat.mul_add]
    lsym f2_eq stop [37] with [hx8, h0, h1, h2, hra, hsp]
    all_goals rw [hnext] at hc
    · -- the back edge
      have hlt : 8 * (j + 1) < n := by
        simp only [BitVec.lt_def, BitVec.toNat_ofNat] at hc; omega
      apply ih (j + 1) _ _ (by omega) hlt _ _ _ _ _ _ _ hstep
      · simp [lsym_simp, hnext]
      · simp [lsym_simp, h0]
      · simp [lsym_simp, h1]
      · simp [lsym_simp, h2]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · intro r hr; rw [← hreg r hr]; simp [scratch] at hr; simp [updReg_apply, hr]
    · -- the exit: every byte is copied
      obtain rfl : 8 * j + 8 = n := by
        simp only [BitVec.le_def, BitVec.toNat_ofNat] at hc; omega
      apply hpost _ _ hstep
      intro r hr; rw [← hreg r hr]; simp [scratch] at hr; simp [updReg_apply, hr]

/-- **`memcpy(dst, src, n)`**: the `n` bytes at `dst` become those at `src`, no other byte
    changes, and no register but the scratch ones does (so `x0` is still `dst`). No address is
    in both regions. -/
theorem memcpy_contract : armIsa.Contract program.lift ctx 2
    (fun ret top regs _ => regs .x30 = ret ∧ regs .sp = top ∧
      ∀ i < (regs .x2).toNat, ∀ j < (regs .x2).toNat,
        regs .x0 + BitVec.ofNat 64 i ≠ regs .x1 + BitVec.ofNat 64 j)
    (fun _ _ regs m r' m' =>
      Copied m (regs .x0) (regs .x1) (regs .x2).toNat m' ∧ Kept regs r') := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hdis⟩ hk
  have hzero : regs .x2 = 0#64 → Copied m (regs .x0) (regs .x1) (regs .x2).toNat m := fun h =>
    ⟨by simp [h], fun _ _ => rfl⟩
  have hpos : ¬regs .x2 = 0#64 → 0 < (regs .x2).toNat := fun h =>
    Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq h')
  have hstart : Copied m (regs .x0) (regs .x1) 0 m := ⟨by simp, fun _ _ => rfl⟩
  lsym f2_eq stop [16, 37] with [hra, hsp]
  · -- aligned, no bytes
    refine hk _ _ ⟨hzero hc, ?_⟩
    intro r hr; simp [scratch] at hr; simp [updReg_apply, hr]
  · -- aligned, some bytes: the word loop
    refine word_loop m regs (regs .x0) (regs .x1) _ (regs .x2).isLt ?_ hdis
      (fun r' m' h h' => hk r' m' ⟨h, h'⟩) _ 0 _ m rfl (hpos hc) (by simp [lsym_simp])
      (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp, hra])
      (by simp [lsym_simp, hsp]) ?_ hstart
    · have : regs .x2 &&& 7#64 = 0#64 := by bv_decide
      have h := congrArg BitVec.toNat this
      rw [BitVec.toNat_and] at h
      exact (Nat.and_two_pow_sub_one_eq_mod _ 3).symm.trans h
    · intro r hr; simp [scratch] at hr; simp [updReg_apply, hr]
  · -- not aligned, no bytes
    refine hk _ _ ⟨hzero hc, ?_⟩
    intro r hr; simp [scratch] at hr; simp [updReg_apply, hr]
  · -- not aligned, some bytes: the byte loop
    refine byte_loop m regs (regs .x0) (regs .x1) _ (regs .x2).isLt hdis
      (fun r' m' h h' => hk r' m' ⟨h, h'⟩) _ 0 _ m rfl (hpos hc) (by simp [lsym_simp])
      (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp, hra])
      (by simp [lsym_simp, hsp]) ?_ hstart
    intro r hr; simp [scratch] at hr; simp [updReg_apply, hr]

end LeanVerifiers.ARM
