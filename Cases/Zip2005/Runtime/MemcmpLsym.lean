/-
  Cases.Zip2005.Runtime.MemcmpLsym

  `memcmp(a, b, n)` at Lprog again, with `lsym` (`Lprog/Tactic.lean`): the same contract as
  `MemcmpLprog.lean`, which steps each instruction by hand. The theorem over `stepSp1`
  (`MemcmpLprog.safe`) is not restated: it follows from the contract the same way.
  `lsym` steps the body, computes each operation, and closes the memory checks of the loads
  and the conditions of the returns; what is left is what the function means: the loop's
  invariant at its head, and the postcondition at each return.

  The loop is stated on Lprog's register file, not on a machine state that agrees with it:
  `lsym` computes registers as `updReg`, so their values are read off by `simp`.
-/

import Cases.Zip2005.Runtime.MemcmpLprog
import LprogRiscV.Lsym

namespace Cases.Zip2005.MemcmpLsym

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Cases.Zip2005.Image Lprog.RiscV Lprog.RiscV.Machine Cases.Zip2005.MemcmpLprog

/-- A register other than `x0`, read from a machine state built from a register file. -/
theorem getReg_ofParts_ne {r : Reg} (h : r ≠ .x0) (regs : Reg → BitVec 64) (m : MachineState) :
    (ofParts regs m).getReg r = regs r := by
  rw [getReg_ofParts]; simp [h]

theorem ofNat_succ (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- **The byte loop**, from byte `j < n`, at the loop head, on the register file. -/
theorem loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (u0 : MachineState) (a b : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (hpost : ∀ r' m', Post u0 a b n (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : MachineState), n - j = k → j < n →
      regs .x10 = a + BitVec.ofNat 64 j → regs .x11 = b + BitVec.ofNat 64 j →
      regs .x12 = BitVec.ofNat 64 (n - j) → regs .x1 = ret → regs .x2 = top →
      (∀ addr, m.getMem addr = u0.getMem addr) → m.code = u0.code →
      (∀ r, r ∉ clobbered → r ≠ .x0 → regs r = u0.getReg r) →
      (∀ i < j, u0.getByte (a + BitVec.ofNat 64 i) = u0.getByte (b + BitVec.ofNat 64 i)) →
      LSafeN fs G N Q ⟨⟨0, 2, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ hk hj; omega
  | succ k ih =>
    intro j regs m hk hj h10 h11 h12 hra hsp hmem hcode hkept hbytes
    have hbyte : ∀ x, m.getByte x = u0.getByte x := fun x => by simp [MachineState.getByte, hmem]
    lsym hf stop [2] with [h10, h11, h12, hra, hsp, hva j hj, hvb j hj]
    · -- the bytes differ: the result is their difference
      apply hpost
      refine ⟨?_, fun addr => ?_, ?_, fun r hr => ?_, ?_⟩
      · simp [getReg_ofParts_ne (show Reg.x10 ≠ .x0 by decide), lsym_simp, hbyte] at hc ⊢
        constructor
        · intro h; exact absurd (by bv_omega) hc
        · intro h; exact absurd (congrArg _ (h j hj)) hc
      · simp [hmem]
      · exact hcode
      · by_cases h0 : r = .x0
        · subst h0; simp [getReg_x0]
        · rw [getReg_ofParts_ne h0]
          simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h10', h11', h12', h13, h14⟩ := hr
          simp [lsym_simp, h10', h13, h14, hkept r (by simp [clobbered, *]) h0]
      · rw [getReg_ofParts_ne (by decide)]
        simp only [lsym_simp, hbyte, ↓reduceIte, reduceCtorEq]
        rw [BitVec.sub_eq_add_neg]; exact sext32_sub_bytes _ _
    · -- the bytes agree and some are left: the back edge
      rename_i hb
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | hge
        · exact h
        · rw [ofNat_add_neg_one (by omega), show n - j - 1 = 0 by omega] at hc; exact absurd rfl hc
      apply ih (j + 1) _ m (by omega) hlt
      · simp [lsym_simp, h10, BitVec.add_assoc, ofNat_succ]
      · simp [lsym_simp, h11, BitVec.add_assoc, ofNat_succ]
      · simp [lsym_simp, h12, ofNat_add_neg_one (show 0 < n - j by omega), show n - j - 1 = n - (j + 1) by omega]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact hmem
      · exact hcode
      · intro r hr h0
        simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h10', h11', h12', h13, h14⟩ := hr
        simp [lsym_simp, h10', h11', h12', h13, h14, hkept r (by simp [clobbered, *]) h0]
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact hbytes i h
        · rw [← hbyte, ← hbyte]; exact zeroExtend_byte_inj _ _ hb
    · -- the bytes agree and none are left: the blocks are equal
      rename_i hb
      have hz : n - (j + 1) = 0 := by
        rw [ofNat_add_neg_one (by omega)] at hc
        have := ofNat_eq_zero (by omega) hc; omega
      apply hpost
      refine ⟨?_, fun addr => ?_, ?_, fun r hr => ?_, ?_⟩
      · rw [getReg_ofParts_ne (by decide)]
        simp only [lsym_simp, ↓reduceIte]
        refine ⟨fun _ i hi => ?_, fun _ => by simp⟩
        rcases Nat.lt_or_ge i j with h | h
        · exact hbytes i h
        · obtain rfl : i = j := by omega
          rw [← hbyte, ← hbyte]; exact zeroExtend_byte_inj _ _ hb
      · simp [hmem]
      · exact hcode
      · by_cases h0 : r = .x0
        · subst h0; simp [getReg_x0]
        · rw [getReg_ofParts_ne h0]
          simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          obtain ⟨h10', h11', h12', h13, h14⟩ := hr
          simp [lsym_simp, h10', h11', h12', h13, h14, hkept r (by simp [clobbered, *]) h0]
      · rw [getReg_ofParts_ne (by decide)]
        simp [lsym_simp, signExtend12]

/-- **`memcmp`'s contract at Lprog**, as in `MemcmpLprog.contract`. -/
theorem contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (u0 : MachineState) (a b : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (regs : Reg → BitVec 64) (m : MachineState) (hag : Agree (ofParts regs m) u0)
    (h10 : u0.getReg .x10 = a) (h11 : u0.getReg .x11 = b) (h12 : u0.getReg .x12 = BitVec.ofNat 64 n)
    (hra : u0.getReg .x1 = ret) (hsp : u0.getReg .x2 = top)
    (hpost : ∀ r' m', Post u0 a b n (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩ := by
  -- the register file and the memory, from the machine state they agree with
  have hr : ∀ r, r ≠ .x0 → regs r = u0.getReg r := fun r h => by
    rw [← getReg_ofParts_ne h regs m]; exact hag.regs r
  have hmem : ∀ addr, m.getMem addr = u0.getMem addr := fun addr => hag.mem addr
  have hcode : m.code = u0.code := hag.code
  have r10 := hr .x10 (by decide); have r11 := hr .x11 (by decide)
  have r12 := hr .x12 (by decide); have r1 := hr .x1 (by decide); have r2 := hr .x2 (by decide)
  rw [h10] at r10; rw [h11] at r11; rw [h12] at r12; rw [hra] at r1; rw [hsp] at r2
  lsym hf stop [2] with [r10, r11, r12, r1, r2]
  · -- no bytes: the result is zero
    have hz : n = 0 := ofNat_eq_zero hn hc
    subst hz
    apply hpost
    refine ⟨?_, fun addr => ?_, ?_, fun r hr' => ?_, ?_⟩
    · rw [getReg_ofParts_ne (by decide)]; simp [lsym_simp]
    · simp [hmem]
    · exact hcode
    · by_cases h0 : r = .x0
      · subst h0; simp [getReg_x0]
      · rw [getReg_ofParts_ne h0]
        have h10' : r ≠ .x10 := fun h => hr' (by simp [clobbered, h])
        simp [lsym_simp, h10', hr r h0]
    · rw [getReg_ofParts_ne (by decide)]; simp [lsym_simp, signExtend12]
  · -- some bytes: the loop
    have hpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hc
      · exact h
    exact loop u0 a b n hn hva hvb hpost n 0 regs m (by omega) hpos (by simp [r10]) (by simp [r11])
      (by simp [r12]) r1 r2 hmem hcode (fun r _ h0 => hr r h0) (fun i hi => absurd hi (Nat.not_lt_zero i))

end Cases.Zip2005.MemcmpLsym
