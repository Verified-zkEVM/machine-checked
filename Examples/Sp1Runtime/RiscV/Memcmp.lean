/-
  Examples.Sp1Runtime.RiscV.Memcmp

  `memcmp(a, b, n)`, for every length `n`: its contract at Lprog (`memcmp_contract`), proved
  with `lsym`, and the same statement over riscv-zkvm's machine (`memcmp_correct`), through
  `SafeN.of_contract`.

  The function is `Examples/src/c/memcmp.c`, compiled by clang: twelve instructions, the ones rustc's
  `compiler_builtins` has for `memcmp` in an SP1 guest, with two of the increments in another
  order. `lsym` steps the body, computes each operation, and closes the memory checks of the
  loads and the conditions of the returns; what is left is what the function means: the loop's
  invariant at its head, and the postcondition at each return.

  The loop is stated on Lprog's register file, not on a machine state that agrees with it:
  `lsym` computes registers as `updReg`, so their values are read off by `simp`.
-/

import Examples.Sp1Runtime.RiscV.MemcmpImage
import Examples.Kit
import MachineChecked.RiscV.Lift.Rules
import LprogRiscV.Lsym

namespace Examples.Sp1Runtime.RiscV.Memcmp

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Sp1Runtime.RiscV.MemcmpImage

theorem sext32_sub_bytes (x y : BitVec 8) :
    BitVec.signExtend 64 ((BitVec.zeroExtend 64 x + -BitVec.zeroExtend 64 y).truncate 32) =
      BitVec.zeroExtend 64 x + -BitVec.zeroExtend 64 y := by
  rw [← BitVec.sub_eq_add_neg]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · have e : (2 ^ 64 - y.toNat % 2 ^ 64 + x.toNat % 2 ^ 64) % 2 ^ 64 = x.toNat - y.toNat := by omega
    simp only [e, decide_eq_true_eq]
    split <;> omega
  · have e : (2 ^ 64 - y.toNat % 2 ^ 64 + x.toNat % 2 ^ 64) % 2 ^ 64 =
        2 ^ 64 - (y.toNat - x.toNat) := by omega
    simp only [e, decide_eq_true_eq]
    split <;> omega

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-- The registers `memcmp` may change. -/
def clobbered : List Reg := [.x10, .x11, .x12, .x13, .x14]

/-- What `memcmp` leaves behind from a machine state `u0`, in a machine state `v` it returns in. -/
def Post (u0 : MachineState) (a b : Word) (n : Nat) (v : MachineState) : Prop :=
  (v.getReg .x10 = 0 ↔
    ∀ i < n, u0.getByte (a + BitVec.ofNat 64 i) = u0.getByte (b + BitVec.ofNat 64 i)) ∧
  (∀ addr, v.getMem addr = u0.getMem addr) ∧ v.code = u0.code ∧
  (∀ r, r ∉ clobbered → v.getReg r = u0.getReg r) ∧
  BitVec.signExtend 64 ((v.getReg .x10).truncate 32) = v.getReg .x10

/-- A register other than `x0`, read from a machine state built from a register file. -/
theorem getReg_ofParts_ne {r : Reg} (h : r ≠ .x0) (regs : Reg → BitVec 64) (m : MachineState) :
    (ofParts regs m).getReg r = regs r := by
  rw [getReg_ofParts]; simp [h]

/-- **The byte loop**, from byte `j < n`, at the loop head, on the register file. -/
theorem loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (u0 : MachineState) (a b : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (hpost : ∀ r' m', Post u0 a b n (ofParts r' m') → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : MachineState), n - j = k → j < n →
      regs .x10 = a + BitVec.ofNat 64 j → regs .x11 = b + BitVec.ofNat 64 j →
      regs .x12 = BitVec.ofNat 64 (n - j) → regs .x1 = ret → regs .x2 = top →
      (∀ addr, m.getMem addr = u0.getMem addr) → m.code = u0.code →
      (∀ r, r ∉ clobbered → r ≠ .x0 → regs r = u0.getReg r) →
      (∀ i < j, u0.getByte (a + BitVec.ofNat 64 i) = u0.getByte (b + BitVec.ofNat 64 i)) →
      LSafeN fns G N Q ⟨⟨0, 2, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ hk hj; omega
  | succ k ih =>
    intro j regs m hk hj h10 h11 h12 hra hsp hmem hcode hkept hbytes
    have hbyte : ∀ x, m.getByte x = u0.getByte x := fun x => by simp [MachineState.getByte, hmem]
    lsym f0_eq stop [2] with [h10, h11, h12, hra, hsp, hva j hj, hvb j hj]
    · -- the bytes differ: the result is their difference
      apply hpost
      refine ⟨?_, fun addr => ?_, ?_, fun r hr => ?_, ?_⟩
      · simp [getReg_ofParts_ne (show Reg.x10 ≠ .x0 by decide), lsym_simp, hbyte] at hc ⊢
        constructor
        · intro h; exact absurd (by bv_omega) hc
        · intro h; exact absurd (congrArg _ (h j hj)) hc
      · simp [hmem]
      · exact hcode
      · exact frame_ofParts hkept (by lframe [clobbered]) _ r hr
      · rw [getReg_ofParts_ne (by decide)]
        simp only [lsym_simp, hbyte, ↓reduceIte]
        exact sext32_sub_bytes _ _
    · -- the bytes agree and some are left: the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | hge
        · exact h
        · rw [ofNat_add_neg_one (by omega), show n - j - 1 = 0 by omega] at hc; exact absurd rfl hc
      apply ih (j + 1) _ m (by omega) hlt
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, ofNat_add_neg_one (show 0 < n - j by omega), show n - j - 1 = n - (j + 1) by omega]
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · exact hmem
      · exact hcode
      · intro r hr h0
        rw [← hkept r hr h0]
        revert r; lframe [clobbered]
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact hbytes i h
        · rw [← hbyte, ← hbyte]; exact zeroExtend_byte_inj _ _ hc_1
    · -- the bytes agree and none are left: the blocks are equal
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
          rw [← hbyte, ← hbyte]; exact zeroExtend_byte_inj _ _ hc_1
      · simp [hmem]
      · exact hcode
      · exact frame_ofParts hkept (by lframe [clobbered]) _ r hr
      · rw [getReg_ofParts_ne (by decide)]
        simp [lsym_simp]

/-- **`memcmp`'s contract at Lprog**. -/
theorem memcmp_contract {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (u0 : MachineState) (a b : Word) (n : Nat) (hn : n < 2 ^ 64)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (regs : Reg → BitVec 64) (m : MachineState) (hag : Agree (ofParts regs m) u0)
    (h10 : u0.getReg .x10 = a) (h11 : u0.getReg .x11 = b) (h12 : u0.getReg .x12 = BitVec.ofNat 64 n)
    (hra : u0.getReg .x1 = ret) (hsp : u0.getReg .x2 = top)
    (hpost : ∀ r' m', Post u0 a b n (ofParts r' m') → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩ := by
  -- the register file and the memory, from the machine state they agree with
  have hr : ∀ r, r ≠ .x0 → regs r = u0.getReg r := fun r h => by
    rw [← getReg_ofParts_ne h regs m]; exact hag.regs r
  have hmem : ∀ addr, m.getMem addr = u0.getMem addr := fun addr => hag.mem addr
  have hcode : m.code = u0.code := hag.code
  have r10 := hr .x10 (by decide); have r11 := hr .x11 (by decide)
  have r12 := hr .x12 (by decide); have r1 := hr .x1 (by decide); have r2 := hr .x2 (by decide)
  rw [h10] at r10; rw [h11] at r11; rw [h12] at r12; rw [hra] at r1; rw [hsp] at r2
  lsym f0_eq stop [2] with [r10, r11, r12, r1, r2]
  · -- no bytes: the result is zero
    have hz : n = 0 := ofNat_eq_zero hn hc
    subst hz
    apply hpost
    refine ⟨?_, fun addr => ?_, ?_, fun r hr' => ?_, ?_⟩
    · rw [getReg_ofParts_ne (by decide)]; simp [lsym_simp]
    · simp [hmem]
    · exact hcode
    · exact frame_ofParts (fun r _ h0 => hr r h0) (by lframe [clobbered]) _ r hr'
    · rw [getReg_ofParts_ne (by decide)]; simp [lsym_simp]
  · -- some bytes: the loop
    have hpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hc
      · exact h
    exact loop u0 a b n hn hva hvb hpost n 0 regs m (by omega) hpos (by simp [r10]) (by simp [r11])
      (by simp [r12]) r1 r2 hmem hcode (fun r _ h0 => hr r h0) (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- **`memcmp(a, b, n)` over `stepSp1`**, for every length: it returns to `ra` with zero in `x10`
    exactly when the `n` bytes at `a` and at `b` agree (and sign-extended from 32 bits, as an
    `int`), memory and code untouched, and every register but `x10`..`x14` as it was. -/
theorem memcmp_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (ra a b : Word)
    (n : Nat) (hn : n < 2 ^ 64)
    (hpc : s.pc = 0x1000#64) (hcode : ∀ f ∈ fns, CodeAt f.base (f.prog.map some) s)
    (hra : s.getReg .x1 = ra) (h10 : s.getReg .x10 = a) (h11 : s.getReg .x11 = b)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n)
    (hva : ∀ i < n, isValidMemAddrSp1 (a + BitVec.ofNat 64 i) = true)
    (hvb : ∀ i < n, isValidMemAddrSp1 (b + BitVec.ofNat 64 i) = true)
    (hk : ∀ t, t.pc = ra &&& ~~~1#64 → t.code = s.code → (∀ addr, t.getMem addr = s.getMem addr) →
      (∀ r, r ∉ clobbered → t.getReg r = s.getReg r) →
      (t.getReg .x10 = 0 ↔
        ∀ i < n, s.getByte (a + BitVec.ofNat 64 i) = s.getByte (b + BitVec.ofNat 64 i)) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 →
      SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x1000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_contract hok (g := 0) hg (hpc.trans hb.symm) hcode
    (Post := Post s a b n)
    (fun _ _ hk => memcmp_contract s a b n hn hva hvb _ _ (agree_ofParts_regsOf s) h10 h11 h12
      rfl rfl hk) ?_
  intro t r' m' hag hpc' ⟨hx10, hmem, hcode', hkept, hsx⟩
  apply hk
  · rw [hpc', hra]
  · rw [← hag.code]; exact hcode'
  · intro addr; rw [← hag.mem addr]; exact hmem addr
  · intro r hr; rw [← hag.regs r]; exact hkept r hr
  · rw [← hag.regs]; exact hx10
  · rw [← hag.regs]; exact hsx

end Examples.Sp1Runtime.RiscV.Memcmp
