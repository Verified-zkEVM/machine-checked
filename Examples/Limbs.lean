/-
  Examples.Limbs

  `add_limbs` of `Examples/src/c/limbs.c`, compiled by clang (`Examples/elf/limbs.elf`), for
  every length: its contract at Lprog, proved with `lsym`, and the same statement over
  riscv-zkvm's machine.

  `add_limbs(r, a, b, n)` adds two numbers of `n` 64-bit limbs, least significant first, and
  returns the carry out. The specification is over natural numbers: `limbsVal` is the number
  a list of limbs stands for, and after the call the limbs at `r` and the carry `c` satisfy
  `limbsVal out + c * 2^(64*n) = limbsVal as + limbsVal bs`, with `as` and `bs` the limbs at
  `a` and `b` on entry. The memory outside the `n` limbs at `r` is as it was.

  The arithmetic of one limb (`limb_step`) and what one iteration does to the invariant
  (`step_inv`) are lemmas of their own, apart from the stepped goal. The loop is a lemma at its
  head from an arbitrary limb, by induction on the limbs left.
-/

import Examples.Gen.Limbs
import Examples.Kit

namespace Examples.Limbs

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Gen.Limbs

theorem hok : ProgOk fns := by decide

/-! ## Numbers as limbs -/

/-- The number a list of 64-bit limbs stands for, least significant first. -/
def limbsVal : List Word → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 ^ 64 * limbsVal xs

/-- The `n` doublewords from address `p`. -/
def limbsAt (m : MachineState) (p : Word) (n : Nat) : List Word :=
  (List.range n).map fun i => m.getMem (p + BitVec.ofNat 64 (8 * i))

theorem limbsVal_append_singleton (xs : List Word) (x : Word) :
    limbsVal (xs ++ [x]) = limbsVal xs + 2 ^ (64 * xs.length) * x.toNat := by
  induction xs with
  | nil => simp [limbsVal]
  | cons y ys ih =>
    simp only [List.cons_append, limbsVal, ih, List.length_cons, Nat.mul_add, Nat.pow_add,
      Nat.mul_one]
    rw [Nat.mul_comm (2 ^ (64 * ys.length)) (2 ^ 64), Nat.mul_assoc]
    omega

theorem limbsAt_succ (m : MachineState) (p : Word) (j : Nat) :
    limbsAt m p (j + 1) = limbsAt m p j ++ [m.getMem (p + BitVec.ofNat 64 (8 * j))] := by
  simp [limbsAt, List.range_succ]

theorem length_limbsAt (m : MachineState) (p : Word) (j : Nat) : (limbsAt m p j).length = j := by
  simp [limbsAt]

/-! ## One limb -/

/-- The carry out of `A + B + c`, as the code computes it: either addition wrapped. -/
def carryOut (A B c : Word) : Word :=
  (if A + c < A then 1#64 else 0#64) ||| (if A + (c + B) < A + c then 1#64 else 0#64)

/-- **One limb's arithmetic.** With `s = A + c` and `t = s + B` modulo 2^64, and the carry out
    `(s < A) | (t < s)` (the code tests `s < A`, which for a carry in of 0 or 1 is the source's
    `s < c`), the carry out is 0 or 1 and `A + B + c = t + carry * 2^64` over the naturals. -/
theorem limb_step (A B c : Word) (hc : c = 0#64 ∨ c = 1#64) :
    (carryOut A B c = 0#64 ∨ carryOut A B c = 1#64) ∧
      A.toNat + B.toNat + c.toNat = (A + (c + B)).toNat + (carryOut A B c).toNat * 2 ^ 64 := by
  unfold carryOut
  by_cases h1 : A + c < A <;> by_cases h2 : A + (c + B) < A + c <;>
    simp only [h1, h2, ↓reduceIte, BitVec.or_zero, BitVec.zero_or, BitVec.or_self] <;>
    rcases hc with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> bv_omega

/-- The invariant's arithmetic over one limb, with `P = 2^(64*j)` and `W = 2^64`. -/
theorem nat_step (Vr Va Vb P W A B c t c' : Nat) (h1 : Vr + c * P = Va + Vb)
    (h2 : A + B + c = t + c' * W) : Vr + P * t + c' * (P * W) = Va + P * A + (Vb + P * B) := by
  have h := congrArg (P * ·) h2
  simp only [Nat.mul_add] at h
  rw [Nat.mul_comm c P] at h1
  rw [show c' * (P * W) = P * (c' * W) by ac_rfl]
  omega

/-! ## Addresses -/

theorem ofNat8_succ (j : Nat) :
    BitVec.ofNat 64 (8 * j) + 8#64 = BitVec.ofNat 64 (8 * (j + 1)) := by
  bv_omega

theorem ofNat8_inj {i j : Nat} (hi : 8 * i < 2 ^ 64) (hj : 8 * j < 2 ^ 64)
    (h : BitVec.ofNat 64 (8 * i) = BitVec.ofNat 64 (8 * j)) : i = j := by
  bv_omega

theorem add_ofNat8_inj (p : Word) {i j : Nat} (hi : 8 * i < 2 ^ 64) (hj : 8 * j < 2 ^ 64)
    (h : p + BitVec.ofNat 64 (8 * i) = p + BitVec.ofNat 64 (8 * j)) : i = j := by
  bv_omega

theorem shl3 (x : Word) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

/-! ## The loop -/

/-- **One iteration and the invariant.** With `j` limbs added, the carry `c` and the invariant
    over the memory `m`, storing limb `j` gives the invariant for `j + 1` limbs with the carry
    out, and changes no doubleword outside the limbs at `r`. -/
theorem step_inv (m0 m : MachineState) (r a b : Word) (n j : Nat) (c : Word) (hn : 8 * n < 2 ^ 64)
    (hj : j < n)
    (hda : ∀ i < n, ∀ k < n, r + BitVec.ofNat 64 (8 * i) ≠ a + BitVec.ofNat 64 (8 * k))
    (hdb : ∀ i < n, ∀ k < n, r + BitVec.ofNat 64 (8 * i) ≠ b + BitVec.ofNat 64 (8 * k))
    (hcar : c = 0#64 ∨ c = 1#64)
    (hinv : limbsVal (limbsAt m r j) + c.toNat * 2 ^ (64 * j) =
      limbsVal (limbsAt m0 a j) + limbsVal (limbsAt m0 b j))
    (hkept : ∀ x, (∀ i < j, x ≠ r + BitVec.ofNat 64 (8 * i)) → m.getMem x = m0.getMem x)
    (A B : Word) (hA : A = m.getMem (a + BitVec.ofNat 64 (8 * j)))
    (hB : B = m.getMem (b + BitVec.ofNat 64 (8 * j)))
    (m1 : MachineState) (hm1 : m1 = m.setMem (r + BitVec.ofNat 64 (8 * j)) (A + (c + B))) :
    (carryOut A B c = 0#64 ∨ carryOut A B c = 1#64) ∧
    limbsVal (limbsAt m1 r (j + 1)) + (carryOut A B c).toNat * 2 ^ (64 * (j + 1)) =
      limbsVal (limbsAt m0 a (j + 1)) + limbsVal (limbsAt m0 b (j + 1)) ∧
    (∀ x, (∀ i < j + 1, x ≠ r + BitVec.ofNat 64 (8 * i)) → m1.getMem x = m0.getMem x) := by
  obtain ⟨hc', hstep⟩ := limb_step A B c hcar
  have hA0 : m0.getMem (a + BitVec.ofNat 64 (8 * j)) = A := by
    rw [hA]; exact (hkept _ fun i hi => (hda i (by omega) j hj).symm).symm
  have hB0 : m0.getMem (b + BitVec.ofNat 64 (8 * j)) = B := by
    rw [hB]; exact (hkept _ fun i hi => (hdb i (by omega) j hj).symm).symm
  have hsame : limbsAt m1 r j = limbsAt m r j := by
    simp only [limbsAt]
    apply List.map_congr_left
    intro i hi
    have hi' : i < j := List.mem_range.mp hi
    have hne : r + BitVec.ofNat 64 (8 * i) ≠ r + BitVec.ofNat 64 (8 * j) := fun h => by
      have := add_ofNat8_inj r (by omega) (by omega) h; omega
    rw [hm1, getMem_setMem]; simp only [hne, ↓reduceIte]
  have hnew : m1.getMem (r + BitVec.ofNat 64 (8 * j)) = A + (c + B) := by
    rw [hm1, getMem_setMem]; simp only [↓reduceIte]
  refine ⟨hc', ?_, fun x hx => ?_⟩
  · rw [limbsAt_succ, limbsAt_succ, limbsAt_succ, limbsVal_append_singleton,
      limbsVal_append_singleton, limbsVal_append_singleton, length_limbsAt, length_limbsAt,
      length_limbsAt, hsame, hnew, hA0, hB0, show 64 * (j + 1) = 64 * j + 64 by omega, Nat.pow_add]
    exact nat_step _ _ _ _ _ _ _ _ _ _ hinv hstep
  · rw [hm1, getMem_setMem]; simp only [hx j (by omega), ↓reduceIte]
    exact hkept x fun i hi => hx i (by omega)

/-- What `add_limbs(r, a, b, n)` leaves in the register file `r'` and the memory `m'`, from the
    memory `m`. -/
def Added (m : MachineState) (r a b : Word) (n : Nat) (r' : Reg → BitVec 64) (m' : MachineState) :
    Prop :=
  (r' .x10 = 0#64 ∨ r' .x10 = 1#64) ∧
  limbsVal (limbsAt m' r n) + (r' .x10).toNat * 2 ^ (64 * n) =
    limbsVal (limbsAt m a n) + limbsVal (limbsAt m b n) ∧
  (∀ x, (∀ i < n, x ≠ r + BitVec.ofNat 64 (8 * i)) → m'.getMem x = m.getMem x) ∧
  m'.code = m.code

/-- **The limb loop**, at its head with `j < n` limbs added and the carry `c`, on the register
    file. -/
theorem add_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m0 : MachineState) (r a b : Word) (n : Nat) (hn : 8 * n < 2 ^ 64)
    (hva : ∀ i < n, isValidDwordAccessSp1 (a + BitVec.ofNat 64 (8 * i)) = true)
    (hvb : ∀ i < n, isValidDwordAccessSp1 (b + BitVec.ofNat 64 (8 * i)) = true)
    (hvr : ∀ i < n, isValidDwordAccessSp1 (r + BitVec.ofNat 64 (8 * i)) = true ∧
      noCodeAt m0 (r + BitVec.ofNat 64 (8 * i)) 8 = true)
    (hda : ∀ i < n, ∀ k < n, r + BitVec.ofNat 64 (8 * i) ≠ a + BitVec.ofNat 64 (8 * k))
    (hdb : ∀ i < n, ∀ k < n, r + BitVec.ofNat 64 (8 * i) ≠ b + BitVec.ofNat 64 (8 * k))
    (hpost : ∀ r' m', Added m0 r a b n r' m' →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨rest, r', m'⟩) :
    ∀ k j (regs : Reg → BitVec 64) (m : MachineState) (c : Word), n - j = k → j < n →
      regs .x10 = r + BitVec.ofNat 64 (8 * j) → regs .x11 = a + BitVec.ofNat 64 (8 * j) →
      regs .x12 = b + BitVec.ofNat 64 (8 * j) → regs .x13 = r + BitVec.ofNat 64 (8 * n) →
      regs .x14 = c → regs .x1 = ret → regs .x2 = top → m.code = m0.code →
      (c = 0#64 ∨ c = 1#64) →
      limbsVal (limbsAt m r j) + c.toNat * 2 ^ (64 * j) =
        limbsVal (limbsAt m0 a j) + limbsVal (limbsAt m0 b j) →
      (∀ x, (∀ i < j, x ≠ r + BitVec.ofNat 64 (8 * i)) → m.getMem x = m0.getMem x) →
      rvIsa.SafeN (liftProg fns) sp1Ctx G N Q ⟨⟨0, 8, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ _ _ hk hj; omega
  | succ k ih =>
    intro j regs m c hk hj h10 h11 h12 h13 h14 hra hsp hcode hcar hinv hkept
    have hnc : noCodeAt m (r + BitVec.ofNat 64 (8 * j)) 8 = true := by
      rw [← (hvr j hj).2]; simp [noCodeAt, hcode]
    obtain ⟨hcar', hinv', hkept'⟩ := step_inv m0 m r a b n j c hn hj hda hdb hcar hinv hkept
      _ _ rfl rfl _ rfl
    lsym f0_eq stop [8] with [h10, h11, h12, h13, h14, hra, hsp, hva j hj, hvb j hj, (hvr j hj).1, hnc]
    · -- the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · obtain rfl : n = j + 1 := by omega
          exact absurd (ofNat8_succ j) hc
      apply ih (j + 1) _ _ _ (by omega) hlt
      · simp [lsym_simp, ofNat8_succ]
      · simp [lsym_simp, ofNat8_succ]
      · simp [lsym_simp, ofNat8_succ]
      · simp [lsym_simp, h13]
      · simp only [lsym_simp]; rfl
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · simpa using hcode
      · exact hcar'
      · exact hinv'
      · exact hkept'
    · -- the exit: every limb is added
      have hjn : j + 1 = n := by
        rw [ofNat8_succ] at hc
        exact ofNat8_inj (by omega) hn hc
      subst hjn
      apply hpost
      refine ⟨?_, ?_, hkept', by simpa using hcode⟩
      · simpa [lsym_simp, carryOut] using hcar'
      · simpa [lsym_simp, carryOut] using hinv'

/-- **`add_limbs(r, a, b, n)`**: the `n` limbs at `r` and the carry returned are the sum of the
    numbers at `a` and at `b`; no doubleword outside the limbs at `r` changes. The three regions
    are valid doublewords, `r`'s not code, `8 * n` does not wrap, and `r` is disjoint from both
    `a` and `b` (more than the source needs: it would also allow `r = a` or `r = b`). -/
theorem add_limbs_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧
      8 * (regs .x13).toNat < 2 ^ 64 ∧
      (∀ i < (regs .x13).toNat,
        isValidDwordAccessSp1 (regs .x11 + BitVec.ofNat 64 (8 * i)) = true) ∧
      (∀ i < (regs .x13).toNat,
        isValidDwordAccessSp1 (regs .x12 + BitVec.ofNat 64 (8 * i)) = true) ∧
      (∀ i < (regs .x13).toNat,
        isValidDwordAccessSp1 (regs .x10 + BitVec.ofNat 64 (8 * i)) = true ∧
          noCodeAt m (regs .x10 + BitVec.ofNat 64 (8 * i)) 8 = true) ∧
      (∀ i < (regs .x13).toNat, ∀ k < (regs .x13).toNat,
        regs .x10 + BitVec.ofNat 64 (8 * i) ≠ regs .x11 + BitVec.ofNat 64 (8 * k)) ∧
      (∀ i < (regs .x13).toNat, ∀ k < (regs .x13).toNat,
        regs .x10 + BitVec.ofNat 64 (8 * i) ≠ regs .x12 + BitVec.ofNat 64 (8 * k)))
    (fun _ _ regs m r' m' =>
      Added m (regs .x10) (regs .x11) (regs .x12) (regs .x13).toNat r' m') := by
  intro G N Q ret top rest regs m ⟨hra, hsp, hn, hva, hvb, hvr, hda, hdb⟩ hk
  lsym f0_eq stop [8] with [hra, hsp]
  · -- no limbs
    apply hk
    exact ⟨by simp [lsym_simp], by simp [lsym_simp, limbsAt, limbsVal, hc], fun _ _ => rfl, rfl⟩
  · -- some limbs: the loop
    have hpos : 0 < (regs .x13).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x13).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hc
      · exact h
    exact add_loop m (regs .x10) (regs .x11) (regs .x12) _ hn hva hvb hvr hda hdb hk _ 0 _ m 0#64
      rfl hpos (by simp [lsym_simp]) (by simp [lsym_simp]) (by simp [lsym_simp])
      (by simp [lsym_simp, shl3]) (by simp [lsym_simp]) (by simp [lsym_simp, hra])
      (by simp [lsym_simp, hsp]) rfl (Or.inl rfl) (by simp [limbsAt, limbsVal]) (fun _ _ => rfl)

/-- **`add_limbs` on the machine.** -/
theorem add_limbs_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s)
    (hn : 8 * (s.getReg .x13).toNat < 2 ^ 64)
    (hva : ∀ i < (s.getReg .x13).toNat,
      isValidDwordAccessSp1 (s.getReg .x11 + BitVec.ofNat 64 (8 * i)) = true)
    (hvb : ∀ i < (s.getReg .x13).toNat,
      isValidDwordAccessSp1 (s.getReg .x12 + BitVec.ofNat 64 (8 * i)) = true)
    (hvr : ∀ i < (s.getReg .x13).toNat,
      isValidDwordAccessSp1 (s.getReg .x10 + BitVec.ofNat 64 (8 * i)) = true ∧
        noCodeAt s (s.getReg .x10 + BitVec.ofNat 64 (8 * i)) 8 = true)
    (hda : ∀ i < (s.getReg .x13).toNat, ∀ j < (s.getReg .x13).toNat,
      s.getReg .x10 + BitVec.ofNat 64 (8 * i) ≠ s.getReg .x11 + BitVec.ofNat 64 (8 * j))
    (hdb : ∀ i < (s.getReg .x13).toNat, ∀ j < (s.getReg .x13).toNat,
      s.getReg .x10 + BitVec.ofNat 64 (8 * i) ≠ s.getReg .x12 + BitVec.ofNat 64 (8 * j))
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      (t.getReg .x10 = 0#64 ∨ t.getReg .x10 = 1#64) →
      limbsVal (limbsAt t (s.getReg .x10) (s.getReg .x13).toNat) +
          (t.getReg .x10).toNat * 2 ^ (64 * (s.getReg .x13).toNat) =
        limbsVal (limbsAt s (s.getReg .x11) (s.getReg .x13).toNat) +
          limbsVal (limbsAt s (s.getReg .x12) (s.getReg .x13).toNat) →
      (∀ x, (∀ i < (s.getReg .x13).toNat, x ≠ s.getReg .x10 + BitVec.ofNat 64 (8 * i)) →
        t.getMem x = s.getMem x) →
      SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode add_limbs_contract
    ⟨rfl, rfl, hn, hva, hvb, hvr, hda, hdb⟩ ?_
  rintro t r' m' hag hpc' ⟨hbit, hsum, hkept, -⟩
  have h10 : t.getReg .x10 = r' .x10 := by rw [← hag.regs, getReg_ofParts]; simp
  have hlimbs : ∀ p n, limbsAt t p n = limbsAt m' p n := fun p n => by
    simp only [limbsAt, ← hag.mem, getMem_ofParts]
  refine hk t hpc' (h10 ▸ hbit) ?_ fun x hx => ?_
  · rw [h10, hlimbs]; exact hsum
  · rw [← hag.mem]; exact hkept x hx

end Examples.Limbs
