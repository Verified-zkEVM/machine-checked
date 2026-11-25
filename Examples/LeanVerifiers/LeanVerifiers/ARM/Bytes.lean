/-
  LeanVerifiers.ARM.Bytes

  Reads and writes of the byte memory (`Isa.lean`), byte by byte: what a byte is after a
  little-endian store, and what a little-endian load reads; and the arithmetic on addresses
  that the loops use. Addresses are `base + i` modulo 2^64.
-/

import LeanVerifiers.ARM.Isa

namespace LeanVerifiers.ARM

/-- `j + 1`, as addresses count it. -/
theorem ofNat_succ (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem add_ofNat_inj (a : BitVec 64) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 j) : i = j := by
  bv_omega

theorem ofNat_inj {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : BitVec.ofNat 64 i = BitVec.ofNat 64 j) : i = j := by
  bv_omega

theorem add_ofNat_succ (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 (i + 1) = a + 1 + BitVec.ofNat 64 i := by
  rw [← ofNat_succ, BitVec.add_comm (BitVec.ofNat 64 i), BitVec.add_assoc]; rfl

/-- **A byte outside a store** is kept. -/
theorem storeLE_of_ne (m : Bytes) (a v x : BitVec 64) (n : Nat)
    (h : ∀ i < n, x ≠ a + BitVec.ofNat 64 i) : storeLE m a v n x = m x := by
  induction n generalizing m a v with
  | zero => rfl
  | succ n ih =>
    rw [storeLE, ih]
    · have := h 0 (by omega)
      simp only [BitVec.add_zero] at this
      simp [this]
    · intro i hi
      have := h (i + 1) (by omega)
      rwa [add_ofNat_succ] at this

/-- **A byte of a store**: byte `i` of the value. -/
theorem storeLE_add (m : Bytes) (a v : BitVec 64) (n i : Nat) (hi : i < n) (hn : n ≤ 2 ^ 64) :
    storeLE m a v n (a + BitVec.ofNat 64 i) = (v >>> (8 * i)).truncate 8 := by
  induction n generalizing m a v i with
  | zero => omega
  | succ n ih =>
    rw [storeLE]
    cases i with
    | zero =>
      rw [storeLE_of_ne]
      · simp
      · intro k hk; bv_omega
    | succ i =>
      rw [add_ofNat_succ, ih _ _ _ i (by omega) (by omega), ← BitVec.shiftRight_add,
        show 8 + 8 * i = 8 * (i + 1) by omega]

/-- **A byte of a load**: the byte at that address. -/
theorem loadLE_byte (m : Bytes) (a : BitVec 64) (n i : Nat) (hi : i < n) (hn : n ≤ 8) :
    (loadLE m a n >>> (8 * i)).truncate 8 = m (a + BitVec.ofNat 64 i) := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    rw [loadLE]
    cases i with
    | zero => simp only [Nat.mul_zero, BitVec.ushiftRight_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero]; generalize m a = b; generalize loadLE m (a + 1) n = w; bv_decide
    | succ i =>
      rw [add_ofNat_succ, ← ih _ i (by omega) (by omega)]
      generalize m a = b; generalize loadLE m (a + 1) n = w
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      all_goals bv_decide

theorem ofNat_eq_zero {x : Nat} (hx : x < 2 ^ 64) (h : BitVec.ofNat 64 x = 0#64) : x = 0 := by
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this

theorem ofNat_add_neg_one {x : Nat} (h : 0 < x) :
    BitVec.ofNat 64 x + 18446744073709551615#64 = BitVec.ofNat 64 (x - 1) := by
  bv_omega

theorem add_ofNat_add (a : BitVec 64) (i j : Nat) :
    a + BitVec.ofNat 64 (i + j) = a + BitVec.ofNat 64 i + BitVec.ofNat 64 j := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp

/-- The `n` bytes at `dst` are those that were at `src`, and no other byte has changed. -/
def Copied (m0 : Bytes) (dst src : BitVec 64) (n : Nat) (m' : Bytes) : Prop :=
  (∀ i < n, m' (dst + BitVec.ofNat 64 i) = m0 (src + BitVec.ofNat 64 i)) ∧
    ∀ x, (∀ i < n, x ≠ dst + BitVec.ofNat 64 i) → m' x = m0 x

/-- **One step of a copy**: with `j` bytes copied, loading `w` bytes at `src + j` and storing
    them at `dst + j` leaves `j + w` bytes copied. No address is in both regions. -/
theorem Copied.step {m0 m : Bytes} {dst src : BitVec 64} {n j : Nat} (w : Nat) (hw : w ≤ 8)
    (hjw : j + w ≤ n) (hn : n < 2 ^ 64)
    (hdis : ∀ i < n, ∀ j < n, dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (h : Copied m0 dst src j m) :
    Copied m0 dst src (j + w)
      (storeLE m (dst + BitVec.ofNat 64 j) (loadLE m (src + BitVec.ofNat 64 j) w) w) := by
  obtain ⟨hdone, hkept⟩ := h
  constructor
  · intro i hi
    rcases Nat.lt_or_ge i j with h | h
    · rw [storeLE_of_ne, hdone i h]
      intro t ht h'
      rw [← add_ofNat_add] at h'
      have := add_ofNat_inj dst (by omega) (by omega) h'; omega
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_ofNat_add, storeLE_add _ _ _ _ _ (by omega) (by omega),
        loadLE_byte _ _ _ _ (by omega) hw, ← add_ofNat_add]
      exact hkept _ fun i hi => (hdis i (by omega) (j + t) (by omega)).symm
  · intro x hx
    rw [storeLE_of_ne]
    · exact hkept x fun i hi => hx i (by omega)
    · intro t ht; rw [← add_ofNat_add]; exact hx _ (by omega)

/-! ## Words -/

/-- A load reads the bytes at its address only. -/
theorem loadLE_congr {m m' : Bytes} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (a + BitVec.ofNat 64 i)) :
    loadLE m a n = loadLE m' a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [loadLE, loadLE, h0,
      ih fun i hi => by have := h (i + 1) (by omega); rwa [add_ofNat_succ] at this]

/-- **A word read where it was written.** -/
theorem loadLE_storeLE_same (m : Bytes) (a v : BitVec 64) : loadLE (storeLE m a v 8) a 8 = v := by
  have h : ∀ i < 8, (loadLE (storeLE m a v 8) a 8 >>> (8 * i)).truncate 8 =
      (v >>> (8 * i)).truncate 8 := fun i hi => by
    rw [loadLE_byte _ _ _ _ hi (by omega), storeLE_add _ _ _ _ _ hi (by omega)]
  generalize loadLE (storeLE m a v 8) a 8 = w at h
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega); have h4 := h 4 (by omega); have h5 := h 5 (by omega)
  have h6 := h 6 (by omega); have h7 := h 7 (by omega)
  clear h
  bv_decide

/-- **A word read apart from a word written**: the two do not overlap. -/
theorem loadLE_storeLE_apart (m : Bytes) (a b v : BitVec 64) (h1 : 8#64 ≤ b - a)
    (h2 : b - a ≤ 0xFFFFFFFFFFFFFFF8#64) : loadLE (storeLE m a v 8) b 8 = loadLE m b 8 := by
  refine loadLE_congr fun i hi => storeLE_of_ne _ _ _ _ _ fun t ht => ?_
  bv_omega

/-- Two words at offsets from one base. -/
theorem loadLE_storeLE_off (m : Bytes) (p a b v : BitVec 64) (h1 : 8#64 ≤ b - a)
    (h2 : b - a ≤ 0xFFFFFFFFFFFFFFF8#64) :
    loadLE (storeLE m (p + a) v 8) (p + b) 8 = loadLE m (p + b) 8 :=
  loadLE_storeLE_apart _ _ _ _ (by bv_omega) (by bv_omega)

theorem loadLE_storeLE_off0 (m : Bytes) (p b v : BitVec 64) (h1 : 8#64 ≤ b)
    (h2 : b ≤ 0xFFFFFFFFFFFFFFF8#64) : loadLE (storeLE m p v 8) (p + b) 8 = loadLE m (p + b) 8 :=
  loadLE_storeLE_apart _ _ _ _ (by bv_omega) (by bv_omega)

theorem loadLE_storeLE_0off (m : Bytes) (p a v : BitVec 64) (h1 : 8#64 ≤ a)
    (h2 : a ≤ 0xFFFFFFFFFFFFFFF8#64) : loadLE (storeLE m (p + a) v 8) p 8 = loadLE m p 8 :=
  loadLE_storeLE_apart _ _ _ _ (by bv_omega) (by bv_omega)

/-- The 8 bytes at `q` are outside the `n` bytes at `p`. -/
def Out (p : BitVec 64) (n : Nat) (q : BitVec 64) : Prop :=
  n ≤ (q - p).toNat ∧ (q - p).toNat ≤ 2 ^ 64 - 8

/-- A word outside a region, read after a word written inside it. -/
theorem loadLE_storeLE_out {p q : BitVec 64} {n : Nat} (hq : Out p n q) (m : Bytes)
    (a v : BitVec 64) (ha : a.toNat + 8 ≤ n) :
    loadLE (storeLE m (p + a) v 8) q 8 = loadLE m q 8 := by
  obtain ⟨h1, h2⟩ := hq
  exact loadLE_storeLE_apart _ _ _ _ (by bv_omega) (by bv_omega)

/-- A word inside a region, read after a word written outside it. -/
theorem loadLE_storeLE_in {p q : BitVec 64} {n : Nat} (hq : Out p n q) (m : Bytes)
    (a v : BitVec 64) (ha : a.toNat + 8 ≤ n) :
    loadLE (storeLE m q v 8) (p + a) 8 = loadLE m (p + a) 8 := by
  obtain ⟨h1, h2⟩ := hq
  exact loadLE_storeLE_apart _ _ _ _ (by bv_omega) (by bv_omega)

/-- A byte outside a region is kept by a word written inside it. -/
theorem storeLE_out {p x : BitVec 64} {n : Nat} (hx : n ≤ (x - p).toNat) (m : Bytes)
    (a v : BitVec 64) (ha : a.toNat + 8 ≤ n) : storeLE m (p + a) v 8 x = m x :=
  storeLE_of_ne _ _ _ _ _ fun t ht => by bv_omega

theorem storeLE_out0 {p x : BitVec 64} {n : Nat} (hx : n ≤ (x - p).toNat) (m : Bytes)
    (v : BitVec 64) (hn : 8 ≤ n) : storeLE m p v 8 x = m x :=
  storeLE_of_ne _ _ _ _ _ fun t ht => by bv_omega

end LeanVerifiers.ARM
