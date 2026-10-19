/-
  MachineChecked.RiscV.Sym.Region

  Memory as named, 8-aligned regions.

  A `Region base vs s` says the `vs.length` doublewords starting at `base` hold
  `vs`, in order. The symbolic executor keeps one such fact per region the
  code touches -- the stack frame, each buffer a pointer argument names, each
  global it reads or writes -- and a store becomes one `Region.set` step on the
  region it lands in plus one `Region.frame` step on every other region. That
  is O(#regions) per store, where a flat list of stores would cost O(#stores)
  disequalities per load.

  Everything is stated over `MachineState.getMem` at `base + 8 i`, so the
  bookkeeping about which doubleword an address selects is done once here, in
  `Nat`, and the executor only has to name the index.
-/

import MachineChecked.RiscV.Sym.Exec

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

/-- `vs.length` doublewords at `base`. -/
def Region (base : Word) (vs : List Word) (s : MachineState) : Prop :=
  ∀ i : Nat, i < vs.length → s.getMem (base + BitVec.ofNat 64 (8 * i)) = vs[i]!

/-- Two regions do not overlap, as a `Nat` fact about their extents. Neither
    wraps around the address space. -/
def Disjoint (b₁ : Word) (n₁ : Nat) (b₂ : Word) (n₂ : Nat) : Prop :=
  (b₁.toNat + 8 * n₁ ≤ b₂.toNat ∨ b₂.toNat + 8 * n₂ ≤ b₁.toNat)
    ∧ b₁.toNat + 8 * n₁ ≤ 2 ^ 64 ∧ b₂.toNat + 8 * n₂ ≤ 2 ^ 64

theorem Disjoint.symm {b₁ : Word} {n₁ : Nat} {b₂ : Word} {n₂ : Nat}
    (h : Disjoint b₁ n₁ b₂ n₂) : Disjoint b₂ n₂ b₁ n₁ :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- Two blocks inside one block that does not wrap, at literal offsets that do not overlap. -/
theorem Disjoint.within {B : Word} {N : Nat} (hnw : B.toNat + 8 * N ≤ 2 ^ 64) {a b : Word}
    {i m j n : Nat} (ha : a = B + BitVec.ofNat 64 (8 * i)) (hb : b = B + BitVec.ofNat 64 (8 * j))
    (him : i + m ≤ N) (hjn : j + n ≤ N) (hsep : i + m ≤ j ∨ j + n ≤ i) : Disjoint a m b n := by
  subst ha hb
  unfold Disjoint
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Sub-blocks of disjoint regions are disjoint: `[a, a + 8 m) ⊆ [b₁, b₁ + 8 n₁)` and
    `[b, b + 8 n) ⊆ [b₂, b₂ + 8 n₂)`. -/
theorem Disjoint.of_sub {b₁ : Word} {n₁ : Nat} {b₂ : Word} {n₂ : Nat} (h : Disjoint b₁ n₁ b₂ n₂)
    {a : Word} {i m : Nat} (ha : a = b₁ + BitVec.ofNat 64 (8 * i)) (him : i + m ≤ n₁)
    {b : Word} {j n : Nat} (hb : b = b₂ + BitVec.ofNat 64 (8 * j)) (hjn : j + n ≤ n₂) :
    Disjoint a m b n := by
  subst ha hb
  unfold Disjoint at *
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `base + 8 i` as a `Nat`, when the region does not wrap. -/
theorem toNat_addr {base : Word} {i n : Nat} (hi : i < n) (hnw : base.toNat + 8 * n ≤ 2 ^ 64) :
    (base + BitVec.ofNat 64 (8 * i)).toNat = base.toNat + 8 * i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- Cells of disjoint regions have different addresses. -/
theorem addr_ne_of_disjoint {b₁ : Word} {n₁ : Nat} {b₂ : Word} {n₂ : Nat}
    (h : Disjoint b₁ n₁ b₂ n₂) {i j : Nat} (hi : i < n₁) (hj : j < n₂) :
    b₁ + BitVec.ofNat 64 (8 * i) ≠ b₂ + BitVec.ofNat 64 (8 * j) := by
  intro heq
  have := congrArg BitVec.toNat heq
  rw [toNat_addr hi h.2.1, toNat_addr hj h.2.2] at this
  rcases h.1 with h1 | h1 <;> omega

/-- Cells of one region have different addresses at different indices. -/
theorem addr_ne_of_ne {base : Word} {n i j : Nat} (hi : i < n) (hj : j < n)
    (hnw : base.toNat + 8 * n ≤ 2 ^ 64) (hij : i ≠ j) :
    base + BitVec.ofNat 64 (8 * i) ≠ base + BitVec.ofNat 64 (8 * j) := by
  intro heq
  have := congrArg BitVec.toNat heq
  rw [toNat_addr hi hnw, toNat_addr hj hnw] at this
  omega

/-- `vs[i]!` at an in-range index is `vs[i]`. -/
theorem getBang {vs : List Word} {i : Nat} (h : i < vs.length) : vs[i]! = vs[i] :=
  getElem!_pos vs i h

/-! ## Reading and writing a region -/

/-- A load from cell `i`. -/
theorem Region.get {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    {i : Nat} (hi : i < vs.length) {v : Word} (hv : vs[i]! = v) :
    s.getMem (base + BitVec.ofNat 64 (8 * i)) = v := by
  rw [h i hi, hv]

/-- A store to cell `i` of the region it lands in. -/
theorem Region.set {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    {i : Nat} (hi : i < vs.length) (hnw : base.toNat + 8 * vs.length ≤ 2 ^ 64) (v : Word)
    {s' : MachineState} (hs' : s' = (s.setMem (base + BitVec.ofNat 64 (8 * i)) v).setPC s'.pc) :
    Region base (vs.set i v) s' := by
  intro j hj
  rw [List.length_set] at hj
  rw [hs']
  by_cases hij : j = i
  · subst hij
    rw [memShape_getMem_eq, getBang (by simpa using hj), List.getElem_set_self]
  · rw [memShape_getMem_ne (addr_ne_of_ne hj hi hnw hij), h j hj,
      getBang (vs := vs.set i v) (i := j) (by simpa using hj), List.getElem_set_ne (Ne.symm hij),
      getBang hj]

/-- A store into some *other* region leaves this one alone. -/
theorem Region.frame {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    {b₂ : Word} {n₂ : Nat} (hd : Disjoint base vs.length b₂ n₂) {j : Nat} (hj : j < n₂) (v : Word)
    {s' : MachineState} (hs' : s' = (s.setMem (b₂ + BitVec.ofNat 64 (8 * j)) v).setPC s'.pc) :
    Region base vs s' := by
  intro i hi
  rw [hs', memShape_getMem_ne (addr_ne_of_disjoint hd hi hj), h i hi]

/-- A step that does not touch memory leaves every region alone. -/
theorem Region.of_mem_eq {base : Word} {vs : List Word} {s s' : MachineState}
    (h : Region base vs s) (hm : s'.mem = s.mem) : Region base vs s' := by
  intro i hi
  simp only [MachineState.getMem, hm]
  exact h i hi

theorem Region.of_getMem_eq {base : Word} {vs : List Word} {s s' : MachineState}
    (h : Region base vs s) (hm : ∀ a, s'.getMem a = s.getMem a) : Region base vs s' := by
  intro i hi
  rw [hm]; exact h i hi

/-! ## Splitting and joining -/

theorem Region.nil {base : Word} {s : MachineState} : Region base [] s := by
  intro i hi; simp at hi

theorem Region.length_pos_of_get {base : Word} {vs : List Word} {s : MachineState}
    (_ : Region base vs s) : True := trivial

/-- The cells of a region as one fact per cell, for reading a concrete
    literal off. `vs` a literal, `i` a literal: `vs[i]!` reduces by `rfl`. -/
theorem Region.get' {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    (i : Nat) (hi : i < vs.length) :
    s.getMem (base + BitVec.ofNat 64 (8 * i)) = vs[i]! := h i hi

/-- A region seen from a base offset by whole cells. -/
theorem Region.shift {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    (k : Nat) :
    Region (base + BitVec.ofNat 64 (8 * k)) (vs.drop k) s := by
  intro i hi
  rw [List.length_drop] at hi
  have hik : k + i < vs.length := by omega
  have : base + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (8 * i)
      = base + BitVec.ofNat 64 (8 * (k + i)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  rw [this, h (k + i) hik, getBang hik, getBang (by simpa using hi), List.getElem_drop]

/-- The first `k` cells. -/
theorem Region.take {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    (k : Nat) : Region base (vs.take k) s := by
  intro i hi
  rw [List.length_take] at hi
  have hik : i < vs.length := by omega
  rw [h i hik, getBang hik, getBang (by simpa using hi), List.getElem_take]

/-- Two adjacent regions make one. -/
theorem Region.append {base : Word} {vs ws : List Word} {s : MachineState}
    (h₁ : Region base vs s) (h₂ : Region (base + BitVec.ofNat 64 (8 * vs.length)) ws s) :
    Region base (vs ++ ws) s := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hiv : i < vs.length
  · rw [h₁ i hiv, getBang hiv, getBang (by simpa using hi), List.getElem_append_left hiv]
  · have hj : i - vs.length < ws.length := by omega
    have := h₂ (i - vs.length) hj
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)] at this
    rw [this, getBang hj, getBang (by simpa using hi), List.getElem_append_right (by omega)]

end MachineChecked.RiscV.Sym

namespace MachineChecked.RiscV.Sym

/-- A list of known length is the literal of its own elements. This is how the
    executor turns a region hypothesis over a list *variable* -- a stack frame
    of unknown contents -- into one over a literal it can update cell by cell. -/
theorem List.eq_map_range {α : Type} [Inhabited α] (F : List α) {n : Nat} (h : F.length = n) :
    F = (List.range n).map (fun i => F[i]!) := by
  subst h
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact (getElem!_pos F i h1).symm

open RiscvZkvm.Rv64 in
theorem Region.of_eq {base : Word} {vs vs' : List Word} {s : MachineState}
    (h : Region base vs s) (heq : vs = vs') : Region base vs' s := heq ▸ h

end MachineChecked.RiscV.Sym

namespace MachineChecked.RiscV.Sym

/-- A "negative" offset as a subtraction. `omega`'s certificates for
    `(x + (2^64 - d)) % 2^64` are very expensive for the kernel to check;
    `(2^64 - d + x) % 2^64` is cheap. -/
theorem add_ofNat_big (x : BitVec 64) (c : Nat) (h : 2 ^ 63 ≤ c) (h2 : c < 2 ^ 64) :
    x + BitVec.ofNat 64 c = x - BitVec.ofNat 64 (2 ^ 64 - c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

end MachineChecked.RiscV.Sym

namespace MachineChecked.RiscV.Sym

theorem add_sub_cancel_left' (a b : BitVec 64) : a + b - a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add]
  have := a.isLt; have := b.isLt
  omega

theorem add_add_sub_cancel_left' (a b c : BitVec 64) : a + b + c - a = b + c := by
  rw [BitVec.add_assoc]; exact add_sub_cancel_left' a (b + c)

theorem add_add_sub_add_cancel' (a b c : BitVec 64) : a + (b + c) - (a + b) = c := by
  rw [← BitVec.add_assoc]; exact add_sub_cancel_left' (a + b) c

theorem add_add_sub_cancel_right' (a b c : BitVec 64) : a + b + c - b = a + c := by
  rw [BitVec.add_assoc, BitVec.add_comm b c, ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- An address `x + k` against a literal region base `c`: the offset is the literal `k - c`
(folded by the simprocs). Stated for `ofNat` literals only, so `bp + ofNat (10 i) + 9 - bp`
keeps its shape for the cancellation lemmas. -/
theorem add_lit_sub_lit (x : BitVec 64) (k c : Nat) :
    x + BitVec.ofNat 64 k - BitVec.ofNat 64 c = x + (BitVec.ofNat 64 k - BitVec.ofNat 64 c) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub]
  have := x.isLt
  omega

/-- A right shift of a numeral is a numeral: the executor's symbolic-offset
    loads see `base + ofNat i >>> k` as `base + ofNat e`. -/
theorem ofNat_ushiftRight (i k : Nat) :
    BitVec.ofNat 64 i >>> k = BitVec.ofNat 64 (i % 18446744073709551616 / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide)))).symm

end MachineChecked.RiscV.Sym
