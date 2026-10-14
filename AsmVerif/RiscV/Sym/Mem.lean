/-
  AsmVerif.RiscV.Sym.Mem

  What the symbolic executor needs to know about a region beyond its contents:
  that it is 8-aligned, inside SP1's address space, and outside the code window
  (`RegionOk`), so every access into it passes `memOkSp1`; how a store into it
  is written in the shape the executor produces; how sub-doubleword accesses
  select and update a cell; and the "everything else unchanged" predicate a
  function's postcondition carries (`Unchanged`).
-/

import AsmVerif.RiscV.Sym.Region

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

/-! ## Well-placed regions -/

/-- A region the code may access: 8-aligned, inside SP1's addressable space,
    and wholly outside the code window `[lo, hi)`. -/
structure RegionOk (lo hi : Nat) (base : Word) (n : Nat) : Prop where
  aligned : base.toNat % 8 = 0
  inMem : base.toNat + 8 * n ≤ SP1_MAX_MEMORY
  offCode : base.toNat + 8 * n ≤ lo ∨ hi ≤ base.toNat

/-- A block off a wider code window is off a narrower one. -/
theorem RegionOk.weaken {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {lo' hi' : Nat} (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : RegionOk lo' hi' base n :=
  ⟨h.aligned, h.inMem, h.offCode.imp (fun h1 => Nat.le_trans h1 hlo) (fun h2 => Nat.le_trans hhi h2)⟩

theorem RegionOk.nowrap {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n) :
    base.toNat + 8 * n ≤ 2 ^ 64 := by
  have := h.inMem; unfold SP1_MAX_MEMORY at this; omega

theorem RegionOk.sub {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    (k m : Nat) (hkm : k + m ≤ n) : RegionOk lo hi (base + BitVec.ofNat 64 (8 * k)) m := by
  have hnw := h.inMem
  unfold SP1_MAX_MEMORY at hnw
  have hk : (base + BitVec.ofNat 64 (8 * k)).toNat = base.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hk]; have := h.aligned; omega
  · rw [hk]; have := h.inMem; omega
  · rw [hk]; rcases h.offCode with h1 | h1
    · left; omega
    · right; omega

/-- Address of cell `i` plus a byte offset `k < 8`, as a `Nat`. -/
theorem toNat_cell {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) :
    (base + BitVec.ofNat 64 (8 * i + k)).toNat = base.toNat + 8 * i + k := by
  have hnw := h.inMem
  unfold SP1_MAX_MEMORY at hnw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i + k) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- A dword access to cell `i` of a well-placed region is permitted. -/
theorem dwordOk {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {i : Nat} (hi : i < n) :
    isValidDwordAccessSp1 (base + BitVec.ofNat 64 (8 * i)) = true := by
  have ht := toNat_cell h hi (k := 0) (by omega)
  simp only [Nat.add_zero] at ht
  apply isValidDwordAccessSp1_of
  · rw [ht]; have := h.inMem; omega
  · rw [ht]; have := h.aligned; omega

theorem addrOk {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) :
    isValidMemAddrSp1 (base + BitVec.ofNat 64 (8 * i + k)) = true := by
  apply isValidMemAddrSp1_of_lt
  rw [toNat_cell h hi hk]; have := h.inMem; omega

theorem aligned4Ok {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (h4 : k % 4 = 0) :
    isAligned4 (base + BitVec.ofNat 64 (8 * i + k)) = true := by
  apply isAligned4_of
  rw [toNat_cell h hi hk]; have := h.aligned; omega

theorem aligned2Ok {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (h2 : k % 2 = 0) :
    isAligned2 (base + BitVec.ofNat 64 (8 * i + k)) = true := by
  apply isAligned2_of
  rw [toNat_cell h hi hk]; have := h.aligned; omega

/-- A store of `w` bytes at byte `k` of cell `i` hits no code. -/
theorem noCodeOk {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {s : MachineState} (hcw : CodeWithin lo hi s) {i k w : Nat} (hi : i < n) (hk : k < 8)
    (hw : 0 < w) (hkw : k + w ≤ 8) :
    noCodeAt s (base + BitVec.ofNat 64 (8 * i + k)) w = true := by
  apply noCodeAt_of_codeWithin hcw _ _ hw
  · rw [toNat_cell h hi hk]
    rcases h.offCode with h1 | h1
    · left; omega
    · right; have := h.aligned; omega
  · rw [toNat_cell h hi hk]; have := h.nowrap; omega

/-! ## Sub-doubleword selection -/

theorem alignToDword_cell {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) :
    alignToDword (base + BitVec.ofNat 64 (8 * i + k)) = base + BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  have hnw := h.nowrap
  have hal := h.aligned
  have ht := toNat_cell h hi hk
  have ht0 := toNat_cell h hi (k := 0) (by omega)
  simp only [Nat.add_zero] at ht0
  rw [ht0]
  -- `alignToDword x = x &&& ~~~7`, i.e. `x - x % 8`.
  have key : ∀ y : Word, (y &&& ~~~7#64).toNat = y.toNat - y.toNat % 8 := by
    intro y
    have hlow : (y &&& 7#64).toNat = y.toNat % 8 := by
      rw [BitVec.toNat_and]; simp; exact Nat.and_two_pow_sub_one_eq_mod y.toNat 3
    have hdisj : (y &&& ~~~7#64) &&& (y &&& 7#64) = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro j
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
      cases (7#64).getLsbD j <;> cases y.getLsbD j <;> simp
    have hsum : (y &&& ~~~7#64) + (y &&& 7#64) = y := by
      rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, ← BitVec.and_or_distrib_left]
      have : (~~~7#64 ||| 7#64) = BitVec.allOnes 64 := by decide
      rw [this, BitVec.and_allOnes]
    have hle : (y &&& ~~~7#64).toNat ≤ y.toNat := by
      rw [BitVec.toNat_and]; exact Nat.and_le_left
    have hh := congrArg BitVec.toNat hsum
    rw [BitVec.toNat_add, hlow] at hh
    have hy := y.isLt
    omega
  unfold alignToDword
  rw [key, ht]
  omega

theorem byteOffset_cell {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) :
    byteOffset (base + BitVec.ofNat 64 (8 * i + k)) = k := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [toNat_cell h hi hk]
  change (base.toNat + 8 * i + k) &&& (2 ^ 3 - 1) = k
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have := h.aligned
  omega

/-! ## Stores, in the executor's shape -/

/-- The value written to a cell by a store of the given width at byte `k`. -/
def storeCell : Nat → Word → Nat → Word → Word
  | 8, _, _, v => v
  | 4, old, k, v => replaceWord32 old (k / 4) (v.truncate 32)
  | 2, old, k, v => replaceHalfword old (k / 2) (v.truncate 16)
  | 1, old, k, v => replaceByte old k (v.truncate 8)
  | _, old, _, _ => old

/-- The value a load of the given width at byte `k` reads out of a cell,
    before sign or zero extension. -/
def loadCell (w : Nat) (cell : Word) (k : Nat) : Word :=
  match w with
  | 8 => cell
  | 4 => (extractWord32 cell (k / 4)).zeroExtend 64
  | 2 => (extractHalfword cell (k / 2)).zeroExtend 64
  | 1 => (extractByte cell k).zeroExtend 64
  | _ => cell

theorem Region.set_sd {lo hi : Nat} {base : Word} {vs : List Word} {s : MachineState}
    (h : Region base vs s) (hok : RegionOk lo hi base vs.length) {i : Nat} (hi : i < vs.length)
    {a v p : Word} {s' : MachineState} (hs' : (s.setMem a v).setPC p = s')
    (ha : a = base + BitVec.ofNat 64 (8 * i)) {vs' : List Word} (hvs : vs.set i v = vs') :
    Region base vs' s' := by
  subst ha hvs
  exact Region.set h hi hok.nowrap v (by rw [← hs']; rfl)

theorem Region.frame_sd {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    {b₂ : Word} {n₂ : Nat} (hd : Disjoint base vs.length b₂ n₂) {j : Nat} (hj : j < n₂)
    {a v p : Word} {s' : MachineState} (hs' : (s.setMem a v).setPC p = s')
    (ha : a = b₂ + BitVec.ofNat 64 (8 * j)) : Region base vs s' := by
  subst ha
  exact Region.frame h hd hj v (by rw [← hs']; rfl)

/-- A store with `setWord32` is a `setMem` of the containing cell. -/
theorem setWord32_cell {lo hi : Nat} {base : Word} {n : Nat} (hok : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (s : MachineState) (v : BitVec 32) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i + k)) :
    s.setWord32 a v = s.setMem (base + BitVec.ofNat 64 (8 * i))
      (replaceWord32 (s.getMem (base + BitVec.ofNat 64 (8 * i))) (k / 4) v) := by
  subst ha
  rw [setWord32_eq, alignToDword_cell hok hi hk, byteOffset_cell hok hi hk]

theorem setHalfword_cell {lo hi : Nat} {base : Word} {n : Nat} (hok : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (s : MachineState) (v : BitVec 16) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i + k)) :
    s.setHalfword a v = s.setMem (base + BitVec.ofNat 64 (8 * i))
      (replaceHalfword (s.getMem (base + BitVec.ofNat 64 (8 * i))) (k / 2) v) := by
  subst ha
  rw [setHalfword_eq, alignToDword_cell hok hi hk, byteOffset_cell hok hi hk]

theorem setByte_cell {lo hi : Nat} {base : Word} {n : Nat} (hok : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (s : MachineState) (v : BitVec 8) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i + k)) :
    s.setByte a v = s.setMem (base + BitVec.ofNat 64 (8 * i))
      (replaceByte (s.getMem (base + BitVec.ofNat 64 (8 * i))) k v) := by
  subst ha
  rw [setByte_eq, alignToDword_cell hok hi hk, byteOffset_cell hok hi hk]

theorem getWord32_cell {lo hi : Nat} {base : Word} {n : Nat} (hok : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (s : MachineState) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i + k)) :
    s.getWord32 a = extractWord32 (s.getMem (base + BitVec.ofNat 64 (8 * i))) (k / 4) := by
  subst ha
  rw [getWord32_eq, alignToDword_cell hok hi hk, byteOffset_cell hok hi hk]

theorem getHalfword_cell {lo hi : Nat} {base : Word} {n : Nat} (hok : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (s : MachineState) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i + k)) :
    s.getHalfword a = extractHalfword (s.getMem (base + BitVec.ofNat 64 (8 * i))) (k / 2) := by
  subst ha
  rw [getHalfword_eq, alignToDword_cell hok hi hk, byteOffset_cell hok hi hk]

theorem getByte_cell {lo hi : Nat} {base : Word} {n : Nat} (hok : RegionOk lo hi base n)
    {i k : Nat} (hi : i < n) (hk : k < 8) (s : MachineState) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i + k)) :
    s.getByte a = extractByte (s.getMem (base + BitVec.ofNat 64 (8 * i))) k := by
  subst ha
  rw [getByte_eq, alignToDword_cell hok hi hk, byteOffset_cell hok hi hk]

/-! ## Everything else unchanged -/

/-- `a` lies in the region `(b, n)`. -/
def InRegion (a : Word) (b : Word) (n : Nat) : Prop :=
  b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8 * n

/-- Memory outside the listed regions is the same in `s'` as in `s`. -/
def Unchanged (W : List (Word × Nat)) (s s' : MachineState) : Prop :=
  ∀ a : Word, (∀ r ∈ W, ¬ InRegion a r.1 r.2) → s'.getMem a = s.getMem a

theorem Unchanged.refl (W : List (Word × Nat)) (s : MachineState) : Unchanged W s s :=
  fun _ _ => rfl

theorem Unchanged.trans {W : List (Word × Nat)} {s₁ s₂ s₃ : MachineState}
    (h₁ : Unchanged W s₁ s₂) (h₂ : Unchanged W s₂ s₃) : Unchanged W s₁ s₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem Unchanged.mono {W W' : List (Word × Nat)} {s s' : MachineState}
    (hsub : ∀ r ∈ W, r ∈ W') (h : Unchanged W s s') : Unchanged W' s s' :=
  fun a ha => h a (fun r hr => ha r (hsub r hr))

/-- A step that leaves memory alone. -/
theorem Unchanged.of_mem_eq {W : List (Word × Nat)} {s s' s'' : MachineState}
    (h : Unchanged W s s') (hm : s''.mem = s'.mem) : Unchanged W s s'' :=
  fun a ha => by simp only [MachineState.getMem, hm]; exact h a ha

/-- A store into a listed region. -/
theorem Unchanged.store {W : List (Word × Nat)} {s s' s'' : MachineState}
    (h : Unchanged W s s') {b : Word} {n : Nat} (hW : (b, n) ∈ W) {i : Nat} (hi : i < n)
    (hnw : b.toNat + 8 * n ≤ 2 ^ 64) {a v p : Word}
    (hs'' : (s'.setMem a v).setPC p = s'') (ha : a = b + BitVec.ofNat 64 (8 * i)) :
    Unchanged W s s'' := by
  intro x hx
  subst ha
  have hne : x ≠ b + BitVec.ofNat 64 (8 * i) := by
    intro heq
    apply hx (b, n) hW
    show InRegion x b n
    unfold InRegion
    rw [heq, toNat_addr hi hnw]
    exact ⟨by omega, by omega⟩
  rw [← hs'', memShape_getMem_ne hne]
  exact h x hx

/-- A region disjoint from everything in `W` survives an `Unchanged W` step. -/
theorem Region.of_unchanged {base : Word} {vs : List Word} {s s' : MachineState}
    (h : Region base vs s) {W : List (Word × Nat)} (hu : Unchanged W s s')
    (hd : ∀ r ∈ W, Disjoint base vs.length r.1 r.2) : Region base vs s' := by
  intro i hi
  rw [hu _ ?_]
  · exact h i hi
  · intro r hr hin
    have hdr := hd r hr
    have ht := toNat_addr hi hdr.2.1
    unfold InRegion at hin
    rw [ht] at hin
    rcases hdr.1 with h1 | h1 <;> omega

end AsmVerif.RiscV.Sym

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64 in
/-- `negw` of an aligned pointer is aligned: `memset`'s head-byte count. -/
theorem negw_and7 (a : BitVec 64) (h : a &&& 7#64 = 0#64) :
    BitVec.signExtend 64 (BitVec.truncate 32 0#64 + -BitVec.truncate 32 a) &&& 7#64 = 0#64 := by
  have ha : a.toNat % 8 = 0 := by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_signExtend]
  simp only [BitVec.truncate_eq_setWidth, BitVec.setWidth_zero, BitVec.zero_add, BitVec.toNat_neg,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  split <;> omega

/-- A region base is doubleword-aligned, as the mask test the code performs. -/
theorem RegionOk.and7 {lo hi : Nat} {b : Word} {n : Nat} (h : RegionOk lo hi b n) :
    b &&& 7#64 = 0#64 := by
  have ha := h.aligned
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

end AsmVerif.RiscV.Sym
