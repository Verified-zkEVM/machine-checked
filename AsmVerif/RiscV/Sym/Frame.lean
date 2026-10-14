/-
  AsmVerif.RiscV.Sym.Frame

  What a function specification says about everything it does not compute:
  the registers the ABI preserves, the memory it may write, and the code.

  A specification is written in continuation form (`AsmVerif.RiscV.SafeN`):

    Pre s → (∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
                  Unchanged W s t → … → Safe P t) → Safe P s

  and the executor reads each of those conjuncts back as facts about `t`.
  `W` lists the blocks the callee may write: its own stack scratch below `sp`
  (one block, sized by the callee's worst-case stack use) and whatever output
  buffers it is handed.
-/

import AsmVerif.RiscV.Sym.Syscall
import AsmVerif.RiscV.Sym.Layout

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

/-! ## Registers -/

/-- The registers the RISC-V calling convention preserves across a call:
    `sp`, `gp`, `tp` and `s0`–`s11`. -/
def calleeSavedRegs : List Reg :=
  [.x2, .x3, .x4, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The callee-saved registers hold in `t` what they held in `s`. -/
def CalleeSaved (s t : MachineState) : Prop :=
  ∀ r ∈ calleeSavedRegs, t.getReg r = s.getReg r

theorem CalleeSaved.refl (s : MachineState) : CalleeSaved s s := fun _ _ => rfl

theorem CalleeSaved.trans {s₁ s₂ s₃ : MachineState} (h₁ : CalleeSaved s₁ s₂)
    (h₂ : CalleeSaved s₂ s₃) : CalleeSaved s₁ s₃ :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem CalleeSaved.get {s t : MachineState} (h : CalleeSaved s t) (r : Reg)
    (hr : r ∈ calleeSavedRegs) {v : Word} (hv : s.getReg r = v) : t.getReg r = v :=
  (h r hr).trans hv

/-- `CalleeSaved` from one equation per register, the form a proof ends in. -/
theorem CalleeSaved.intro {s t : MachineState}
    (h2 : t.getReg .x2 = s.getReg .x2) (h3 : t.getReg .x3 = s.getReg .x3)
    (h4 : t.getReg .x4 = s.getReg .x4) (h8 : t.getReg .x8 = s.getReg .x8)
    (h9 : t.getReg .x9 = s.getReg .x9) (h18 : t.getReg .x18 = s.getReg .x18)
    (h19 : t.getReg .x19 = s.getReg .x19) (h20 : t.getReg .x20 = s.getReg .x20)
    (h21 : t.getReg .x21 = s.getReg .x21) (h22 : t.getReg .x22 = s.getReg .x22)
    (h23 : t.getReg .x23 = s.getReg .x23) (h24 : t.getReg .x24 = s.getReg .x24)
    (h25 : t.getReg .x25 = s.getReg .x25) (h26 : t.getReg .x26 = s.getReg .x26)
    (h27 : t.getReg .x27 = s.getReg .x27) : CalleeSaved s t := by
  intro r hr
  simp only [calleeSavedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-! ## Code -/

theorem regShape_code {s : MachineState} {rd : Reg} {v p : Word} :
    ((s.setReg rd v).setPC p).code = s.code := by simp
theorem memShape_code {s : MachineState} {a v p : Word} :
    ((s.setMem a v).setPC p).code = s.code := by simp
theorem pcShape_code {s : MachineState} {p : Word} : (s.setPC p).code = s.code := by simp

/-! ## Memory -/

/-- Any block is a region of *something*: its current contents. This is how a
    stack frame of unknown contents enters a proof. -/
def contents (s : MachineState) (b : Word) (n : Nat) : List Word :=
  (List.range n).map fun i => s.getMem (b + BitVec.ofNat 64 (8 * i))

theorem Region.junk (b : Word) (n : Nat) (s : MachineState) : Region b (contents s b n) s := by
  intro i hi
  simp only [contents, List.length_map, List.length_range] at hi
  rw [getBang (by simp [contents]; omega)]
  simp [contents]

/-- A block of unknown contents, as a list variable of known length. -/
theorem Region.exists_junk (b : Word) (n : Nat) (s : MachineState) :
    ∃ F : List Word, Region b F s ∧ F.length = n :=
  ⟨contents s b n, Region.junk b n s, by simp [contents]⟩

@[simp] theorem length_contents (s : MachineState) (b : Word) (n : Nat) :
    (contents s b n).length = n := by simp [contents]

/-- A sub-block of a region, as a region of its own. -/
theorem Region.sub {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    (i m : Nat) {a : Word} (ha : a = base + BitVec.ofNat 64 (8 * i))
    {ws : List Word} (hws : (vs.drop i).take m = ws) : Region a ws s := by
  subst ha hws
  exact (h.shift i).take m

theorem RegionOk.sub' {lo hi : Nat} {base : Word} {n : Nat} (h : RegionOk lo hi base n)
    (i m : Nat) (hle : i + m ≤ n) {a : Word} (ha : a = base + BitVec.ofNat 64 (8 * i)) :
    RegionOk lo hi a m := by
  subst ha; exact h.sub i m hle

/-- `(b', n')` covers `(b, n)`. -/
def Covers (b' : Word) (n' : Nat) (b : Word) (n : Nat) : Prop :=
  b'.toNat ≤ b.toNat ∧ b.toNat + 8 * n ≤ b'.toNat + 8 * n'

/-- A store into a region that a listed one covers (a heap block inside the heap range). -/
theorem Unchanged.store_cover {W : List (Word × Nat)} {s s' s'' : MachineState}
    (h : Unchanged W s s') {B : Word} {N : Nat} (hW : (B, N) ∈ W) {b : Word} {n : Nat}
    (hc : Covers B N b n) {i : Nat} (hi : i < n) (hnw : b.toNat + 8 * n ≤ 2 ^ 64) {a v p : Word}
    (hs'' : (s'.setMem a v).setPC p = s'') (ha : a = b + BitVec.ofNat 64 (8 * i)) :
    Unchanged W s s'' := by
  intro x hx
  subst ha
  have hne : x ≠ b + BitVec.ofNat 64 (8 * i) := by
    intro heq
    apply hx (B, N) hW
    show InRegion x B N
    unfold InRegion
    rw [heq, toNat_addr hi hnw]
    obtain ⟨h1, h2⟩ := hc
    exact ⟨by omega, by omega⟩
  rw [← hs'', memShape_getMem_ne hne]
  exact h x hx

/-- Composition of frames: a callee's write set covered by the caller's. -/
theorem Unchanged.trans_cover {W W' : List (Word × Nat)} {s₀ s t : MachineState}
    (h₁ : Unchanged W s₀ s) (h₂ : Unchanged W' s t)
    (hc : ∀ r ∈ W', ∃ r' ∈ W, Covers r'.1 r'.2 r.1 r.2) : Unchanged W s₀ t := by
  intro a ha
  rw [h₂ a ?_]
  · exact h₁ a ha
  · intro r hr hin
    obtain ⟨r', hr', hcov⟩ := hc r hr
    apply ha r' hr'
    unfold InRegion at hin ⊢
    unfold Covers at hcov
    omega

theorem cover_nil {W : List (Word × Nat)} : ∀ r ∈ ([] : List (Word × Nat)), ∃ r' ∈ W, Covers r'.1 r'.2 r.1 r.2 :=
  fun _ h => absurd h (by simp)

theorem cover_cons {W : List (Word × Nat)} {r : Word × Nat} {rs : List (Word × Nat)}
    {r' : Word × Nat} (hr' : r' ∈ W) (hc : Covers r'.1 r'.2 r.1 r.2)
    (ht : ∀ q ∈ rs, ∃ r' ∈ W, Covers r'.1 r'.2 q.1 q.2) :
    ∀ q ∈ r :: rs, ∃ r' ∈ W, Covers r'.1 r'.2 q.1 q.2 := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨r', hr', hc⟩
  · exact ht q hq

theorem disj_nil {b : Word} {n : Nat} : ∀ r ∈ ([] : List (Word × Nat)), Disjoint b n r.1 r.2 :=
  fun _ h => absurd h (by simp)

theorem disj_cons {b : Word} {n : Nat} {r : Word × Nat} {rs : List (Word × Nat)}
    (hd : Disjoint b n r.1 r.2) (ht : ∀ q ∈ rs, Disjoint b n q.1 q.2) :
    ∀ q ∈ r :: rs, Disjoint b n q.1 q.2 := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hd
  · exact ht q hq

/-- A region disjoint from a callee's write set survives the call. -/
theorem Region.of_unchanged' {base : Word} {vs : List Word} {s s' : MachineState}
    (h : Region base vs s) {W : List (Word × Nat)} (hu : Unchanged W s s') {n : Nat}
    (hn : vs.length = n) (hd : ∀ r ∈ W, Disjoint base n r.1 r.2) : Region base vs s' :=
  h.of_unchanged hu (hn ▸ hd)

/-- A region all of whose cells lie outside a callee's write set, except a
    sub-block the callee reports on: the region is patched with the report. -/
theorem Region.patch {base : Word} {vs : List Word} {s t : MachineState}
    (h : Region base vs s) {W : List (Word × Nat)} (hu : Unchanged W s t)
    {i : Nat} {ws : List Word} (hle : i + ws.length ≤ vs.length) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i)) (hq : Region a ws t)
    (hout : ∀ j, j < vs.length → (j < i ∨ i + ws.length ≤ j) →
      ∀ r ∈ W, ¬ InRegion (base + BitVec.ofNat 64 (8 * j)) r.1 r.2)
    {vs' : List Word} (hvs : vs.take i ++ ws ++ vs.drop (i + ws.length) = vs') :
    Region base vs' t := by
  subst ha hvs
  intro j hj
  simp only [List.length_append, List.length_take, List.length_drop] at hj
  by_cases hin : i ≤ j ∧ j < i + ws.length
  · have hk : j - i < ws.length := by omega
    have := hq (j - i) hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)] at this
    rw [this, getBang hk, getBang (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_right (by simp; omega)]
    congr 1; simp; omega
  · have hj' : j < vs.length := by omega
    rw [hu _ (hout j hj' (by omega)), h j hj']
    by_cases hlo : j < i
    · rw [getBang hj', getBang (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_append_left (by simp; omega), List.getElem_take]
    · rw [getBang hj', getBang (by simp; omega), List.getElem_append_right (by simp; omega),
        List.getElem_drop]
      congr 1; simp; omega

/-! ## The stack -/

/-- `sp` is 16-aligned and has `room` bytes of stack below it, all inside the
    legacy memory zone and below the layout's stack top. -/
structure StackOk (L : Layout) (room : Nat) (sp : Word) : Prop where
  aligned : sp.toNat % 16 = 0
  lo : room + 0x10000 ≤ sp.toNat
  hi : sp.toNat ≤ L.stackTop

end AsmVerif.RiscV.Sym

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

/-! ## Per-entry forms, for proofs the executor builds one entry at a time -/

theorem out_nil {base : Word} {n i m : Nat} :
    ∀ j, j < n → (j < i ∨ i + m ≤ j) →
      ∀ r ∈ ([] : List (Word × Nat)), ¬ InRegion (base + BitVec.ofNat 64 (8 * j)) r.1 r.2 :=
  fun _ _ _ _ h => absurd h (by simp)

theorem out_cons {base : Word} {n i m : Nat} {r : Word × Nat} {rs : List (Word × Nat)}
    (hd : ∀ j, j < n → (j < i ∨ i + m ≤ j) → ¬ InRegion (base + BitVec.ofNat 64 (8 * j)) r.1 r.2)
    (ht : ∀ j, j < n → (j < i ∨ i + m ≤ j) →
      ∀ q ∈ rs, ¬ InRegion (base + BitVec.ofNat 64 (8 * j)) q.1 q.2) :
    ∀ j, j < n → (j < i ∨ i + m ≤ j) →
      ∀ q ∈ r :: rs, ¬ InRegion (base + BitVec.ofNat 64 (8 * j)) q.1 q.2 := by
  intro j hj hji q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hd j hj hji
  · exact ht j hj hji q hq

theorem RegionOk.of_nat {lo hi : Nat} {base : Word} {n : Nat} (h1 : base.toNat % 8 = 0)
    (h2 : base.toNat + 8 * n ≤ SP1_MAX_MEMORY) (h3 : base.toNat + 8 * n ≤ lo ∨ hi ≤ base.toNat) :
    RegionOk lo hi base n := ⟨h1, h2, h3⟩

/-- A mask by a literal bounds the value: the fact the executor gives `omega` for each
    `x &&& c` in an address goal (table indices `t & 0xFF`). -/
theorem toNat_and_le_lit (x : BitVec 64) (n : Nat) : (x &&& BitVec.ofNat 64 n).toNat ≤ n := by
  rw [BitVec.toNat_and]; exact Nat.le_trans Nat.and_le_right (Nat.mod_le _ _)

/-- A mask whose low `k` bits are clear clears them in the value (aligned table offsets). -/
theorem toNat_and_mod_lit (x : BitVec 64) (n k : Nat) (hk : k ≤ 64) (h : n % 2 ^ k = 0) :
    (x &&& BitVec.ofNat 64 n).toNat % 2 ^ k = 0 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk), h, Nat.and_zero]

/-- A mask never increases the value. -/
theorem toNat_and_le_self (x y : BitVec 64) : (x &&& y).toNat ≤ x.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_left

/-! ### Bit-width bounds

`x.toNat < 2 ^ k` through literals, zero extension, shifts, masks, `|||` and `+`: the facts
`widthBound` (in `AsmVerif.RiscV.Sym.Sym`) builds for `omega`, which sees none of these operations. -/

theorem wb_mono {x : BitVec 64} {k m : Nat} (h : x.toNat < 2 ^ k) (hkm : k ≤ m) : x.toNat < 2 ^ m :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hkm)
theorem wb_lit (n k : Nat) (h : n < 2 ^ k) : (BitVec.ofNat 64 n).toNat < 2 ^ k := by
  rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h
theorem wb_setWidth {m : Nat} (x : BitVec m) (hm : m ≤ 64) : (BitVec.setWidth 64 x).toNat < 2 ^ m := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hm))]
  exact x.isLt
theorem wb_shl {x : BitVec 64} {k : Nat} (c : Nat) (h : x.toNat < 2 ^ k) : (x <<< c).toNat < 2 ^ (k + c) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos c))
theorem wb_ushr {x : BitVec 64} {k : Nat} (c : Nat) (h : x.toNat < 2 ^ k) : (x >>> c).toNat < 2 ^ (k - c) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  calc x.toNat < 2 ^ k := h
    _ ≤ 2 ^ c * 2 ^ (k - c) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
theorem wb_or {x y : BitVec 64} {k : Nat} (hx : x.toNat < 2 ^ k) (hy : y.toNat < 2 ^ k) : (x ||| y).toNat < 2 ^ k := by
  rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow hx hy
theorem wb_and_l {x : BitVec 64} {k : Nat} (y : BitVec 64) (hx : x.toNat < 2 ^ k) : (x &&& y).toNat < 2 ^ k := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_left hx
theorem wb_and_r {y : BitVec 64} {k : Nat} (x : BitVec 64) (hy : y.toNat < 2 ^ k) : (x &&& y).toNat < 2 ^ k := by
  rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right hy
theorem wb_add {x y : BitVec 64} {k : Nat} (hx : x.toNat < 2 ^ k) (hy : y.toNat < 2 ^ k) :
    (x + y).toNat < 2 ^ (k + 1) := by
  rw [BitVec.toNat_add, Nat.pow_succ]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
theorem wb_eq {x y : BitVec 64} {k : Nat} (h : y = x) (hx : x.toNat < 2 ^ k) : y.toNat < 2 ^ k := h ▸ hx

/-- `x <<< 32 >>> 32` (the compiler's zero-extension of a 32-bit value) is `x` below `2^32`. -/
theorem shl_shr32_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 32) : x <<< 32 >>> 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : x.toNat * 2 ^ 32 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mul_div_cancel _ (by decide)]

/-- `sext.w` of a value below `2^31` is the value. -/
theorem sextw_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.truncate 32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : x.toNat % 2 ^ 32 = x.toNat := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  simp only [show ¬ (2 ^ (32 - 1) ≤ x.toNat) by omega, decide_false]
  exact Nat.mod_eq_of_lt (by omega)

/-- `addiw rd, rs, 0` (the `sext.w` idiom) of a value below `2^31` is the value. -/
theorem sextw_add0_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.truncate 32 x + BitVec.truncate 32 0#64) = x := by
  rw [show BitVec.truncate 32 (0#64) = 0#32 from rfl, BitVec.add_zero]
  exact sextw_of_lt h
end AsmVerif.RiscV.Sym
