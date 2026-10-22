/-
  MachineChecked.RiscV.Sym.Carry

  A memory invariant the executor carries through stores and calls, as it carries `RoImage`.

  `Carry R Q L s`: every memory that agrees with `s`'s outside the *open* addresses satisfies
  `Q L'` for every sublist `L'` of `L`. An address is open when it lies in one of the fixed
  ranges `R` (`Nat` bounds) or in one of the buffers of the live list `L` (`(base, cells)`
  pairs). So a store to an open address keeps the fact (`Carry.setMem`), so does a call whose
  write set lies in open memory (`Carry.of_unchanged`), and buffers may be dropped from the
  list (`Carry.sublist`). What `Q` says is the program's: the allocator's control
  block and block headers, an owned static. A specification that changes closed memory (the
  allocator itself) states `Carry` of its return state, possibly with a longer live list.
-/

import MachineChecked.RiscV.Sym.Ro
import Batteries.Data.List.Perm

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

/-- An open address: inside a fixed range, or inside a live buffer. -/
def Open (R : List (Nat × Nat)) (L : List (Word × Nat)) (a : Word) : Prop :=
  (∃ r ∈ R, r.1 ≤ a.toNat ∧ a.toNat < r.2) ∨ ∃ r ∈ L, InRegion a r.1 r.2

/-- Memory `s` satisfies `Q` of every sublist of `L`, through its closed addresses only. -/
def Carry (R : List (Nat × Nat)) (Q : List (Word × Nat) → (Word → Word) → Prop)
    (L : List (Word × Nat)) (s : MachineState) : Prop :=
  ∀ m : Word → Word, (∀ a, ¬ Open R L a → m a = s.getMem a) → ∀ L', L'.Subperm L → Q L' m

/-- Every address of `[b, b + 8 n)` is open. -/
def OpenBlock (R : List (Nat × Nat)) (L : List (Word × Nat)) (b : Word) (n : Nat) : Prop :=
  ∀ a, InRegion a b n → Open R L a

variable {R : List (Nat × Nat)} {Q : List (Word × Nat) → (Word → Word) → Prop}
  {L : List (Word × Nat)} {s t : MachineState}

theorem Carry.holds (h : Carry R Q L s) : Q L s.getMem := h _ (fun _ _ => rfl) L (List.Subperm.refl L)

theorem Open.sublist {L' : List (Word × Nat)} {a : Word} (hs : L'.Sublist L) (h : Open R L' a) :
    Open R L a := by
  rcases h with h | ⟨r, hr, hin⟩
  · exact .inl h
  · exact .inr ⟨r, hs.subset hr, hin⟩

theorem Open.subperm {L' : List (Word × Nat)} {a : Word} (hs : L'.Subperm L) (h : Open R L' a) :
    Open R L a := by
  rcases h with h | ⟨r, hr, hin⟩
  · exact .inl h
  · exact .inr ⟨r, hs.subset hr, hin⟩

/-- Dropping live buffers keeps the invariant. -/
theorem Carry.sublist {L' : List (Word × Nat)} (h : Carry R Q L s) (hs : L'.Sublist L) :
    Carry R Q L' s :=
  fun m hm L'' h'' => h m (fun a ha => hm a fun h' => ha (h'.sublist hs)) L'' (h''.trans hs.subperm)

/-- The live list is a set: reordering it keeps the invariant. -/
theorem Carry.perm {L' : List (Word × Nat)} (h : Carry R Q L s) (hp : L.Perm L') :
    Carry R Q L' s :=
  fun m hm L'' h'' => h m (fun a ha => hm a fun h' => ha (h'.subperm hp.symm.subperm)) L''
    (h''.trans hp.symm.subperm)

/-- A buffer of the live list to its front. -/
theorem Carry.toFront {l₁ l₂ : List (Word × Nat)} {x : Word × Nat} (h : Carry R Q (l₁ ++ x :: l₂) s) :
    Carry R Q (x :: (l₁ ++ l₂)) s :=
  h.perm List.perm_middle

theorem Carry.of_getMem (h : Carry R Q L s) (hm : ∀ a, ¬ Open R L a → t.getMem a = s.getMem a) :
    Carry R Q L t :=
  fun m hm' => h m fun a ha => (hm' a ha).trans (hm a ha)

/-- `Carry` from `Q` at the state, when `Q` reads closed memory only and survives dropping
    live buffers. -/
theorem Carry.intro (hQ : Q L s.getMem)
    (hframe : ∀ m m' : Word → Word, Q L m → (∀ a, ¬ Open R L a → m' a = m a) → Q L m')
    (hsub : ∀ L', L'.Subperm L → ∀ m, Q L m → Q L' m) : Carry R Q L s :=
  fun m hm L' hs => hsub L' hs m (hframe _ m hQ hm)

theorem Carry.of_mem_eq (h : Carry R Q L s) (hm : t.mem = s.mem) : Carry R Q L t :=
  h.of_getMem fun a _ => by simp [MachineState.getMem, hm]

theorem Carry.of_eq (h : Carry R Q L s) (e : s = t) : Carry R Q L t := e ▸ h

/-- A store to an open address keeps the invariant. -/
theorem Carry.setMem (h : Carry R Q L s) {a : Word} (ha : Open R L a) (v p : Word) :
    Carry R Q L ((s.setMem a v).setPC p) :=
  h.of_getMem fun a' ha' => memShape_getMem_ne (s := s) fun e => ha' (by rw [e]; exact ha)

/-- A block write to open addresses keeps the invariant. -/
theorem Carry.writeWords (h : Carry R Q L s) {a : Word} {ws : List Word}
    (ha : ∀ i, i < ws.length → Open R L (a + BitVec.ofNat 64 (8 * i))) (p : Word) :
    Carry R Q L ((s.writeWords a ws).setPC p) :=
  h.of_getMem fun a' ha' => by
    rw [pcShape_getMem, getMem_writeWords_of_ne]
    intro i hi e
    exact ha' (e ▸ ha i hi)

/-- A call whose write set is open keeps the invariant. -/
theorem Carry.of_unchanged {W : List (Word × Nat)} (h : Carry R Q L s) (hu : Unchanged W s t)
    (hW : ∀ r ∈ W, OpenBlock R L r.1 r.2) : Carry R Q L t :=
  h.of_getMem fun a ha => hu a fun r hr hin => ha (hW r hr a hin)

/-- A block inside a fixed range is open. -/
theorem openBlock_range (R : List (Nat × Nat)) (L : List (Word × Nat)) {lo hi : Nat}
    (hr : (lo, hi) ∈ R) {b : Word} {n : Nat}
    (h1 : lo ≤ b.toNat) (h2 : b.toNat + 8 * n ≤ hi) : OpenBlock R L b n :=
  fun a ha => Or.inl ⟨(lo, hi), hr, by unfold InRegion at ha; omega, by unfold InRegion at ha; omega⟩

/-- A block inside one of two fixed ranges is open (a frame fact that leaves the block below
    one bound or above another). -/
theorem openBlock_range2 (R : List (Nat × Nat)) (L : List (Word × Nat)) {lo hi lo' hi' : Nat}
    (hr : (lo, hi) ∈ R) (hr' : (lo', hi') ∈ R) {b : Word} {n : Nat}
    (h : (lo ≤ b.toNat ∧ b.toNat + 8 * n ≤ hi) ∨ (lo' ≤ b.toNat ∧ b.toNat + 8 * n ≤ hi')) :
    OpenBlock R L b n := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact openBlock_range R L hr h1 h2
  · exact openBlock_range R L hr' h1 h2

/-- A block inside a live buffer is open. -/
theorem openBlock_live (R : List (Nat × Nat)) (L : List (Word × Nat)) {p : Word} {k : Nat}
    (hr : (p, k) ∈ L) {b : Word} {n : Nat}
    (h1 : p.toNat ≤ b.toNat) (h2 : b.toNat + 8 * n ≤ p.toNat + 8 * k) : OpenBlock R L b n :=
  fun a ha => Or.inr ⟨(p, k), hr, by show InRegion a p k; unfold InRegion at ha ⊢; omega⟩

/-- The empty block is open. -/
theorem openBlock_zero (R : List (Nat × Nat)) (L : List (Word × Nat)) (b : Word) :
    OpenBlock R L b 0 :=
  fun a ha => by unfold InRegion at ha; omega

theorem openW_nil (R : List (Nat × Nat)) (L : List (Word × Nat)) :
    ∀ r ∈ ([] : List (Word × Nat)), OpenBlock R L r.1 r.2 :=
  fun _ h => absurd h (by simp)

theorem openW_cons {r : Word × Nat} {rs : List (Word × Nat)} (hd : OpenBlock R L r.1 r.2)
    (ht : ∀ q ∈ rs, OpenBlock R L q.1 q.2) : ∀ q ∈ r :: rs, OpenBlock R L q.1 q.2 := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hd
  · exact ht q hq

/-- A cell of an open block is open. -/
theorem OpenBlock.cell {b : Word} {n i : Nat} (h : OpenBlock R L b n) (hi : i < n)
    (hnw : b.toNat + 8 * n ≤ 2 ^ 64) : Open R L (b + BitVec.ofNat 64 (8 * i)) :=
  h _ (by unfold InRegion; rw [toNat_addr hi hnw]; omega)

/-- The address of an open one-cell block is open. -/
theorem OpenBlock.at {a : Word} (h : OpenBlock R L a 1) (hnw : a.toNat + 8 ≤ 2 ^ 64) :
    Open R L a := by
  simpa using h.cell (i := 0) (by decide) (by simpa using hnw)

/-- A store into a cell of an open block keeps the invariant. -/
theorem Carry.setMem_cell (h : Carry R Q L s) {b : Word} {n i : Nat} (hb : OpenBlock R L b n)
    (hi : i < n) (hnw : b.toNat + 8 * n ≤ 2 ^ 64) {a : Word} (ha : a = b + BitVec.ofNat 64 (8 * i))
    (v p : Word) : Carry R Q L ((s.setMem a v).setPC p) :=
  h.setMem (ha ▸ hb.cell hi hnw) v p

/-- A block write into an open block keeps the invariant. -/
theorem Carry.writeWords_block (h : Carry R Q L s) {b : Word} {n off : Nat} (hb : OpenBlock R L b n)
    (hnw : b.toNat + 8 * n ≤ 2 ^ 64) {a : Word} {ws : List Word} (hlen : off + ws.length ≤ n)
    (ha : a = b + BitVec.ofNat 64 (8 * off)) (p : Word) :
    Carry R Q L ((s.writeWords a ws).setPC p) := by
  refine h.writeWords (fun i hi => ?_) p
  have hc := hb.cell (i := off + i) (by omega) hnw
  have : a + BitVec.ofNat 64 (8 * i) = b + BitVec.ofNat 64 (8 * (off + i)) := by
    subst ha
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [this]; exact hc

/-- A word disequality, as one of `toNat`s (a branch fact, for `omega`). -/
theorem toNat_ne_of_ne {a b : Word} (h : ¬ a = b) : ¬ a.toNat = b.toNat :=
  fun e => h (BitVec.eq_of_toNat_eq e)

end MachineChecked.RiscV.Sym
