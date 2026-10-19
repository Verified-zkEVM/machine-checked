/-
  MachineChecked.RiscV.Sym.Ro

  The read-only segment of a `Layout`, as the executor sees it: `RoImage L s` says memory
  holds every chunk of `L`'s segment. A load from a literal address inside the segment is
  served from the chunk holding it (`RoImage.get`, `RoImage.ok`), and the fact survives
  every store or call whose write set lies outside the segment.

  Also here: the facts about a layout's windows the specifications' region hypotheses
  need (`RegionOk.toText`, `RegionOk.roOut`) and a frame below the stack pointer
  (`StackOk.frame`).
-/

import MachineChecked.RiscV.Sym.Regs

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

variable {L : Layout}

/-- The base address of chunk `k`. -/
def roChunkBase (L : Layout) (k : Nat) : Word := BitVec.ofNat 64 (L.roBase + 512 * k)

/-- Memory holds the read-only segment. -/
def RoImage (L : Layout) (s : MachineState) : Prop :=
  ∀ k, k < L.roChunks → Region (roChunkBase L k) (L.roChunk k) s

theorem RoImage.get {s : MachineState} (h : RoImage L s) (k : Nat) (hk : k < L.roChunks) :
    Region (roChunkBase L k) (L.roChunk k) s := h k hk

/-- Outside the segment, as a `Nat` fact about an address. -/
def OutsideRo (L : Layout) (a : Nat) : Prop := a < L.roBase ∨ L.roBase + L.roBytes ≤ a

theorem RoImage.of_mem_eq {s s' : MachineState} (h : RoImage L s) (hm : s'.mem = s.mem) :
    RoImage L s' := fun k hk => (h k hk).of_mem_eq hm

theorem RoImage.of_eq {s s' : MachineState} (h : RoImage L s) (e : s = s') : RoImage L s' := e ▸ h

theorem toNat_roCell {k i : Nat} (hk : k < L.roChunks) (hi : i < (L.roChunk k).length) :
    (roChunkBase L k + BitVec.ofNat 64 (8 * i)).toNat = L.roBase + 512 * k + 8 * i := by
  have hf := L.roChunk_fits k hk
  have hb := L.ro_nowrap
  unfold roChunkBase
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := L.roBase + 512 * k) (by omega), Nat.mod_eq_of_lt (a := 8 * i) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- A store outside the segment leaves it alone. -/
theorem RoImage.setMem {s : MachineState} (h : RoImage L s) {a : Word} (ha : OutsideRo L a.toNat)
    (v p : Word) : RoImage L ((s.setMem a v).setPC p) := by
  intro k hk i hi
  rw [memShape_getMem_ne]
  · exact h k hk i hi
  · intro heq
    have := congrArg BitVec.toNat heq
    rw [toNat_roCell hk hi] at this
    have hf := L.roChunk_fits k hk
    unfold OutsideRo at ha
    omega

theorem RoImage.writeWords {s : MachineState} (h : RoImage L s) {a : Word} {ws : List Word}
    (ha : a.toNat + 8 * ws.length ≤ L.roBase ∨ L.roBase + L.roBytes ≤ a.toNat)
    (hnw : a.toNat + 8 * ws.length ≤ 2 ^ 64) (p : Word) :
    RoImage L ((s.writeWords a ws).setPC p) := by
  intro k hk i hi
  rw [pcShape_getMem, getMem_writeWords_of_ne]
  · exact h k hk i hi
  · intro j hj heq
    have h1 := congrArg BitVec.toNat heq
    rw [toNat_roCell hk hi, toNat_addr hj hnw] at h1
    have hf := L.roChunk_fits k hk
    omega

/-- A call whose write set lies outside the segment leaves it alone. -/
theorem RoImage.of_unchanged {W : List (Word × Nat)} {s t : MachineState} (h : RoImage L s)
    (hu : Unchanged W s t)
    (hW : ∀ r ∈ W, r.1.toNat + 8 * r.2 ≤ L.roBase ∨ L.roBase + L.roBytes ≤ r.1.toNat) :
    RoImage L t := by
  intro k hk i hi
  rw [hu _ ?_]
  · exact h k hk i hi
  · intro r hr hin
    have := hW r hr
    unfold InRegion at hin
    rw [toNat_roCell hk hi] at hin
    have hf := L.roChunk_fits k hk
    omega

theorem roW_nil (L : Layout) : ∀ r ∈ ([] : List (Word × Nat)),
    r.1.toNat + 8 * r.2 ≤ L.roBase ∨ L.roBase + L.roBytes ≤ r.1.toNat :=
  fun _ h => absurd h (by simp)

theorem roW_cons {r : Word × Nat} {rs : List (Word × Nat)}
    (hd : r.1.toNat + 8 * r.2 ≤ L.roBase ∨ L.roBase + L.roBytes ≤ r.1.toNat)
    (ht : ∀ q ∈ rs, q.1.toNat + 8 * q.2 ≤ L.roBase ∨ L.roBase + L.roBytes ≤ q.1.toNat) :
    ∀ q ∈ r :: rs, q.1.toNat + 8 * q.2 ≤ L.roBase ∨ L.roBase + L.roBytes ≤ q.1.toNat := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hd
  · exact ht q hq

/-- The cells of a region wholly outside the segment are outside it. -/
theorem outsideRo_cell {base : Word} {n i : Nat} (hi : i < n) (hnw : base.toNat + 8 * n ≤ 2 ^ 64)
    (h : base.toNat + 8 * n ≤ L.roBase ∨ L.roBase + L.roBytes ≤ base.toNat) :
    OutsideRo L (base + BitVec.ofNat 64 (8 * i)).toNat := by
  rw [toNat_addr hi hnw]
  unfold OutsideRo
  omega

theorem RoImage.ok (L : Layout) (lo hi : Nat) (hlo : L.roBase + L.roBytes ≤ lo) (k : Nat)
    (hk : k < L.roChunks) : RegionOk lo hi (roChunkBase L k) (L.roChunk k).length := by
  have hf := L.roChunk_fits k hk
  have hb := L.ro_nowrap
  have hbase : (roChunkBase L k).toNat = L.roBase + 512 * k := by
    unfold roChunkBase; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, ?_, ?_⟩ <;> rw [hbase]
  · have := L.ro_aligned
    omega
  · have := L.ro_inMem
    omega
  · left; omega

/-- A function's frame: the `n` doublewords below `sp`, when the stack has room. -/
theorem StackOk.frame {room : Nat} {sp : Word} (h : StackOk L room sp) (n : Nat)
    (hn : 8 * n ≤ room) : RegionOk L.textLo L.textHi (sp - BitVec.ofNat 64 (8 * n)) n := by
  obtain ⟨h1, h2, h3⟩ := h
  have hst := L.stack_text
  have hsm := L.stack_inMem
  have e : (sp - BitVec.ofNat 64 (8 * n)).toNat = sp.toNat - 8 * n := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [e]
  · omega
  · omega
  · left; omega

/-- A block the guest may write: outside both the read-only segment and the code, which
    sit together in `[roBase, textHi)`. Specifications state their pointer arguments this
    way. -/
theorem RegionOk.toText {b : Word} {n : Nat} (h : RegionOk L.roBase L.textHi b n) :
    RegionOk L.textLo L.textHi b n := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  have := L.ro_text
  omega

theorem RegionOk.roOut {b : Word} {n : Nat} (h : RegionOk L.roBase L.textHi b n) :
    b.toNat + 8 * n ≤ L.roBase ∨ L.roBase + L.roBytes ≤ b.toNat := by
  obtain ⟨_, _, h3⟩ := h
  have := L.ro_text
  have := L.text_le
  omega

/-- A sub-block of a region off the segment is off it. -/
theorem roOut_sub {base : Word} {n : Nat}
    (h : base.toNat + 8 * n ≤ L.roBase ∨ L.roBase + L.roBytes ≤ base.toNat)
    (hnw : base.toNat + 8 * n ≤ 2 ^ 64) (i m : Nat) {a : Word}
    (ha : a = base + BitVec.ofNat 64 (8 * i)) (him : i + m ≤ n) :
    a.toNat + 8 * m ≤ L.roBase ∨ L.roBase + L.roBytes ≤ a.toNat := by
  subst ha
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end MachineChecked.RiscV.Sym
