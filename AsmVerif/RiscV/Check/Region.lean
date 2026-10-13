/-
  AsmVerif.RiscV.Check.Region

  Address-space regions and their disjointness: the frame on which C's layout facts sit.

  A region is a byte interval `[base, base + len)` that does not wrap. Two regions are
  disjoint when their intervals do not meet; a doubleword key that `Hits` one disjoint
  region cannot lie in another. This is the ISA-independent half of the memory layer, used
  to state that the stack, the read-only data, the statics, the heap arena and the input
  window of an image occupy separate parts of the address space.
-/

import AsmVerif.RiscV.Check.Spec

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64

/-- A byte interval `[base, base + len)`, as a concrete region of the address space. -/
structure Region where
  base : Word
  len : Nat
  deriving DecidableEq, Repr

namespace Region

/-- The first address past the region. -/
def hi (r : Region) : Nat := r.base.toNat + r.len

/-- `a` is one of the region's bytes. -/
def Mem (r : Region) (a : Word) : Prop := r.base.toNat ≤ a.toNat ∧ a.toNat < r.hi

/-- The region does not wrap past `2^64`. -/
def wf (r : Region) : Bool := decide (r.hi ≤ 2 ^ 64)

/-- The regions' intervals do not meet. -/
def Disjoint (r s : Region) : Bool :=
  decide (r.hi ≤ s.base.toNat) || decide (s.hi ≤ r.base.toNat)

/-- A disjoint pair shares no byte. -/
theorem not_mem_of_disjoint {r s : Region} (h : r.Disjoint s = true) {a : Word}
    (hr : r.Mem a) (hs : s.Mem a) : False := by
  simp only [Disjoint, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold Mem hi at hr hs
  simp only [hi] at h
  omega

/-- A key the region covers (`Mem`) is one its doubleword hits. The converse (a hit key lies
    near the region) needs clearance from the address-space ends, which the layout's regions
    have; it is stated where D uses it, with those bounds in hand. -/
theorem mem_hits {r : Region} {a : Word} (h : r.Mem a) : Hits r.base r.len a := by
  obtain ⟨hlo, hhi⟩ := h
  unfold hi at hhi
  unfold Hits
  left
  rw [BitVec.toNat_sub_of_le hlo]
  omega

end Region

/-- A list of regions is pairwise disjoint and each well-formed. -/
def Region.pairwiseOk : List Region → Bool
  | [] => true
  | r :: rs => r.wf && rs.all (r.Disjoint ·) && Region.pairwiseOk rs

theorem Region.pairwiseOk_disjoint {rs : List Region} (h : Region.pairwiseOk rs = true)
    {r s : Region} (hr : r ∈ rs) (hs : s ∈ rs) (hne : r ≠ s) : r.Disjoint s = true := by
  induction rs with
  | nil => cases hr
  | cons a as ih =>
    simp only [Region.pairwiseOk, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp hr with rfl | hr' <;> rcases List.mem_cons.mp hs with rfl | hs'
    · exact absurd rfl hne
    · exact h.1.2 s hs'
    · -- `s = a`, `r ∈ as`: disjointness is symmetric.
      have := h.1.2 r hr'
      simp only [Region.Disjoint, Bool.or_eq_true, decide_eq_true_eq] at this ⊢
      omega
    · exact ih h.2 hr' hs'

end AsmVerif.RiscV.Check
