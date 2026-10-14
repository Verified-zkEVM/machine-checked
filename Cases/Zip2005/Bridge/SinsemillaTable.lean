import Cases.Zip2005.Bridge.SpecPoint
import Cases.Zip2005.Sinsemilla.SinsemillaModel
import Cases.Zip2005.Spec.Zip2005.Imported
import Cases.Zip2005.Precompile

/-!
# The guest's Sinsemilla table is the spec's generator family

`sTable` (the 1024 points `S(j)` as the guest's read-only image holds them, Montgomery limbs)
against ironwood's `orchardGenerators.S` (the real keygen table): `sTable_gen`, entry by entry.
The check is a kernel computation (`decide +kernel`, GMP `Nat` arithmetic, no `native_decide`)
over one pass of the table in four segments of 256 entries (`tabCheckL`, `tabCheckL_sound`); one
segment at a time keeps the kernel's memory near 5 GB (the four together peak at about 10 GB).
-/

namespace Cases.Zip2005.SpecMul

open RiscvZkvm.Rv64 Cases.Zip2005.Precompile.Pallas
open Zcash.Circuits (Fp Fq Point)

/-- The spec point eight table words (Montgomery limbs of `x`, then `y`) denote. -/
def tabPt (w0 w1 w2 w3 w4 w5 w6 w7 : Word) : Point Fp :=
  ⟨((Accel.leLimbsToNat [w0, w1, w2, w3] * Fp.rInv % Fp.p : ℕ) : Fp),
    ((Accel.leLimbsToNat [w4, w5, w6, w7] * Fp.rInv % Fp.p : ℕ) : Fp)⟩

/-- One pass over the table, eight words per entry, against the spec's generators from `m`. -/
def tabCheckL : List Word → ℕ → Bool
  | w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: rest, m =>
    decide (tabPt w0 w1 w2 w3 w4 w5 w6 w7 = Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S m) &&
      tabCheckL rest (m + 1)
  | _, _ => true

theorem tabCheckL_sound : ∀ (L : List Word) (m : ℕ), tabCheckL L m = true →
    ∀ j, 8 * j + 8 ≤ L.length →
      tabPt L[8 * j]! L[8 * j + 1]! L[8 * j + 2]! L[8 * j + 3]! L[8 * j + 4]! L[8 * j + 5]!
        L[8 * j + 6]! L[8 * j + 7]! = Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S (m + j)
  | w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: rest, m, h, j, hj => by
    simp only [tabCheckL, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have ih := tabCheckL_sound rest (m + 1) h.2 j (by simp at hj; omega)
      rw [show m + (j + 1) = m + 1 + j by omega, ← ih]
      simp only [show 8 * (j + 1) = 8 * j + 8 by ring, List.getElem!_cons_succ]
  | [], _, _, j, hj => by simp at hj
  | [_], _, _, j, hj => by simp at hj
  | [_, _], _, _, j, hj => by simp at hj
  | [_, _, _], _, _, j, hj => by simp at hj
  | [_, _, _, _], _, _, j, hj => by simp at hj
  | [_, _, _, _, _], _, _, j, hj => by simp at hj
  | [_, _, _, _, _, _], _, _, j, hj => by simp at hj
  | [_, _, _, _, _, _, _], _, _, j, hj => by simp at hj

set_option maxRecDepth 100000 in
theorem tabCheck_seg0 : tabCheckL ((sTable.drop 0).take 2048) 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem tabCheck_seg1 : tabCheckL ((sTable.drop 2048).take 2048) 256 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem tabCheck_seg2 : tabCheckL ((sTable.drop 4096).take 2048) 512 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem tabCheck_seg3 : tabCheckL ((sTable.drop 6144).take 2048) 768 = true := by decide +kernel

theorem getElem!_drop_take (L : List Word) (a b i : ℕ) (hi : i < b) :
    ((L.drop a).take b)[i]! = L[a + i]! := by
  simp [List.getElem!_eq_getElem?_getD, hi, List.getElem?_drop]

theorem seg_entry (k j : ℕ) (hj : j < 256) (h : tabCheckL ((sTable.drop (2048 * k)).take 2048) (256 * k) = true)
    (hlen : 2048 * k + 2048 ≤ sTable.length) :
    tabPt sTable[2048 * k + 8 * j]! sTable[2048 * k + (8 * j + 1)]! sTable[2048 * k + (8 * j + 2)]!
      sTable[2048 * k + (8 * j + 3)]! sTable[2048 * k + (8 * j + 4)]! sTable[2048 * k + (8 * j + 5)]!
      sTable[2048 * k + (8 * j + 6)]! sTable[2048 * k + (8 * j + 7)]! =
      Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S (256 * k + j) := by
  have hl : ((sTable.drop (2048 * k)).take 2048).length = 2048 := by
    simp only [List.length_take, List.length_drop]; omega
  have := tabCheckL_sound _ _ h j (by omega)
  rw [getElem!_drop_take _ _ _ _ (by omega), getElem!_drop_take _ _ _ _ (by omega),
    getElem!_drop_take _ _ _ _ (by omega), getElem!_drop_take _ _ _ _ (by omega),
    getElem!_drop_take _ _ _ _ (by omega), getElem!_drop_take _ _ _ _ (by omega),
    getElem!_drop_take _ _ _ _ (by omega), getElem!_drop_take _ _ _ _ (by omega)] at this
  exact this

/-- **The guest's Sinsemilla table is the spec's generator family**, entry by entry. -/
theorem sTable_gen (m : ℕ) (hm : m < 1024) :
    tabPt sTable[8 * m]! sTable[8 * m + 1]! sTable[8 * m + 2]! sTable[8 * m + 3]! sTable[8 * m + 4]!
      sTable[8 * m + 5]! sTable[8 * m + 6]! sTable[8 * m + 7]! =
      Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S m := by
  have hlen := sTable_length
  obtain ⟨k, j, hk, hj, rfl⟩ : ∃ k j, k < 4 ∧ j < 256 ∧ m = 256 * k + j :=
    ⟨m / 256, m % 256, by omega, Nat.mod_lt _ (by decide), (Nat.div_add_mod m 256).symm⟩
  have hseg : tabCheckL ((sTable.drop (2048 * k)).take 2048) (256 * k) = true := by
    interval_cases k
    · exact tabCheck_seg0
    · exact tabCheck_seg1
    · exact tabCheck_seg2
    · exact tabCheck_seg3
  have r : ∀ i, 8 * (256 * k + j) + i = 2048 * k + (8 * j + i) := fun i => by ring
  rw [r 1, r 2, r 3, r 4, r 5, r 6, r 7, show 8 * (256 * k + j) = 2048 * k + 8 * j by ring]
  exact seg_entry k j hj hseg (by omega)

end Cases.Zip2005.SpecMul
