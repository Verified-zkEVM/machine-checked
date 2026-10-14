import Cases.Zip2005.Poseidon.PoseidonPerm
import Cases.Zip2005.Blake2b.SpecBridge
import Cases.Zip2005.Spec.Zip2005.Imported

/-!
# The guest's Poseidon permutation is the spec's

`Poseidon.permute` works on Montgomery representatives; `D n = n · R⁻¹` is the field element a
representative stands for. Under `D`, `Fp.add`, `Fp.mul` and `Fp.pow5` are `+`, `*` and `x⁵`, the
constants the guest reads are the spec's `P128Pow5T3` round constants and MDS matrix, and so
`permute` is `Permute.value` (4 full rounds, 28 paired partial rounds, 4 full rounds).
-/

namespace Cases.Zip2005.Poseidon

open Zcash.Circuits.Poseidon

abbrev F := CompElliptic.Fields.Pasta.PallasBaseField

/-- The field element a Montgomery representative stands for. -/
def D (n : Nat) : F := (n : F) * (Fp.rInv : F)

theorem D_add (a b : Nat) : D (Fp.add a b) = D a + D b := by
  unfold D Fp.add; rw [← Fp.p_card, ZMod.natCast_mod]; push_cast; ring

theorem D_mul (a b : Nat) : D (Fp.mul a b) = D a * D b := by
  unfold D Fp.mul; rw [← Fp.p_card, ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod]; push_cast; ring

theorem D_R : D Fp.R = 1 := by
  have h : Fp.R * Fp.rInv % Fp.p = 1 := by decide +kernel
  have := congrArg (Nat.cast : ℕ → F) h
  rw [← Fp.p_card, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
  exact this

theorem D_zero : D 0 = 0 := by simp [D]

theorem D_pow5 (x : Nat) : D (Fp.pow5 x) = D x * D x * (D x * D x) * D x := by
  simp only [Fp.pow5, D_mul, D_R, one_mul]

/-- A representative's value as a cast: the equation to check is on `Nat`. -/
theorem D_eq_cast {n m : Nat} (h : n * Fp.rInv % Fp.p = m % Fp.p) : D n = (m : F) := by
  unfold D
  rw [← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h

def Dst (x : St) : Permute.State F := { x0 := D x.1, x1 := D x.2.1, x2 := D x.2.2 }

abbrev specRC := Permute.P128Pow5T3.roundConstants
abbrev specMds := Permute.P128Pow5T3.mds

/-- The round constants the guest reads are the spec's. -/
theorem D_rc (r : Nat) (hr : r < 64) :
    D (rc r).1 = (specRC r).x0 ∧ D (rc r).2.1 = (specRC r).x1 ∧ D (rc r).2.2 = (specRC r).x2 := by
  interval_cases r <;>
    exact ⟨D_eq_cast (by decide +kernel), D_eq_cast (by decide +kernel), D_eq_cast (by decide +kernel)⟩

/-- The MDS matrix the guest reads is the spec's. -/
theorem D_mds (i j : Nat) (hi : i < 3) (hj : j < 3) : D (mds i j) = specMds i j := by
  interval_cases i <;> interval_cases j <;> exact D_eq_cast (by decide +kernel)

theorem D_row (i : Nat) (hi : i < 3) (y : St) :
    D (row i y) = D y.1 * specMds i 0 + D y.2.1 * specMds i 1 + D y.2.2 * specMds i 2 := by
  simp only [row, D_add, D_mul, D_zero, D_mds i 0 hi (by decide), D_mds i 1 hi (by decide),
    D_mds i 2 hi (by decide)]
  ring

theorem Dst_mdsApply (y : St) :
    Dst (mdsApply y) = { x0 := D y.1 * specMds 0 0 + D y.2.1 * specMds 0 1 + D y.2.2 * specMds 0 2,
                         x1 := D y.1 * specMds 1 0 + D y.2.1 * specMds 1 1 + D y.2.2 * specMds 1 2,
                         x2 := D y.1 * specMds 2 0 + D y.2.1 * specMds 2 1 + D y.2.2 * specMds 2 2 } := by
  simp only [Dst, mdsApply, D_row 0 (by decide), D_row 1 (by decide), D_row 2 (by decide)]

theorem D_pow5' (x : Nat) : D (Fp.pow5 x) = pow5 (D x) := by
  rw [D_pow5]; simp only [pow5]

/-- One partial round in the spec's terms (the spec pairs them). -/
def specPartial (r : Nat) (s : Permute.State F) : Permute.State F :=
  let y0 := pow5 (s.x0 + (specRC r).x0)
  let y1 := s.x1 + (specRC r).x1
  let y2 := s.x2 + (specRC r).x2
  { x0 := y0 * specMds 0 0 + y1 * specMds 0 1 + y2 * specMds 0 2,
    x1 := y0 * specMds 1 0 + y1 * specMds 1 1 + y2 * specMds 1 2,
    x2 := y0 * specMds 2 0 + y1 * specMds 2 1 + y2 * specMds 2 2 }

def specRound (r : Nat) (s : Permute.State F) : Permute.State F :=
  if r < 4 ∨ 60 ≤ r then FullRound.value (FullRound.params specRC specMds r) s else specPartial r s

theorem Dst_round (r : Nat) (hr : r < 64) (x : St) : Dst (round r x) = specRound r (Dst x) := by
  obtain ⟨c0, c1, c2⟩ := D_rc r hr
  unfold round specRound
  split
  · rw [fullRound, Dst_mdsApply]
    simp only [D_pow5', D_add, c0, c1, c2, FullRound.value, FullRound.params, Dst]
  · rw [partialRound, Dst_mdsApply]
    simp only [D_pow5', D_add, c0, c1, c2, specPartial, Dst]

def specRounds : Nat → Permute.State F → Permute.State F
  | 0, s => s
  | n + 1, s => specRound n (specRounds n s)

theorem Dst_rounds (n : Nat) (hn : n ≤ 64) (x : St) : Dst (rounds n x) = specRounds n (Dst x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rounds, specRounds, Dst_round n (by omega), ih (by omega)]

/-- The spec's paired partial round is two of the guest's. -/
theorem partial_pair (r : Nat) (s : Permute.State F) :
    PartialRounds.value (PartialRounds.paramsP128 specRC r) s = specPartial (r + 1) (specPartial r s) := by
  rfl

theorem value_eq (s : Permute.State F) : Permute.value specRC s = specRounds 64 s := by
  simp only [Permute.value, Fin.foldl_succ_last, Fin.foldl_zero, Fin.val_last, Fin.val_castSucc,
    partial_pair]
  simp only [specRounds, specRound]
  norm_num

/-- **The guest's permutation is the spec's**, on the values its representatives stand for. -/
theorem permute_bridge (x : St) : Dst (permute x) = Permute.value specRC (Dst x) := by
  rw [value_eq, permute, Dst_rounds 64 le_rfl]

end Cases.Zip2005.Poseidon
