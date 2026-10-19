import Cases.Zip2005.Poseidon.PoseidonAdd
import MachineChecked.RiscV.Sym.Ro
import Cases.Zip2005.Image.Ro

/-!
# Poseidon's permutation on Montgomery limbs

The permutation as the guest computes it, on `Fp` representatives in Montgomery form
(`Fp.add`, `Fp.mul`, `Fp.pow5`): 64 rounds, full for the first and last four, partial between,
over the round constants and the MDS matrix that `P128Pow5T3::constants` copies out of the
read-only segment (`ROUND_CONSTANTS` at chunk 142, 64 × 3 elements; `MDS` at chunk 154).
-/

namespace Cases.Zip2005.Poseidon

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image

/-- `ROUND_CONSTANTS`, 64 rows of three elements, as the read-only segment holds them. -/
def rcWords : List Word :=
  Ro.roChunk142 ++ Ro.roChunk143 ++ Ro.roChunk144 ++ Ro.roChunk145 ++ Ro.roChunk146 ++ Ro.roChunk147 ++
    Ro.roChunk148 ++ Ro.roChunk149 ++ Ro.roChunk150 ++ Ro.roChunk151 ++ Ro.roChunk152 ++ Ro.roChunk153

/-- `MDS`, row-major, as the read-only segment holds it. -/
def mdsWords : List Word := Ro.roChunk154.take 36

/-- The element at word offset `k` of a limb list. -/
def elt (ws : List Word) (k : Nat) : Nat := leLimbsToNat ((ws.drop k).take 4)

abbrev St := Nat × Nat × Nat

def rc (r : Nat) : St := (elt rcWords (12 * r), elt rcWords (12 * r + 4), elt rcWords (12 * r + 8))

def mds (i j : Nat) : Nat := elt mdsWords (12 * i + 4 * j)

/-- Row `i` of the MDS product, accumulated as the guest does from zero. -/
def row (i : Nat) (y : St) : Nat :=
  Fp.add (Fp.add (Fp.add 0 (Fp.mul (mds i 0) y.1)) (Fp.mul (mds i 1) y.2.1)) (Fp.mul (mds i 2) y.2.2)

def mdsApply (y : St) : St := (row 0 y, row 1 y, row 2 y)

def fullRound (c x : St) : St :=
  mdsApply (Fp.pow5 (Fp.add x.1 c.1), Fp.pow5 (Fp.add x.2.1 c.2.1), Fp.pow5 (Fp.add x.2.2 c.2.2))

def partialRound (c x : St) : St :=
  mdsApply (Fp.pow5 (Fp.add x.1 c.1), Fp.add x.2.1 c.2.1, Fp.add x.2.2 c.2.2)

/-- Round `r`: full for `r < 4` and `60 ≤ r`, partial otherwise. -/
def round (r : Nat) (x : St) : St :=
  if r < 4 ∨ 60 ≤ r then fullRound (rc r) x else partialRound (rc r) x

/-- The first `n` rounds. -/
def rounds : Nat → St → St
  | 0, x => x
  | n + 1, x => round n (rounds n x)

def permute (x : St) : St := rounds 64 x

/-- Rounds `k, …, k + n - 1`, for a proof cut between two rounds. -/
def roundsFrom (k : Nat) : Nat → St → St
  | 0, x => x
  | n + 1, x => round (k + n) (roundsFrom k n x)

theorem rounds_add (k n : Nat) (x : St) : rounds (k + n) x = roundsFrom k n (rounds k x) := by
  induction n with
  | zero => rfl
  | succ n ih => show round (k + n) (rounds (k + n) x) = _; rw [ih]; rfl

end Cases.Zip2005.Poseidon
