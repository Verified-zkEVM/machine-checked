import Cases.Zip2005.Poseidon.PoseidonPerm

/-!
# `Hash::<Fp, P128Pow5T3, ConstantLength<2>, 3, 2>` on Montgomery limbs

`init` sets the state to `(0, 0, capacity)` with the capacity element `2 · 2⁶⁴` (two words of
input, one of output); `hash([a, b])` absorbs both words into the rate part and squeezes the first
state word after one permutation.
-/

namespace Cases.Zip2005.Poseidon

/-- `ConstantLength<2>`'s capacity element, `from_u128(2 << 64)`, in Montgomery form. -/
def capacity : Nat := Fp.mul (2 ^ 65) Fp.R2

/-- `Hash::init().hash([a, b])` on Montgomery representatives. -/
def hash2 (a b : Nat) : Nat := (permute (Fp.add 0 a, Fp.add 0 b, capacity)).1

end Cases.Zip2005.Poseidon
