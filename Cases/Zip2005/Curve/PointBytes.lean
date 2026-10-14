import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Curve.FromBytesKit

/-!
# Point encodings: the kit

Four-limb values that are zero, the `CtOption` mask from an `is_some` byte that is `0` or `1`,
and a masked list that is the unmasked one when the mask can only clear zeros.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem limbs4_zero_iff (X : Nat) (h : X < 2 ^ 256) :
    (BitVec.ofNat 64 X = 0#64 ∧ BitVec.ofNat 64 (X >>> 64) = 0#64 ∧
      BitVec.ofNat 64 (X >>> 128) = 0#64 ∧ BitVec.ofNat 64 (X >>> 192) = 0#64) ↔ X = 0 := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    have hX := leLimbsToNat_natToLeLimbs 4 X (by simpa using h)
    rw [natToLeLimbs_four, h0, h1, h2, h3] at hX
    simpa using hX.symm
  · rintro rfl
    simp

/-- `x &&& -is_some` for an `is_some` byte that is `0` under `c` and `1` otherwise. -/
theorem and_neg_zext_if (x : Word) (c : Prop) [Decidable c] :
    x &&& -(BitVec.zeroExtend 64 (if c then 0#8 else 1#8)) = if c then 0#64 else x := by
  split
  · rw [show -(BitVec.zeroExtend 64 0#8) = 0#64 by decide]
    exact BitVec.and_zero
  · rw [show -(BitVec.zeroExtend 64 1#8) = 18446744073709551615#64 by decide]
    exact and_allOnes' x

/-- A mask that can only clear words that are zero anyway. -/
theorem ite_list4 (c : Prop) [Decidable c] (a b d e : Word)
    (h : c → a = 0#64 ∧ b = 0#64 ∧ d = 0#64 ∧ e = 0#64) :
    [if c then 0#64 else a, if c then 0#64 else b, if c then 0#64 else d, if c then 0#64 else e] =
      [a, b, d, e] := by
  split
  · obtain ⟨ha, hb, hd, he⟩ := h ‹c›
    rw [ha, hb, hd, he]
  · rfl

end Cases.Zip2005
