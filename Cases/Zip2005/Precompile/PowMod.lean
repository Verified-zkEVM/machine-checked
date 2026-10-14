/-
  Cases.Zip2005.Precompile.PowMod -- the model's modular exponentiation is modular
  exponentiation.

  `Accel.powMod` is a fuel-indexed square-and-multiply (`powModAux`, 512 fuel),
  written with structural recursion so the kernel can evaluate it. The curve
  precompiles invert through it (`Accel.invMod x p = powMod x (p-2) p`), and
  the primality certificate below evaluates it on concrete numbers, so both need
  the same fact: below `2^512` exponents, it computes `b^e % m`.

  The fuel bound is exact, not a convenience: for `e ≥ 2^512` the fuel runs out
  and `powModAux` returns `1 % m`, so `powMod_eq` genuinely needs `e < 2^512`.
-/

import Cases.Zip2005.Precompile.Limbs
import Mathlib.FieldTheory.Finite.Basic

namespace Cases.Zip2005.Precompile

open RiscvZkvm.Rv64

/-- Square-and-multiply with `fuel` steps computes `b^e % m` whenever the
    exponent has at most `fuel` bits. -/
theorem powModAux_eq (m : Nat) :
    ∀ (fuel b e : Nat), e < 2 ^ fuel → Accel.powModAux m fuel b e = b ^ e % m
  | 0, b, e, h => by
    have : e = 0 := by simpa using h
    subst this; simp [Accel.powModAux]
  | fuel + 1, b, e, h => by
    unfold Accel.powModAux
    by_cases he : e = 0
    · subst he; simp
    · rw [if_neg he]
      have hlt : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at h; omega
      simp only
      rw [powModAux_eq m fuel _ _ hlt]
      have hsq : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, Nat.pow_mul, sq]
      split
      · rename_i hodd
        rw [hsq, ← Nat.mul_mod, ← Nat.pow_succ]
        congr 2
        omega
      · rename_i heven
        rw [hsq]
        congr 2
        omega

/-- `Accel.powMod b e m = b^e % m` for every exponent below `2^512`. -/
theorem powMod_eq {b e m : Nat} (h : e < 2 ^ 512) : Accel.powMod b e m = b ^ e % m := by
  rw [Accel.powMod, powModAux_eq m 512 _ _ h, ← Nat.pow_mod]

/-- `powMod` read in `ZMod m` is the power. -/
theorem cast_powMod {b e m : Nat} (h : e < 2 ^ 512) :
    ((Accel.powMod b e m : Nat) : ZMod m) = (b : ZMod m) ^ e := by
  rw [powMod_eq h, ZMod.natCast_mod, Nat.cast_pow]

/-- The model's Fermat inverse is the field inverse -- including at `0`, where
    both sides are `0`. That needs `p - 2 > 0`, so `p = 2` is excluded: there
    `invMod x 2 = x^0 % 2 = 1` for every `x`, including `0`. -/
theorem cast_invMod {p : Nat} [hp : Fact p.Prime] (h2 : 2 < p) (hlt : p < 2 ^ 512) (x : Nat) :
    ((Accel.invMod x p : Nat) : ZMod p) = (x : ZMod p)⁻¹ := by
  rw [Accel.invMod, cast_powMod (by omega)]
  by_cases hx : (x : ZMod p) = 0
  · rw [hx, inv_zero, zero_pow]
    omega
  · have h1 := ZMod.pow_card_sub_one_eq_one hx
    have hsplit : p - 1 = (p - 2) + 1 := by omega
    rw [hsplit, pow_succ] at h1
    exact eq_inv_of_mul_eq_one_left h1

end Cases.Zip2005.Precompile
