/-
  Cases.Zip2005.Precompile.Limbs -- the accelerator wire format as numbers.

  Every SP1 precompile the guest calls (`UINT256_MUL`, `PALLAS_ADD`,
  `PALLAS_DOUBLE`) moves 256-bit numbers as four little-endian doubleword limbs,
  decoded by `Accel.leLimbsToNat` and encoded by `Accel.natToLeLimbs`
  (`riscv-zkvm`, `Rv64/ZiskAccel.lean`). This file is the arithmetic of that
  encoding and nothing else: decoding is bounded, encoding has the stated length,
  and encode-then-decode is reduction mod `2^(64n)` -- so the identity on
  anything that fits.

  These are the facts a machine-level proof consumes when it turns the model's
  `writeWords a0 (natToLeLimbs 4 r)` back into the number `r`.
-/

import RiscvZkvm.Rv64.Sp1Accel
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring

namespace Cases.Zip2005.Precompile

open RiscvZkvm.Rv64

@[simp] theorem leLimbsToNat_nil : Accel.leLimbsToNat [] = 0 := rfl

@[simp] theorem leLimbsToNat_cons (w : Word) (ws : List Word) :
    Accel.leLimbsToNat (w :: ws) = Accel.leLimbsToNat ws * 2 ^ 64 + w.toNat := rfl

/-- Decoding `n` limbs yields a number below `2^(64n)`. -/
theorem leLimbsToNat_lt (ws : List Word) : Accel.leLimbsToNat ws < 2 ^ (64 * ws.length) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw : w.toNat < 2 ^ 64 := w.isLt
    rw [leLimbsToNat_cons, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have h1 : Accel.leLimbsToNat ws * 2 ^ 64 + w.toNat < (Accel.leLimbsToNat ws + 1) * 2 ^ 64 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ ih)

/-- `natToLeLimbs (n+1) x` peels off the low limb. -/
theorem natToLeLimbs_succ (n x : Nat) :
    Accel.natToLeLimbs (n + 1) x = BitVec.ofNat 64 x :: Accel.natToLeLimbs n (x >>> 64) := by
  simp only [Accel.natToLeLimbs, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ _ (by simp) (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, ← Nat.shiftRight_add]
  congr 2
  omega

@[simp] theorem natToLeLimbs_zero (x : Nat) : Accel.natToLeLimbs 0 x = [] := rfl

@[simp] theorem length_natToLeLimbs (n x : Nat) : (Accel.natToLeLimbs n x).length = n := by
  simp [Accel.natToLeLimbs]

/-- Encode-then-decode is reduction mod `2^(64n)`. -/
theorem leLimbsToNat_natToLeLimbs (n x : Nat) :
    Accel.leLimbsToNat (Accel.natToLeLimbs n x) = x % 2 ^ (64 * n) := by
  induction n generalizing x with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [natToLeLimbs_succ, leLimbsToNat_cons, ih, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (64 * n)) (2 ^ 64), Nat.mod_mul]
    ring

/-- ...hence the identity on anything below `2^(64n)`. -/
theorem leLimbsToNat_natToLeLimbs_of_lt {n x : Nat} (h : x < 2 ^ (64 * n)) :
    Accel.leLimbsToNat (Accel.natToLeLimbs n x) = x := by
  rw [leLimbsToNat_natToLeLimbs, Nat.mod_eq_of_lt h]

/-- The four-limb instance the 256-bit precompiles use. -/
theorem leLimbsToNat_natToLeLimbs_four {x : Nat} (h : x < 2 ^ 256) :
    Accel.leLimbsToNat (Accel.natToLeLimbs 4 x) = x :=
  leLimbsToNat_natToLeLimbs_of_lt h

/-- Decode-then-encode is the identity: a limb list is determined by its value
    and its length. -/
theorem natToLeLimbs_leLimbsToNat (ws : List Word) :
    Accel.natToLeLimbs ws.length (Accel.leLimbsToNat ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw : w.toNat < 2 ^ 64 := w.isLt
    rw [List.length_cons, natToLeLimbs_succ, leLimbsToNat_cons, Nat.shiftRight_eq_div_pow]
    have hdiv : (Accel.leLimbsToNat ws * 2 ^ 64 + w.toNat) / 2 ^ 64 = Accel.leLimbsToNat ws := by
      rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 64), Nat.div_eq_of_lt hw, Nat.add_zero]
    rw [hdiv, ih]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hw]

/-- The accelerator point layout `x || y`: the first `nl` limbs of an encoded
    pair are the encoded `x`. -/
@[simp] theorem take_natToLeLimbs_append (nl a b : Nat) :
    (Accel.natToLeLimbs nl a ++ Accel.natToLeLimbs nl b).take nl = Accel.natToLeLimbs nl a := by
  simp

/-- ...and the rest are the encoded `y`. -/
@[simp] theorem drop_natToLeLimbs_append (nl a b : Nat) :
    (Accel.natToLeLimbs nl a ++ Accel.natToLeLimbs nl b).drop nl = Accel.natToLeLimbs nl b := by
  simp

end Cases.Zip2005.Precompile
