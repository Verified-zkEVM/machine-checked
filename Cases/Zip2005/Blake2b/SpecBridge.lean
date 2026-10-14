import Cases.Zip2005.Blake2b.PrfExpandSpec
import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Field.Fq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Machine words and spec byte strings

The joins between the machine's limb lists and the specification's integers and byte strings:
`leos2ip` of a serialised limb list is its number, `i2leosp 256` of a number below `2^256` is its four
limbs' bytes, Montgomery form undone (`Fq.mont_back`, `Fp.mont_back`), `Fq::from_uniform_bytes`'s
value, and `ToScalar^Orchard`'s.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel _root_.Zip2005 _root_.Zip2005.Blake2b

set_option autoImplicit false

theorem leos2ip_stateBytes (ws : List Word) : leos2ip (stateBytes (ws.map BitVec.toNat)) = leLimbsToNat ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have e : stateBytes ((w :: ws).map BitVec.toNat) = wordBytes w.toNat ++ stateBytes (ws.map BitVec.toNat) := by
      simp [stateBytes]
    rw [e, leos2ip_append, B2b.wordBytes_length, B2b.leos2ip_wordBytes, ih, leLimbsToNat_cons]
    ring

theorem leos2ip_inj (S T : List UInt8) (hl : S.length = T.length) (h : leos2ip S = leos2ip T) : S = T := by
  induction S generalizing T with
  | nil => cases T with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons b S ih => cases T with
    | nil => simp at hl
    | cons c T =>
      simp only [leos2ip_cons] at h
      have hb := b.toNat_lt; have hc := c.toNat_lt
      have e1 : b.toNat = c.toNat := by omega
      have e2 : leos2ip S = leos2ip T := by omega
      rw [UInt8.toNat_inj.mp e1, ih T (by simpa using hl) e2]

theorem leos2ip_i2leospAux (k n : Nat) : leos2ip (i2leospAux k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [i2leospAux, Nat.mod_one]
  | succ k ih =>
    simp only [i2leospAux, leos2ip_cons, ih, UInt8.toNat_ofNat']
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num, Nat.mod_mod, pow_succ, Nat.mul_comm (256 ^ k), Nat.mod_mul]

/-- A number below `2^256` as 32 bytes: its four limbs' serialisation. -/
theorem i2leosp256_limbs (v : Nat) (hv : v < 2 ^ 256) :
    i2leosp 256 v = stateBytes ((natToLeLimbs 4 v).map BitVec.toNat) := by
  apply leos2ip_inj
  · simp [stateBytes_length]
  · rw [leos2ip_stateBytes, leLimbsToNat_natToLeLimbs 4 v (by simpa using hv), i2leosp, leos2ip_i2leospAux]
    exact Nat.mod_eq_of_lt (by simpa using hv)

/-- A word as 8 bytes. -/
theorem i2leosp64_word (w : Word) : i2leosp 64 w.toNat = stateBytes [w.toNat] := by
  apply leos2ip_inj
  · simp [stateBytes_length]
  · have e := leos2ip_stateBytes [w]
    simp only [List.map_cons, List.map_nil] at e
    rw [e, leLimbsToNat_cons, leLimbsToNat_nil, i2leosp, leos2ip_i2leospAux]
    have := w.isLt
    simp only [Nat.zero_mul, Nat.zero_add, Nat.reduceAdd, Nat.reduceDiv]
    exact Nat.mod_eq_of_lt (by simpa using this)

theorem Fq.mont_back (a : Nat) : a * Fq.R % Fq.q * Fq.rInv % Fq.q = a % Fq.q := by
  have h1 : Fq.R * Fq.rInv % Fq.q = 1 := by decide +kernel
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, h1, Nat.mul_one, Nat.mod_mod]

theorem Fp.mont_back (a : Nat) : a * Fp.R % Fp.p * Fp.rInv % Fp.p = a % Fp.p := by
  have h1 : Fp.R * Fp.rInv % Fp.p = 1 := by decide +kernel
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, h1, Nat.mul_one, Nat.mod_mod]

/-- `Fq::from_uniform_bytes` in Montgomery form: the 512-bit number `lo + 2^256·hi`, times `R`. -/
theorem Fq.from_uniform_eq (lo hi : Nat) :
    Fq.add (Fq.mul lo Fq.R2) (Fq.mul hi Fq.R3) = (lo + 2 ^ 256 * hi) * Fq.R % Fq.q := by
  have h1 : Fq.R2 * Fq.rInv % Fq.q = Fq.R % Fq.q := by decide +kernel
  have h2 : Fq.R3 * Fq.rInv % Fq.q = 2 ^ 256 * Fq.R % Fq.q := by decide +kernel
  unfold Fq.add Fq.mul
  apply (ZMod.natCast_eq_natCast_iff' _ _ Fq.q).mp
  have c1 := congrArg (Nat.cast : ℕ → ZMod Fq.q) h1
  have c2 := congrArg (Nat.cast : ℕ → ZMod Fq.q) h2
  simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at c1 c2 ⊢
  linear_combination (lo : ZMod Fq.q) * c1 + (hi : ZMod Fq.q) * c2

/-- `Fp::from_uniform_bytes` in Montgomery form. -/
theorem Fp.from_uniform_eq (lo hi : Nat) :
    Fp.add (Fp.mul lo Fp.R2) (Fp.mul hi Fp.R3) = (lo + 2 ^ 256 * hi) * Fp.R % Fp.p := by
  have h1 : Fp.R2 * Fp.rInv % Fp.p = Fp.R % Fp.p := by decide +kernel
  have h2 : Fp.R3 * Fp.rInv % Fp.p = 2 ^ 256 * Fp.R % Fp.p := by decide +kernel
  unfold Fp.add Fp.mul
  apply (ZMod.natCast_eq_natCast_iff' _ _ Fp.p).mp
  have c1 := congrArg (Nat.cast : ℕ → ZMod Fp.p) h1
  have c2 := congrArg (Nat.cast : ℕ → ZMod Fp.p) h2
  simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at c1 c2 ⊢
  linear_combination (lo : ZMod Fp.p) * c1 + (hi : ZMod Fp.p) * c2

theorem Fq.q_card : CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD = Fq.q := rfl

theorem Fp.p_card : CompElliptic.Fields.Pasta.PALLAS_BASE_CARD = Fp.p := rfl

/-- Eight limbs as two 256-bit halves. -/
theorem leLimbsToNat_halves (O : List Word) (h : O.length = 8) :
    leLimbsToNat [O[0]!, O[1]!, O[2]!, O[3]!] + 2 ^ 256 * leLimbsToNat [O[4]!, O[5]!, O[6]!, O[7]!] =
      leLimbsToNat O := by
  match O, h with
  | [a, b, c, d, e, f, g, i], _ =>
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, leLimbsToNat_cons, leLimbsToNat_nil]
    ring

theorem toScalarOrchard_val (x : List UInt8) : (toScalarOrchard x).val = leos2ip x % Fq.q := by
  unfold toScalarOrchard
  rw [ZMod.val_natCast, Fq.q_card]

theorem toBaseOrchard_val (x : List UInt8) : (toBaseOrchard x).val = leos2ip x % Fp.p := by
  unfold toBaseOrchard
  rw [ZMod.val_natCast, Fp.p_card]

end Cases.Zip2005
