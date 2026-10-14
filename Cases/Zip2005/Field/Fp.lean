/-
  Cases.Zip2005.Fp

  The guest's Pallas base field `Fp`, as numbers.

  On the zkVM the `pasta_curves` fork keeps `Fp` in Montgomery form (`a ↦ a·R`,
  `R = 2^256`) but multiplies with the `UINT256_MUL` precompile: `a * b` is
  `mulmod(mulmod(a, b, p), R⁻¹, p)` (`fields/fp.rs`, `sp1_mulmod`). So a product
  of representatives `aR`, `bR` is `abR` -- the Montgomery product -- computed by
  two exact modular multiplications instead of a reduction.
-/

import Cases.Zip2005.Field.Limbs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Cases.Zip2005.Fp

/-- The Pallas base field modulus. -/
def p : Nat := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- `R⁻¹ mod p`, `R = 2^256`: `R_INV` in `fields/fp.rs`. -/
def rInv : Nat := 0x21f1c4ff1e2278d570cb2996efc89a65ac9fba6a4077fc57cf3f8e8753a769a9

/-- `R mod p`: `Fp::one()`. -/
def R : Nat := 0x3fffffffffffffffffffffffffffffff992c350be41914ad34786d38fffffffd

/-- `R² mod p`: `R2` in `fields/fp.rs`, the factor `Fp::from_raw` multiplies by. -/
def R2 : Nat := 0x096d41af7b9cb7147797a99bc3c95d18d7d30dbd8b0de0e78c78ecb30000000f

/-- `R³ mod p`: `R3` in `fields/fp.rs`, the factor for the high half in `from_u512`. -/
def R3 : Nat := 0x2ae309222d2d9910df8d1014353fd42cf6a68f3b6ac5b1d1f185a5993a9e10f9

theorem rInv_spec : rInv * 2 ^ 256 % p = 1 := by decide +kernel
theorem R3_spec : R3 = R * R * R % p := by decide +kernel
theorem R2_spec : R2 = R * R % p := by decide +kernel
theorem R_spec : R = 2 ^ 256 % p := by decide +kernel
theorem p_lt : p < 2 ^ 256 := by decide +kernel
theorem p_pos : 0 < p := by decide +kernel

/-- The guest's `Fp` product, on representatives. -/
def mul (a b : Nat) : Nat := a * b % p * rInv % p

theorem mul_lt (a b : Nat) : mul a b < p := Nat.mod_lt _ (by decide)

/-- The guest's `Fp` sum, on representatives. -/
def add (a b : Nat) : Nat := (a + b) % p

/-- `x⁵` by the guest's square-and-multiply over the exponent `5 = 0b101`
    (`Field::pow_vartime`, which skips squaring the initial `one`). -/
def pow5 (x : Nat) : Nat :=
  let r₁ := mul R x
  let r₂ := mul r₁ r₁
  let r₃ := mul r₂ r₂
  mul r₃ x

/-- One step of `pow_vartime`'s square-and-multiply: square, then multiply by
    `x` when the exponent bit is set. -/
def sqmul (x a : Nat) (b : Bool) : Nat := if b then mul (mul a a) x else mul a a

/-- Square-and-multiply over bits `i-1, …, 0` of the exponent limb `e`. -/
def powBits (x e : Nat) : Nat → Nat → Nat
  | 0, a => a
  | i + 1, a => powBits x e i (sqmul x a (e.testBit i))

/-- `pow_vartime` exactly: square only once started, i.e. once a set bit has
    been multiplied in. -/
def powBitsV (x e : Nat) : Nat → Nat → Bool → Nat
  | 0, a, _ => a
  | i + 1, a, f =>
    let a₁ := if f then mul a a else a
    if e.testBit i then powBitsV x e i (mul a₁ x) true else powBitsV x e i a₁ f

theorem powBitsV_true (x e i a : Nat) : powBitsV x e i a true = powBits x e i a := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih =>
    simp only [powBitsV, powBits, sqmul, if_true]
    split <;> exact ih _

theorem powBitsV_clear {x e i : Nat} (a : Nat) (f : Bool) (h : e.testBit i = false) :
    powBitsV x e (i + 1) a f = powBitsV x e i (if f then mul a a else a) f := by
  simp only [powBitsV, h, Bool.false_eq_true, if_false]

theorem powBitsV_set {x e i : Nat} (a : Nat) (f : Bool) (h : e.testBit i = true) :
    powBitsV x e (i + 1) a f = powBitsV x e i (mul (if f then mul a a else a) x) true := by
  simp only [powBitsV, h, if_true]

theorem testBit_2pow62 (i : Nat) : Nat.testBit 4611686018427387904 i = decide (i = 62) := by
  rw [show (4611686018427387904 : Nat) = 2 ^ 62 by norm_num, Nat.testBit_two_pow]
  by_cases h : i = 62 <;> simp [h, eq_comm]

/-- `Fp::invert`'s value: `pow_vartime` with the exponent `p - 2`, limbs most
    significant first (`2^62`, `0`, `p₁`, `p₀ - 2`), from Montgomery one `R`. -/
def invert (x : Nat) : Nat :=
  powBits x 11037532056220336127 64 (powBits x 2469829653914515739 64
    (powBits x 0 64 (powBitsV x 4611686018427387904 64 R false)))

/-- `Ep::to_affine` on coordinates (`pasta_curves`, Jacobian): `Z = 1` is
    copied through; otherwise `ζ = Z⁻¹` (zero when `Z` is), and `(X ζ², Y ζ³)`,
    or `(0, 0)` when `ζ = 0`. -/
def toAffine (X Y Z : Nat) : Nat × Nat :=
  if Z = R then (X, Y) else
  let zi := if Z = 0 then 0 else invert Z
  if zi = 0 then (0, 0) else
  let zi2 := mul zi zi
  (mul X zi2, mul Y (mul zi2 zi))

theorem sqmul_lt (x a : Nat) (b : Bool) : sqmul x a b < p := by
  unfold sqmul; split <;> exact mul_lt _ _

theorem powBits_lt (x e : Nat) {i a : Nat} (ha : a < p) : powBits x e i a < p := by
  induction i generalizing a with
  | zero => exact ha
  | succ i ih => exact ih (sqmul_lt x a _)

theorem powBitsV_lt (x e : Nat) {i a : Nat} (f : Bool) (ha : a < p) : powBitsV x e i a f < p := by
  induction i generalizing a f with
  | zero => exact ha
  | succ i ih =>
    simp only [powBitsV]
    split
    · exact ih _ (mul_lt _ _)
    · apply ih; split
      · exact mul_lt _ _
      · exact ha

/-- `x` squared `n` times (`(0..n).fold(x, |x, _| x.square())`). -/
def sqrN (x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => sqrN (mul x x) n

theorem sqrN_succ (x n : Nat) : sqrN x (n + 1) = sqrN (mul x x) n := rfl

theorem sqrN_lt {x : Nat} (n : Nat) (hx : x < p) : sqrN x n < p := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => exact ih (mul_lt _ _)

theorem R_lt : R < p := by rw [R_spec]; exact Nat.mod_lt _ (by decide)

theorem invert_lt (x : Nat) : invert x < p :=
  powBits_lt _ _ (powBits_lt _ _ (powBits_lt _ _ (powBitsV_lt _ _ _ R_lt)))

theorem redc_eq {X M T r : Nat} (hT : 2 ^ 256 * T = X + M * p) (hX : X < 2 ^ 256)
    (hM : M < 2 ^ 256) (h1 : T < p → r = T) (h2 : p ≤ T → r + p = T) : r = X * rInv % p :=
  Cases.Zip2005.redc_eq (by decide) rInv_spec hT hX hM h1 h2

theorem redc_eq_wide {X M T r : Nat} (hT : 2 ^ 256 * T = X + M * p) (hX : X < 2 ^ 256 * p)
    (hM : M < 2 ^ 256) (h1 : T < p → r = T) (h2 : p ≤ T → r + p = T) : r = X * rInv % p :=
  Cases.Zip2005.redc_eq_wide (by decide) rInv_spec hT hX hM h1 h2

/-! ## Limb lists

The executor leaves the constants as literal limb lists (and a product
`natToLeLimbs 4 a` as its four cells, `AsmVerif.RiscV.Sym.cells4`). These fold them back into
numbers. -/

open RiscvZkvm.Rv64.Accel

theorem limbs_p : leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64,
    4611686018427387904#64] = p := by decide +kernel
theorem limbs_R : leLimbsToNat [3780891978758094845#64, 11037255111966004397#64,
    18446744073709551615#64, 4611686018427387903#64] = R := by decide +kernel
theorem limbs_rInv : leLimbsToNat [14933811601259063721#64, 12438865661331504215#64,
    8127635680764926565#64, 2445952672640170197#64] = rInv := by decide +kernel

theorem limbs_R2 : leLimbsToNat [0x8c78ecb30000000f#64, 0xd7d30dbd8b0de0e7#64,
    0x7797a99bc3c95d18#64, 0x096d41af7b9cb714#64] = R2 := by decide +kernel

theorem limbs_R3 : leLimbsToNat [17403498412575166713#64, 17773050464821424593#64,
    16108549121152898092#64, 3090323811697793296#64] = R3 := by decide +kernel

theorem limbs_mod (a : Nat) : leLimbsToNat (natToLeLimbs 4 (a % p)) = a % p :=
  Cases.Zip2005.leLimbsToNat_natToLeLimbs 4 _ (lt_trans (Nat.mod_lt _ (by decide)) p_lt)

end Cases.Zip2005.Fp
