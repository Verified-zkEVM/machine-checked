/-
  Cases.Zip2005.Fq

  The guest's Pallas scalar field `Fq`, as numbers: Montgomery form over
  `R = 2^256`, like `Cases.Zip2005.Fp`.
-/

import Cases.Zip2005.Field.Limbs

namespace Cases.Zip2005.Fq

/-- The Pallas scalar field modulus (the Vesta base field). -/
def q : Nat := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- `2^256` inverted modulo `q`. -/
def rInv : Nat := 0x1f7a89dd176479535790be58c050df13c68de1279dc601eb6119a3dd8e1a6f7f

/-- `R mod q`: `Fq::one()`. -/
def R : Nat := 0x3fffffffffffffffffffffffffffffff992c350be34205675b2b3e9cfffffffd

/-- `R² mod q` and `R³ mod q`: `R2`, `R3` in `fields/fq.rs`. -/
def R2 : Nat := 0x096d41af7ccfdaa97fae231004ccf59067bb433d891a16e3fc9678ff0000000f
def R3 : Nat := 0x007dd97a06e6792c888fececb8e15cb63e13bda50dba41326008b421c249dae4c

theorem rInv_spec : rInv * 2 ^ 256 % q = 1 := by decide +kernel
theorem R_spec : R = 2 ^ 256 % q := by decide +kernel
theorem R2_spec : R2 = R * R % q := by decide +kernel
theorem R3_spec : R3 = R * R * R % q := by decide +kernel
theorem q_lt : q < 2 ^ 256 := by decide +kernel
theorem q_pos : 0 < q := by decide +kernel

/-- The guest's `Fq` product and sum, on representatives. -/
def mul (a b : Nat) : Nat := a * b % q * rInv % q
def add (a b : Nat) : Nat := (a + b) % q

theorem mul_lt (a b : Nat) : mul a b < q := Nat.mod_lt _ (by decide)

theorem redc_eq {X M T r : Nat} (hT : 2 ^ 256 * T = X + M * q) (hX : X < 2 ^ 256)
    (hM : M < 2 ^ 256) (h1 : T < q → r = T) (h2 : q ≤ T → r + q = T) : r = X * rInv % q :=
  Cases.Zip2005.redc_eq (by decide) rInv_spec hT hX hM h1 h2

open RiscvZkvm.Rv64.Accel

theorem limbs_q : leLimbsToNat [10108024940646105089#64, 2469829653919213789#64, 0#64,
    4611686018427387904#64] = q := by decide +kernel
theorem limbs_rInv : leLimbsToNat [6996803668063973247#64, 14307339151492907499#64,
    6309752366338989843#64, 2268276945007704403#64] = rInv := by decide +kernel
theorem limbs_R2 : leLimbsToNat [18200867980676431887#64, 7474641938123724515#64,
    9200329640471491984#64, 679271340771891881#64] = R2 := by decide +kernel
theorem limbs_R3 : leLimbsToNat [39197710403612236#64, 16229805722976916262#64,
    9871554806900181859#64, 566775843421393608#64] = R3 := by decide +kernel

theorem limbs_mod (a : Nat) : leLimbsToNat (natToLeLimbs 4 (a % q)) = a % q :=
  Cases.Zip2005.leLimbsToNat_natToLeLimbs 4 _ (lt_trans (Nat.mod_lt _ (by decide)) q_lt)

end Cases.Zip2005.Fq
