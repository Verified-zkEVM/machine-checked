import Cases.Zip2005.Kit.Mathlib
import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Field.MontTail
import Cases.Zip2005.Image.F_78029b64
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

theorem land_p0 (y : Nat) : (y &&& 11037532056220336129) % 2 ^ 32 = y % 2 := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (11037532056220336129 &&& 2 ^ 32 - 1 : Nat) = 1 by decide, Nat.and_one_is_mod]

/-- The low 32 bits of the final subtraction's first limb do not depend on the mask's high
    bits: `p0 ≡ 1 (mod 2^32)`, so `get_lower_32` masks with `1` where `to_repr` masks with `p0`. -/
theorem low32_eq (a b : BitVec 64) : BitVec.setWidth 32 (((a + 1#64) &&& 1#64) + b) =
    BitVec.setWidth 32 (((a + 18446744073709551615#64) &&& 11037532056220336129#64) + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_add]
  have c1 : (1#64).toNat = 1 := rfl
  have c2 : (18446744073709551615#64).toNat = 18446744073709551615 := rfl
  have c3 : (11037532056220336129#64).toNat = 11037532056220336129 := rfl
  rw [c1, c2, c3, Nat.and_one_is_mod]
  have := land_p0 ((a.toNat + 18446744073709551615) % 2 ^ 64)
  generalize (a.toNat + 18446744073709551615) % 2 ^ 64 &&& 11037532056220336129 = z at this ⊢
  omega

theorem low32_add (a b c d : Nat) :
    a % 2 ^ 32 = (a + 2 ^ 64 * b + 2 ^ 128 * c + 2 ^ 192 * d) % 2 ^ 32 := by
  omega

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- `Fp::get_lower_32`: the low 32 bits of `x·R⁻¹ mod p` (`montgomery_reduce`, first limb).
    Only those bits are computed -- the upper half of `a0` is not zero-extended, and the
    callers truncate (`slli`/`srli` by 32). -/
theorem fp_get_lower_32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 : Word) (x0 x1 x2 x3 : Word)
    (hpc : s.pc = 0x78029b64#64) (hcode : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0)
    (hx : Region a0 [x0, x1, x2, x3] s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [] s t →
      (t.getReg .x10).setWidth 32 = BitVec.ofNat 32 (leLimbsToNat [x0, x1, x2, x3] * Fp.rInv % Fp.p) →
      SafeN G n P t) :
    SafeN G n P s := by
  sym_exec
  sym_close hk
  bn_lin
  have z1 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v8_def v11_def v14_def
  have z2 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v35_def v37_def v38_def
  have z3 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v59_def v61_def v62_def
  have z4 := Bn.mont_low (n0 := 11037532056220336127) (p0 := 11037532056220336129) (by decide) v83_def v85_def v86_def
  have r1 : x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat + v8.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v22.toNat + 2^64 * v25.toNat + 2^128 * v32.toNat + 2^192 * v34.toNat) := by
    linarith
  have r2 : v22.toNat + 2^64 * v25.toNat + 2^128 * v32.toNat + 2^192 * v34.toNat + v35.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v46.toNat + 2^64 * v49.toNat + 2^128 * v56.toNat + 2^192 * v58.toNat) := by
    linarith
  have r3 : v46.toNat + 2^64 * v49.toNat + 2^128 * v56.toNat + 2^192 * v58.toNat + v59.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v70.toNat + 2^64 * v73.toNat + 2^128 * v80.toNat + 2^192 * v82.toNat) := by
    linarith
  have r4 : v70.toNat + 2^64 * v73.toNat + 2^128 * v80.toNat + 2^192 * v82.toNat + v83.toNat * (11037532056220336129 + 2^64 * 2469829653914515739 + 2^254)
      = 2^64 * (v94.toNat + 2^64 * v97.toNat + 2^128 * v104.toNat + 2^192 * v106.toNat) := by
    linarith
  have hT : 2 ^ 256 * (v94.toNat + 2^64 * v97.toNat + 2^128 * v104.toNat + 2^192 * v106.toNat)
      = (x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat)
        + (v8.toNat + 2^64 * v35.toNat + 2^128 * v59.toNat + 2^192 * v83.toNat) * Fp.p := by
    rw [show Fp.p = 11037532056220336129 + 2^64 * 2469829653914515739 + 2^192 * 2^62 by decide]
    symm; linear_combination r1 + 2^64 * r2 + 2^128 * r3 + 2^192 * r4
  obtain ⟨w137, w137_def⟩ : ∃ w, (v135 + 18446744073709551615#64 &&& 11037532056220336129#64 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w138, w138_def⟩ : ∃ w, (w137 + (v94 + 7409212017489215487#64) : Word) = w := ⟨_, rfl⟩
  obtain ⟨w139, w139_def⟩ : ∃ w, (if w138.ult w137 = true then 1#64 else 0#64 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w140, w140_def⟩ : ∃ w, (v135 + 18446744073709551615#64 &&& 2469829653914515739#64 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w141, w141_def⟩ : ∃ w, (w140 + (v116 + 15976914419795035877#64) : Word) = w := ⟨_, rfl⟩
  obtain ⟨w142, w142_def⟩ : ∃ w, (if w141.ult w140 = true then 1#64 else 0#64 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w143, w143_def⟩ : ∃ w, (w141 + w139 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w144, w144_def⟩ : ∃ w, (if w143.ult w141 = true then 1#64 else 0#64 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w145, w145_def⟩ : ∃ w, (w142 + w144 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w146, w146_def⟩ : ∃ w, (w145 + v124 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w147, w147_def⟩ : ∃ w, (if w146.ult w145 = true then 1#64 else 0#64 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w150, w150_def⟩ : ∃ w, (v135 + 18446744073709551615#64 &&& 4611686018427387904#64 : Word) = w := ⟨_, rfl⟩
  obtain ⟨w151, w151_def⟩ : ∃ w, (w150 + (v128 + 13835058055282163712#64) : Word) = w := ⟨_, rfl⟩
  obtain ⟨w152, w152_def⟩ : ∃ w, (w151 + w147 : Word) = w := ⟨_, rfl⟩
  have tl := mont_sub_tail (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v112_def v116_def v117_def v118_def v120_def v121_def v123_def v124_def
    v125_def v126_def v127_def v128_def v129_def v130_def v134_def v135_def w137_def w138_def w139_def w140_def w141_def w142_def w143_def w144_def w145_def w146_def w147_def w150_def w151_def w152_def
  dsimp only at tl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide]
    at tl
  have hXe : leLimbsToNat [x0, x1, x2, x3] =
      x0.toNat + 2^64 * x1.toNat + 2^128 * x2.toNat + 2^192 * x3.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hMe : leLimbsToNat [v8, v35, v59, v83] =
      v8.toNat + 2^64 * v35.toNat + 2^128 * v59.toNat + 2^192 * v83.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hX := leLimbsToNat_lt [x0, x1, x2, x3]
  have hM := leLimbsToNat_lt [v8, v35, v59, v83]
  rw [hXe] at hX
  rw [hMe] at hM
  have hR := Fp.redc_eq hT hX hM tl.1 tl.2
  rw [hx10, hXe, ← hR, ← v138_def, ← v137_def, low32_eq, w137_def, w138_def]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, Bn.toNat_ofNat']
  exact low32_add _ _ _ _

end Cases.Zip2005
