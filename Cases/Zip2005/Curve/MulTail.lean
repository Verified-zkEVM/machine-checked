/-
  Cases.Zip2005.MulTail

  The branch tests of `Ep::mul` (`Cases.Zip2005.Mul`), as facts about the words they
  test: the projective `Z` compared with zero and with `R` limb by limb, and the
  canonical-`y` assertion, whose borrow chain is scheduled differently from the
  `x` one (`lt_flag`).
-/

import Cases.Zip2005.Field.MontTailR

namespace Cases.Zip2005

open RiscvZkvm.Rv64

theorem ult1 (x : Word) : x.ult 1#64 = decide (x = 0#64) := by
  by_cases h : x = 0#64
  · subst h; decide
  · simp only [h, decide_false]; rw [BitVec.ult]; simp; bv_omega

theorem ult1_add1 (x : Word) : (x + 1#64).ult 1#64 = decide (x = 18446744073709551615#64) := by
  rw [ult1]
  by_cases h : x = 18446744073709551615#64
  · subst h; decide
  · simp only [h, decide_false]; simp only [decide_eq_false_iff_not]; bv_omega

/-- `Z == 0`, limb by limb, the flags ANDed as bytes. -/
theorem zflag {z0 z1 z2 z3 v18 v23 v24 v28 v29 v34 v35 v39 v40 v45 v46 v50 v51 v55 : Word}
    (v18_def : (if z0.ult 1#64 = true then 1#64 else 0#64) = v18)
    (v23_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v18) = v23)
    (v24_def : (if z1.ult 1#64 = true then 1#64 else 0#64) = v24)
    (v28_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v24) &&& v23 = v28)
    (v29_def : v28 &&& 255#64 = v29)
    (v34_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v29) = v34)
    (v35_def : (if z2.ult 1#64 = true then 1#64 else 0#64) = v35)
    (v39_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v35) &&& v34 = v39)
    (v40_def : v39 &&& 255#64 = v40)
    (v45_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v40) = v45)
    (v46_def : (if z3.ult 1#64 = true then 1#64 else 0#64) = v46)
    (v50_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v46) &&& v45 = v50)
    (v51_def : v50 &&& 255#64 = v51)
    (v55_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v51) &&& 255#64 = v55) :
    v55 = if z0 = 0#64 ∧ z1 = 0#64 ∧ z2 = 0#64 ∧ z3 = 0#64 then 1#64 else 0#64 := by
  subst_vars
  simp only [ult1]
  by_cases h0 : z0 = 0#64 <;> by_cases h1 : z1 = 0#64 <;> by_cases h2 : z2 = 0#64 <;>
    by_cases h3 : z3 = 0#64 <;> simp [h0, h1, h2, h3]

/-- `Z == R`, limb by limb (`xor` with the limb, or `+ 1` for the all-ones limb). -/
theorem rflag {R0 R1 R3 z0 z1 z2 z3 v77 v78 v84 v85 v86 v90 v91 v95 v97 v101 v102 v106 v109 v110 v114
      v115 v119 : Word}
    (v77_def : z0 ^^^ R0 = v77)
    (v78_def : (if v77.ult 1#64 = true then 1#64 else 0#64) = v78)
    (v84_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v78) = v84)
    (v85_def : z1 ^^^ R1 = v85)
    (v86_def : (if v85.ult 1#64 = true then 1#64 else 0#64) = v86)
    (v90_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v86) &&& v84 = v90)
    (v91_def : v90 &&& 255#64 = v91)
    (v95_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v91) = v95)
    (v97_def : (if (z2 + 1#64).ult 1#64 = true then 1#64 else 0#64) = v97)
    (v101_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v97) &&& v95 = v101)
    (v102_def : v101 &&& 255#64 = v102)
    (v106_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v102) = v106)
    (v109_def : z3 ^^^ R3 = v109)
    (v110_def : (if v109.ult 1#64 = true then 1#64 else 0#64) = v110)
    (v114_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v110) &&& v106 = v114)
    (v115_def : v114 &&& 255#64 = v115)
    (v119_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v115) &&& 255#64 = v119) :
    v119 = if z0 = R0 ∧ z1 = R1 ∧ z2 = 18446744073709551615#64 ∧ z3 = R3 then 1#64 else 0#64 := by
  subst_vars
  simp only [ult1_add1]
  simp only [ult1, BitVec.xor_eq_zero_iff]
  by_cases h0 : z0 = R0 <;> by_cases h1 : z1 = R1 <;> by_cases h2 : z2 = 18446744073709551615#64 <;>
    by_cases h3 : z3 = R3 <;> simp [h0, h1, h2, h3]

/-- Limbs 0–1 of the canonical-`y` test: the mask `v383` is the borrow of
    `y mod 2^128 - (P0 + 2^64 P1)`. -/
theorem ystage01 {N0 N1 : Nat} {y0 y1 v371 v374 v377 v379 v380 v381 v382 v383 : Word}
    (v371_def : (if (y0 + BitVec.ofNat 64 N0).ult y0 = true then 1#64 else 0#64) = v371)
    (v374_def : (18446744073709551615#64 + v371).sshiftRight 63 = v374)
    (v377_def : (if (y1 + BitVec.ofNat 64 N1).ult y1 = true then 1#64 else 0#64) = v377)
    (v379_def : 18446744073709551615#64 + (v377 + v374) = v379)
    (v380_def : y1 + (BitVec.ofNat 64 N1 + v374) = v380)
    (v381_def : (if v380.ult (y1 + BitVec.ofNat 64 N1) = true then 1#64 else 0#64) = v381)
    (v382_def : v379 + v381 = v382)
    (v383_def : v382.sshiftRight 63 = v383) (hN0 : 0 < N0 ∧ N0 < 2 ^ 64)
    (hN1 : 0 < N1 ∧ N1 < 2 ^ 64) :
    (v383 = 0#64 ∧ (2 ^ 64 - N0) + 2 ^ 64 * (2 ^ 64 - N1) ≤ y0.toNat + 2 ^ 64 * y1.toNat) ∨
      (v383 = 18446744073709551615#64 ∧
        y0.toNat + 2 ^ 64 * y1.toNat < (2 ^ 64 - N0) + 2 ^ 64 * (2 ^ 64 - N1)) := by
  subst v379_def v382_def v383_def
  split at v371_def <;> rename_i h0 <;> subst v371_def <;>
    [rw [show (18446744073709551615#64 + 1#64).sshiftRight 63 = 0#64 by decide] at v374_def;
     rw [show (18446744073709551615#64 + 0#64).sshiftRight 63 = 18446744073709551615#64 by decide]
       at v374_def] <;>
    subst v374_def <;> split at v377_def <;> rename_i h1 <;> subst v377_def <;>
    split at v381_def <;> rename_i h2 <;> subst v381_def <;>
    simp only [BitVec.ult, decide_eq_true_eq] at h0 h1 h2
  all_goals first
    | (left; refine ⟨by decide, ?_⟩; bv_omega)
    | (right; refine ⟨by decide, ?_⟩; bv_omega)

/-- Limb 2 (`p2 = 0`): the borrow passes through when `y2 = 0`. -/
theorem ystage2 {Pl : Nat} {yl : Nat} {y2 v383 v384 v385 v386 v387 : Word}
    (h383 : (v383 = 0#64 ∧ Pl ≤ yl) ∨ (v383 = 18446744073709551615#64 ∧ yl < Pl))
    (v384_def : v383 + y2 = v384)
    (v385_def : (if v384.ult v383 = true then 1#64 else 0#64) = v385)
    (v386_def : v383 + v385 = v386)
    (v387_def : v386.sshiftRight 63 = v387) (hyl : yl < 2 ^ 128) (hPl : Pl < 2 ^ 128) :
    (v387 = 0#64 ∧ Pl ≤ yl + 2 ^ 128 * y2.toNat) ∨
      (v387 = 18446744073709551615#64 ∧ yl + 2 ^ 128 * y2.toNat < Pl) := by
  subst v384_def v386_def v387_def
  rcases h383 with ⟨e, h⟩ | ⟨e, h⟩ <;> subst e
  · left
    rw [show (0#64 + y2).ult 0#64 = false by simp [BitVec.ult]] at v385_def
    subst v385_def
    exact ⟨by decide, by omega⟩
  · by_cases hy : y2 = 0#64
    · subst hy; right
      rw [show (18446744073709551615#64 + 0#64).ult 18446744073709551615#64 = false by decide]
        at v385_def
      subst v385_def
      exact ⟨by decide, by simp; omega⟩
    · left
      rw [show (18446744073709551615#64 + y2).ult 18446744073709551615#64 = true by
        simp only [BitVec.ult, decide_eq_true_eq]; bv_omega] at v385_def
      subst v385_def
      have : 1 ≤ y2.toNat := by bv_omega
      exact ⟨by decide, by omega⟩

/-- Limb 3 (`p3 = 2^62`): the parity bit of the result is the "`y < p`" flag. -/
theorem ystage3 {P yl : Nat} {y3 v387 v390 v392 v393 v394 v395 : Word}
    (h387 : (v387 = 0#64 ∧ P ≤ yl) ∨ (v387 = 18446744073709551615#64 ∧ yl < P))
    (v390_def : (if (y3 + 13835058055282163712#64).ult y3 = true then 1#64 else 0#64) = v390)
    (v392_def : 1#64 + (v390 + v387) = v392)
    (v393_def : y3 + (13835058055282163712#64 + v387) = v393)
    (v394_def : (if v393.ult (y3 + 13835058055282163712#64) = true then 1#64 else 0#64) = v394)
    (v395_def : v392 + v394 = v395) (hyl : yl < 2 ^ 192) (hf : v395 &&& 1#64 = 1#64) :
    yl + 2 ^ 192 * y3.toNat < P + 2 ^ 192 * 2 ^ 62 := by
  subst v392_def v393_def v395_def
  rcases h387 with ⟨e, h⟩ | ⟨e, h⟩ <;> subst e <;>
    split at v390_def <;> rename_i h0 <;> subst v390_def <;>
    split at v394_def <;> rename_i h1 <;> subst v394_def <;>
    simp only [BitVec.ult, decide_eq_true_eq] at h0 h1 <;>
    first
    | (exfalso; revert hf; decide)
    | bv_omega

/-- The canonical-`y` test (`y < p`, `p = P0 + 2^64 P1 + 2^254`): the borrows of
    `y - p` kept as masks, the result's parity bit set exactly when `y < p`. -/
theorem yflag {N0 N1 : Nat} {y0 y1 y2 y3 v371 v374 v377 v379 v380 v381 v382 v383 v384 v385 v386 v387
      v390 v392 v393 v394 v395 : Word}
    (v371_def : (if (y0 + BitVec.ofNat 64 N0).ult y0 = true then 1#64 else 0#64) = v371)
    (v374_def : (18446744073709551615#64 + v371).sshiftRight 63 = v374)
    (v377_def : (if (y1 + BitVec.ofNat 64 N1).ult y1 = true then 1#64 else 0#64) = v377)
    (v379_def : 18446744073709551615#64 + (v377 + v374) = v379)
    (v380_def : y1 + (BitVec.ofNat 64 N1 + v374) = v380)
    (v381_def : (if v380.ult (y1 + BitVec.ofNat 64 N1) = true then 1#64 else 0#64) = v381)
    (v382_def : v379 + v381 = v382)
    (v383_def : v382.sshiftRight 63 = v383)
    (v384_def : v383 + y2 = v384)
    (v385_def : (if v384.ult v383 = true then 1#64 else 0#64) = v385)
    (v386_def : v383 + v385 = v386)
    (v387_def : v386.sshiftRight 63 = v387)
    (v390_def : (if (y3 + 13835058055282163712#64).ult y3 = true then 1#64 else 0#64) = v390)
    (v392_def : 1#64 + (v390 + v387) = v392)
    (v393_def : y3 + (13835058055282163712#64 + v387) = v393)
    (v394_def : (if v393.ult (y3 + 13835058055282163712#64) = true then 1#64 else 0#64) = v394)
    (v395_def : v392 + v394 = v395) (hN0 : 0 < N0 ∧ N0 < 2 ^ 64) (hN1 : 0 < N1 ∧ N1 < 2 ^ 64)
    (hf : v395 &&& 1#64 = 1#64) :
    y0.toNat + 2 ^ 64 * y1.toNat + 2 ^ 128 * y2.toNat + 2 ^ 192 * y3.toNat <
      (2 ^ 64 - N0) + 2 ^ 64 * (2 ^ 64 - N1) + 2 ^ 192 * 2 ^ 62 := by
  have h01 := ystage01 v371_def v374_def v377_def v379_def v380_def v381_def v382_def v383_def hN0 hN1
  have h2 := ystage2 h01 v384_def v385_def v386_def v387_def (by omega) (by omega)
  have h3 := ystage3 h2 v390_def v392_def v393_def v394_def v395_def (by omega) hf
  omega

end Cases.Zip2005
