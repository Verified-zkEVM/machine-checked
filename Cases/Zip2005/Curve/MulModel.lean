/-
  Cases.Zip2005.MulModel

  The model of `Ep::mul` (`Cases.Zip2005.Mul`) and, path by path, the facts that turn
  the executor's atoms at its returns into it.
-/

import Cases.Zip2005.Curve.ScalarMul
import Cases.Zip2005.Curve.MulTail
import Cases.Zip2005.Field.Fq

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel AsmVerif.RiscV.Sym

/-- The initial accumulator `Q = (p - 1, 2)` (read-only data at `0x78013890`). -/
def Qw : List Word := [1#64, 0x992d30ed00000000#64, 0x224698fc094cf91b#64, 0#64,
  0x4000000000000000#64, 2#64, 0#64, 0#64, 0#64]

/-- `-Q = (p - 1, p - 2)`, built on the stack after the loop. -/
def negQw : List Word := [1#64, 0x992d30ed00000000#64, 0x224698fc094cf91b#64, 0#64,
  0x4000000000000000#64, 0x992d30ecffffffff#64, 0x224698fc094cf91b#64, 0#64,
  0x4000000000000000#64]

section model
variable (pt k : List Word)

def ptX : Nat := leLimbsToNat [pt[0]!, pt[1]!, pt[2]!, pt[3]!]
def ptY : Nat := leLimbsToNat [pt[4]!, pt[5]!, pt[6]!, pt[7]!]
def ptZ : Nat := leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!]

/-- The base: the affine point, coordinates out of Montgomery form, tag 1. -/
def mulBase : List Word :=
  1#64 :: (natToLeLimbs 4 ((Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).1 * Fp.rInv % Fp.p) ++
    natToLeLimbs 4 ((Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).2 * Fp.rInv % Fp.p))

/-- The scalar's canonical limbs. -/
def mulScalar : List Word := natToLeLimbs 4 (leLimbsToNat k * Fq.rInv % Fq.q)

/-- The sum after the loop, `Q + [k] base - Q`. -/
def mulSum : List Word :=
  completeAddW (mulLoop (scalarBit (mulScalar k)) 0 255 Qw (mulBase pt)).1 negQw

/-- The result: twelve doublewords `(X, Y, Z)`. -/
def mulW : List Word :=
  if ptZ pt = 0 then List.replicate 12 0#64
  else if (mulSum pt k)[0]! = 0 then List.replicate 12 0#64
  else natToLeLimbs 4 (Fp.mul (leLimbsToNat [(mulSum pt k)[1]!, (mulSum pt k)[2]!,
      (mulSum pt k)[3]!, (mulSum pt k)[4]!]) Fp.R2) ++
    natToLeLimbs 4 (Fp.mul (leLimbsToNat [(mulSum pt k)[5]!, (mulSum pt k)[6]!,
      (mulSum pt k)[7]!, (mulSum pt k)[8]!]) Fp.R2) ++ natToLeLimbs 4 Fp.R

/-- What a return tells about the run: no round met the identity, and a
    non-identity sum is canonical (both asserted by the guest). -/
def mulFacts : Prop :=
  ptZ pt ≠ 0 →
    mulOk (scalarBit (mulScalar k)) 0 255 Qw (mulBase pt) ∧
    ((mulSum pt k)[0]! ≠ 0 →
      leLimbsToNat [(mulSum pt k)[1]!, (mulSum pt k)[2]!, (mulSum pt k)[3]!, (mulSum pt k)[4]!] < Fp.p ∧
      leLimbsToNat [(mulSum pt k)[5]!, (mulSum pt k)[6]!, (mulSum pt k)[7]!, (mulSum pt k)[8]!] < Fp.p)

end model

theorem length_mulW (pt k : List Word) : (mulW pt k).length = 12 := by
  unfold mulW
  split_ifs
  · exact List.length_replicate
  · exact List.length_replicate
  · rw [List.length_append, List.length_append, length_natToLeLimbs, length_natToLeLimbs,
      length_natToLeLimbs]

/-- A flag bit survives the byte round trip. -/
theorem flag_byte (x : Word) :
    BitVec.zeroExtend 64 (BitVec.truncate 8 (x &&& 1#64)) &&& 255#64 = x &&& 1#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth]
  by_cases h : i = 0
  · subst h; simp
  · have : (1#64).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]
      simp only [hi, decide_true, Bool.true_and]
      rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp; omega
    simp [this]

theorem limbs4 (z0 z1 z2 z3 : Word) :
    leLimbsToNat [z0, z1, z2, z3] = z0.toNat + 2^64 * z1.toNat + 2^128 * z2.toNat + 2^192 * z3.toNat := by
  simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring

theorem limbs_ne_zero {z0 z1 z2 z3 : Word} (h : ¬(z0 = 0#64 ∧ z1 = 0#64 ∧ z2 = 0#64 ∧ z3 = 0#64)) :
    leLimbsToNat [z0, z1, z2, z3] ≠ 0 := by
  rw [limbs4]; intro e; apply h; refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem limbs_eq_zero {z0 z1 z2 z3 : Word} (h : z0 = 0#64 ∧ z1 = 0#64 ∧ z2 = 0#64 ∧ z3 = 0#64) :
    leLimbsToNat [z0, z1, z2, z3] = 0 := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl

theorem cells_R : [3780891978758094845#64, 11037255111966004397#64, 18446744073709551615#64,
    4611686018427387903#64] = natToLeLimbs 4 Fp.R := by decide +kernel

theorem toAffine_R (X Y : Nat) : Fp.toAffine X Y Fp.R = (X, Y) := by
  simp [Fp.toAffine]

theorem toAffine_lt {X Y Z : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    (Fp.toAffine X Y Z).1 < 2 ^ 256 ∧ (Fp.toAffine X Y Z).2 < 2 ^ 256 := by
  have := Fp.p_lt
  unfold Fp.toAffine
  by_cases hR : Z = Fp.R
  · rw [if_pos hR]; exact ⟨hX, hY⟩
  · rw [if_neg hR]
    dsimp only
    by_cases h0 : (if Z = 0 then 0 else Fp.invert Z) = 0
    · rw [if_pos h0]; exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _⟩
    · rw [if_neg h0]; exact ⟨lt_trans (Fp.mul_lt _ _) this, lt_trans (Fp.mul_lt _ _) this⟩

/-- The guest's in-line `from_repr` (`x R2`, then a Montgomery product by one). -/
theorem cells_mulR2 {a0 a1 a2 a3 : Word} {acc1 acc2 : Nat}
    (h1 : leLimbsToNat [a0, a1, a2, a3] *
        leLimbsToNat [10122100416058490895#64, 15551789045973377255#64, 8617542898466512152#64,
          679271340751763220#64] %
      leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] = acc1)
    (h2 : leLimbsToNat
          [BitVec.ofNat 64 (acc1 >>> (64 * 0)), BitVec.ofNat 64 (acc1 >>> (64 * 1)),
            BitVec.ofNat 64 (acc1 >>> (64 * 2)), BitVec.ofNat 64 (acc1 >>> (64 * 3))] *
        leLimbsToNat [14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64,
          2445952672640170197#64] %
      leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] = acc2) :
    [BitVec.ofNat 64 (acc2 >>> 0), BitVec.ofNat 64 (acc2 >>> 64), BitVec.ofNat 64 (acc2 >>> 128),
      BitVec.ofNat 64 (acc2 >>> 192)] = natToLeLimbs 4 (Fp.mul (leLimbsToNat [a0, a1, a2, a3]) Fp.R2) := by
  rw [cells4, ← h2, ← h1]
  simp only [cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_R2, Fp.limbs_mod]
  rfl

set_option maxRecDepth 4000 in
theorem mul_pathA (pt k : List Word) (hkl : k.length = 4)
    {v15 v18 v22 v23 v24 v28 v29 v33 v34 v35 v39 v40 v44 v45 v46 v50 v51 v55 v57 v58 v59 v60 v65 v66 v67 v68 v77 v78 v84 v85 v86 v90 v91 v95 v97 v101 v102 v106 v109 v110 v114 v115 v119 : Word}
    {acc141_0 : ℕ}
    {v142 v143 v144 v145 : Word}
    {acc150_0 : ℕ}
    {v151 v152 v153 v154 : Word}
    {acc223_0 : ℕ}
    {acc226_1 acc248_0 : List Word}
    {v249 : Word}
    {acc256_0 : List Word}
    (v15_def : pt[8]! = v15)
    (v18_def : (if v15.ult 1#64 = true then 1#64 else 0#64) = v18)
    (v22_def : pt[9]! = v22)
    (v23_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v18) = v23)
    (v24_def : (if v22.ult 1#64 = true then 1#64 else 0#64) = v24)
    (v28_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v24) &&& v23 = v28)
    (v29_def : v28 &&& 255#64 = v29)
    (v33_def : pt[10]! = v33)
    (v34_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v29) = v34)
    (v35_def : (if v33.ult 1#64 = true then 1#64 else 0#64) = v35)
    (v39_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v35) &&& v34 = v39)
    (v40_def : v39 &&& 255#64 = v40)
    (v44_def : pt[11]! = v44)
    (v45_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v40) = v45)
    (v46_def : (if v44.ult 1#64 = true then 1#64 else 0#64) = v46)
    (v50_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v46) &&& v45 = v50)
    (v51_def : v50 &&& 255#64 = v51)
    (v55_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v51) &&& 255#64 = v55)
    (hbr56 : (v55 == 0#64) = true)
    (v57_def : pt[0]! = v57)
    (v58_def : pt[1]! = v58)
    (v59_def : pt[2]! = v59)
    (v60_def : pt[3]! = v60)
    (v65_def : pt[4]! = v65)
    (v66_def : pt[5]! = v66)
    (v67_def : pt[6]! = v67)
    (v68_def : pt[7]! = v68)
    (v77_def : v15 ^^^ 3780891978758094845#64 = v77)
    (v78_def : (if v77.ult 1#64 = true then 1#64 else 0#64) = v78)
    (v84_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v78) = v84)
    (v85_def : v22 ^^^ 11037255111966004397#64 = v85)
    (v86_def : (if v85.ult 1#64 = true then 1#64 else 0#64) = v86)
    (v90_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v86) &&& v84 = v90)
    (v91_def : v90 &&& 255#64 = v91)
    (v95_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v91) = v95)
    (v97_def : (if (v33 + 1#64).ult 1#64 = true then 1#64 else 0#64) = v97)
    (v101_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v97) &&& v95 = v101)
    (v102_def : v101 &&& 255#64 = v102)
    (v106_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v102) = v106)
    (v109_def : v44 ^^^ 4611686018427387903#64 = v109)
    (v110_def : (if v109.ult 1#64 = true then 1#64 else 0#64) = v110)
    (v114_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v110) &&& v106 = v114)
    (v115_def : v114 &&& 255#64 = v115)
    (v119_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v115) &&& 255#64 = v119)
    (hbr120 : (v119 != 0#64) = true)
    (acc141_0_def : leLimbsToNat [v57, v58, v59, v60] * Fp.rInv % Fp.p = acc141_0)
    (v142_def : BitVec.ofNat 64 (acc141_0 >>> 0) = v142)
    (v143_def : BitVec.ofNat 64 (acc141_0 >>> 64) = v143)
    (v144_def : BitVec.ofNat 64 (acc141_0 >>> 128) = v144)
    (v145_def : BitVec.ofNat 64 (acc141_0 >>> 192) = v145)
    (acc150_0_def : leLimbsToNat [v65, v66, v67, v68] * Fp.rInv % Fp.p = acc150_0)
    (v151_def : BitVec.ofNat 64 (acc150_0 >>> 0) = v151)
    (v152_def : BitVec.ofNat 64 (acc150_0 >>> 64) = v152)
    (v153_def : BitVec.ofNat 64 (acc150_0 >>> 128) = v153)
    (v154_def : BitVec.ofNat 64 (acc150_0 >>> 192) = v154)
    (acc223_0_def : leLimbsToNat [k[0]!, k[1]!, k[2]!, k[3]!] * Fq.rInv % Fq.q = acc223_0)
    (post226_12 : (mulLoop
            (scalarBit
              [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)), BitVec.ofNat 64 (acc223_0 >>> (64 * 1)),
                BitVec.ofNat 64 (acc223_0 >>> (64 * 2)), BitVec.ofNat 64 (acc223_0 >>> (64 * 3))])
            0 255
            [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
            [1#64, v142, v143, v144, v145, v151, v152, v153, v154]).1.length =
      9)
    (post226_15 : mulOk
      (scalarBit
        [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)), BitVec.ofNat 64 (acc223_0 >>> (64 * 1)),
          BitVec.ofNat 64 (acc223_0 >>> (64 * 2)), BitVec.ofNat 64 (acc223_0 >>> (64 * 3))])
      0 255 [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
      [1#64, v142, v143, v144, v145, v151, v152, v153, v154])
    (acc226_1_def : (mulLoop
          (scalarBit
            [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)), BitVec.ofNat 64 (acc223_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc223_0 >>> (64 * 2)), BitVec.ofNat 64 (acc223_0 >>> (64 * 3))])
          0 255
          [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
          [1#64, v142, v143, v144, v145, v151, v152, v153, v154]).1 =
      acc226_1)
    (acc248_0_def : completeAddW
        [acc226_1[0]!, acc226_1[1]!, acc226_1[2]!, acc226_1[3]!, acc226_1[4]!, acc226_1[5]!, acc226_1[6]!, acc226_1[7]!,
          acc226_1[8]!]
        [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 11037532056220336127#64,
          2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc248_0)
    (v249_def : acc248_0[0]! = v249)
    (hbr250 : (v249 == 0#64) = true)
    (acc256_0_def : List.replicate 12 0#64 = acc256_0) :
    ([acc256_0[0]!, acc256_0[1]!, acc256_0[2]!, acc256_0[3]!, acc256_0[4]!, acc256_0[5]!, acc256_0[6]!, acc256_0[7]!,
    acc256_0[8]!, acc256_0[9]!, acc256_0[10]!, acc256_0[11]!]) = mulW pt k ∧ mulFacts pt k := by
  subst v15_def v22_def v33_def v44_def v57_def v58_def v59_def v60_def v65_def v66_def v67_def v68_def v249_def
  have hz := zflag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def
    v46_def v50_def v51_def v55_def
  have hZ0 : ptZ pt ≠ 0 := by
    apply limbs_ne_zero; intro h; rw [if_pos h] at hz; rw [hz] at hbr56; exact absurd hbr56 (by decide)
  have hr := rflag v77_def v78_def v84_def v85_def v86_def v90_def v91_def v95_def v97_def v101_def
    v102_def v106_def v109_def v110_def v114_def v115_def v119_def
  have hZR : ptZ pt = Fp.R := by
    have h : pt[8]! = 3780891978758094845#64 ∧ pt[9]! = 11037255111966004397#64 ∧
        pt[10]! = 18446744073709551615#64 ∧ pt[11]! = 4611686018427387903#64 := by
      by_contra h; rw [if_neg h] at hr; rw [hr] at hbr120; exact absurd hbr120 (by decide)
    obtain ⟨e0, e1, e2, e3⟩ := h
    show leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!] = Fp.R
    rw [e0, e1, e2, e3]; exact Fp.limbs_R
  have hbase : mulBase pt = [1#64, v142, v143, v144, v145, v151, v152, v153, v154] := by
    rw [mulBase, hZR, toAffine_R]
    dsimp only [ptX, ptY]
    rw [acc141_0_def, acc150_0_def, ← cells4, ← cells4, v142_def, v143_def, v144_def, v145_def,
      v151_def, v152_def, v153_def, v154_def]
    rfl
  have hscal : mulScalar k = [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)),
      BitVec.ofNat 64 (acc223_0 >>> (64 * 1)), BitVec.ofNat 64 (acc223_0 >>> (64 * 2)),
      BitVec.ofNat 64 (acc223_0 >>> (64 * 3))] := by
    rw [mulScalar, cells4', ← acc223_0_def, list4_eta hkl]
  have hl : acc226_1.length = 9 := by rw [← acc226_1_def]; exact post226_12
  have hsum : mulSum pt k = acc248_0 := by
    rw [mulSum, hscal, hbase, ← acc248_0_def, list9_eta hl, ← acc226_1_def]; rfl
  have htag : (mulSum pt k)[0]! = 0 := by rw [hsum]; simpa using hbr250
  refine ⟨?_, fun _ => ⟨?_, fun h => absurd htag h⟩⟩
  · rw [mulW, if_neg hZ0, if_pos htag, ← acc256_0_def]; rfl
  · rw [hscal, hbase]; exact post226_15

set_option maxRecDepth 4000 in
theorem mul_pathB (pt k : List Word) (hkl : k.length = 4)
    {v15 v18 v22 v23 v24 v28 v29 v33 v34 v35 v39 v40 v44 v45 v46 v50 v51 v55 v57 v58 v59 v60 v65 v66 v67 v68 v77 v78 v84 v85 v86 v90 v91 v95 v97 v101 v102 v106 v109 v110 v114 v115 v119 : Word}
    {acc141_0 : ℕ}
    {v142 v143 v144 v145 : Word}
    {acc150_0 : ℕ}
    {v151 v152 v153 v154 : Word}
    {acc223_0 : ℕ}
    {acc226_1 acc248_0 : List Word}
    {v249 v263 v268 v269 v270 v271 v274 v276 v277 v278 v281 v282 v284 v285 v286 v287 v288 v289 v290 v291 v294 v295 : Word}
    {acc329_0 acc348_0 : ℕ}
    {v349 v351 v353 v355 v358 v362 v365 v366 v367 v368 v371 v374 v377 v379 v380 v381 v382 v383 v384 v385 v386 v387 v390 v392 v393 v394 v395 : Word}
    {acc415_0 acc428_0 : ℕ}
    {v429 v430 v431 v432 v433 v437 : Word}
    (v15_def : pt[8]! = v15)
    (v18_def : (if v15.ult 1#64 = true then 1#64 else 0#64) = v18)
    (v22_def : pt[9]! = v22)
    (v23_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v18) = v23)
    (v24_def : (if v22.ult 1#64 = true then 1#64 else 0#64) = v24)
    (v28_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v24) &&& v23 = v28)
    (v29_def : v28 &&& 255#64 = v29)
    (v33_def : pt[10]! = v33)
    (v34_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v29) = v34)
    (v35_def : (if v33.ult 1#64 = true then 1#64 else 0#64) = v35)
    (v39_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v35) &&& v34 = v39)
    (v40_def : v39 &&& 255#64 = v40)
    (v44_def : pt[11]! = v44)
    (v45_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v40) = v45)
    (v46_def : (if v44.ult 1#64 = true then 1#64 else 0#64) = v46)
    (v50_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v46) &&& v45 = v50)
    (v51_def : v50 &&& 255#64 = v51)
    (v55_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v51) &&& 255#64 = v55)
    (hbr56 : (v55 == 0#64) = true)
    (v57_def : pt[0]! = v57)
    (v58_def : pt[1]! = v58)
    (v59_def : pt[2]! = v59)
    (v60_def : pt[3]! = v60)
    (v65_def : pt[4]! = v65)
    (v66_def : pt[5]! = v66)
    (v67_def : pt[6]! = v67)
    (v68_def : pt[7]! = v68)
    (v77_def : v15 ^^^ 3780891978758094845#64 = v77)
    (v78_def : (if v77.ult 1#64 = true then 1#64 else 0#64) = v78)
    (v84_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v78) = v84)
    (v85_def : v22 ^^^ 11037255111966004397#64 = v85)
    (v86_def : (if v85.ult 1#64 = true then 1#64 else 0#64) = v86)
    (v90_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v86) &&& v84 = v90)
    (v91_def : v90 &&& 255#64 = v91)
    (v95_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v91) = v95)
    (v97_def : (if (v33 + 1#64).ult 1#64 = true then 1#64 else 0#64) = v97)
    (v101_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v97) &&& v95 = v101)
    (v102_def : v101 &&& 255#64 = v102)
    (v106_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v102) = v106)
    (v109_def : v44 ^^^ 4611686018427387903#64 = v109)
    (v110_def : (if v109.ult 1#64 = true then 1#64 else 0#64) = v110)
    (v114_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v110) &&& v106 = v114)
    (v115_def : v114 &&& 255#64 = v115)
    (v119_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v115) &&& 255#64 = v119)
    (hbr120 : (v119 != 0#64) = true)
    (acc141_0_def : leLimbsToNat [v57, v58, v59, v60] * Fp.rInv % Fp.p = acc141_0)
    (v142_def : BitVec.ofNat 64 (acc141_0 >>> 0) = v142)
    (v143_def : BitVec.ofNat 64 (acc141_0 >>> 64) = v143)
    (v144_def : BitVec.ofNat 64 (acc141_0 >>> 128) = v144)
    (v145_def : BitVec.ofNat 64 (acc141_0 >>> 192) = v145)
    (acc150_0_def : leLimbsToNat [v65, v66, v67, v68] * Fp.rInv % Fp.p = acc150_0)
    (v151_def : BitVec.ofNat 64 (acc150_0 >>> 0) = v151)
    (v152_def : BitVec.ofNat 64 (acc150_0 >>> 64) = v152)
    (v153_def : BitVec.ofNat 64 (acc150_0 >>> 128) = v153)
    (v154_def : BitVec.ofNat 64 (acc150_0 >>> 192) = v154)
    (acc223_0_def : leLimbsToNat [k[0]!, k[1]!, k[2]!, k[3]!] * Fq.rInv % Fq.q = acc223_0)
    (post226_12 : (mulLoop
            (scalarBit
              [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)), BitVec.ofNat 64 (acc223_0 >>> (64 * 1)),
                BitVec.ofNat 64 (acc223_0 >>> (64 * 2)), BitVec.ofNat 64 (acc223_0 >>> (64 * 3))])
            0 255
            [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
            [1#64, v142, v143, v144, v145, v151, v152, v153, v154]).1.length =
      9)
    (post226_15 : mulOk
      (scalarBit
        [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)), BitVec.ofNat 64 (acc223_0 >>> (64 * 1)),
          BitVec.ofNat 64 (acc223_0 >>> (64 * 2)), BitVec.ofNat 64 (acc223_0 >>> (64 * 3))])
      0 255 [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
      [1#64, v142, v143, v144, v145, v151, v152, v153, v154])
    (acc226_1_def : (mulLoop
          (scalarBit
            [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)), BitVec.ofNat 64 (acc223_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc223_0 >>> (64 * 2)), BitVec.ofNat 64 (acc223_0 >>> (64 * 3))])
          0 255
          [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
          [1#64, v142, v143, v144, v145, v151, v152, v153, v154]).1 =
      acc226_1)
    (acc248_0_def : completeAddW
        [acc226_1[0]!, acc226_1[1]!, acc226_1[2]!, acc226_1[3]!, acc226_1[4]!, acc226_1[5]!, acc226_1[6]!, acc226_1[7]!,
          acc226_1[8]!]
        [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 11037532056220336127#64,
          2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc248_0)
    (v249_def : acc248_0[0]! = v249)
    (hbr250 : ¬(v249 == 0#64) = true)
    (v263_def : acc248_0[0]! = v263)
    (hbr264 : ¬(v263 == 0#64) = true)
    (v268_def : acc248_0[1]! = v268)
    (v269_def : acc248_0[2]! = v269)
    (v270_def : acc248_0[3]! = v270)
    (v271_def : acc248_0[4]! = v271)
    (v274_def : (if (v268 + 7409212017489215487#64).ult v268 = true then 1#64 else 0#64) = v274)
    (v276_def : v269 + (v274 + 18446744073709551615#64) = v276)
    (v277_def : (if v276.ult v269 = true then 1#64 else 0#64) = v277)
    (v278_def : v274 + (18446744073709551615#64 + v277) = v278)
    (v281_def : (if (v276 + 15976914419795035877#64).ult v276 = true then 1#64 else 0#64) = v281)
    (v282_def : v278 + v281 = v282)
    (v284_def : (v282 + 18446744073709551615#64).sshiftRight 63 = v284)
    (v285_def : v284 + v270 = v285)
    (v286_def : (if v285.ult v284 = true then 1#64 else 0#64) = v286)
    (v287_def : v284 + v286 = v287)
    (v288_def : v287.sshiftRight 63 = v288)
    (v289_def : v271 + v288 = v289)
    (v290_def : (if v289.ult v271 = true then 1#64 else 0#64) = v290)
    (v291_def : v288 + v290 = v291)
    (v294_def : (if (v289 + 13835058055282163712#64).ult v289 = true then 1#64 else 0#64) = v294)
    (v295_def : v291 + v294 = v295)
    (acc329_0_def : leLimbsToNat [v268, v269, v270, v271] *
          leLimbsToNat [10122100416058490895#64, 15551789045973377255#64, 8617542898466512152#64, 679271340751763220#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc329_0)
    (acc348_0_def : leLimbsToNat
            [BitVec.ofNat 64 (acc329_0 >>> (64 * 0)), BitVec.ofNat 64 (acc329_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc329_0 >>> (64 * 2)), BitVec.ofNat 64 (acc329_0 >>> (64 * 3))] *
          leLimbsToNat [14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64, 2445952672640170197#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc348_0)
    (v349_def : BitVec.ofNat 64 (acc348_0 >>> 0) = v349)
    (v351_def : BitVec.ofNat 64 (acc348_0 >>> 64) = v351)
    (v353_def : BitVec.ofNat 64 (acc348_0 >>> 128) = v353)
    (v355_def : BitVec.ofNat 64 (acc348_0 >>> 192) = v355)
    (v358_def : v295 + 1#64 &&& 1#64 = v358)
    (v362_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v358) &&& 255#64 = v362)
    (hbr364 : ¬(v362 != 1#64) = true)
    (v365_def : acc248_0[5]! = v365)
    (v366_def : acc248_0[6]! = v366)
    (v367_def : acc248_0[7]! = v367)
    (v368_def : acc248_0[8]! = v368)
    (v371_def : (if (v365 + 7409212017489215487#64).ult v365 = true then 1#64 else 0#64) = v371)
    (v374_def : (18446744073709551615#64 + v371).sshiftRight 63 = v374)
    (v377_def : (if (v366 + 15976914419795035877#64).ult v366 = true then 1#64 else 0#64) = v377)
    (v379_def : 18446744073709551615#64 + (v377 + v374) = v379)
    (v380_def : v366 + (15976914419795035877#64 + v374) = v380)
    (v381_def : (if v380.ult (v366 + 15976914419795035877#64) = true then 1#64 else 0#64) = v381)
    (v382_def : v379 + v381 = v382)
    (v383_def : v382.sshiftRight 63 = v383)
    (v384_def : v383 + v367 = v384)
    (v385_def : (if v384.ult v383 = true then 1#64 else 0#64) = v385)
    (v386_def : v383 + v385 = v386)
    (v387_def : v386.sshiftRight 63 = v387)
    (v390_def : (if (v368 + 13835058055282163712#64).ult v368 = true then 1#64 else 0#64) = v390)
    (v392_def : 1#64 + (v390 + v387) = v392)
    (v393_def : v368 + (13835058055282163712#64 + v387) = v393)
    (v394_def : (if v393.ult (v368 + 13835058055282163712#64) = true then 1#64 else 0#64) = v394)
    (v395_def : v392 + v394 = v395)
    (acc415_0_def : leLimbsToNat [v365, v366, v367, v368] *
          leLimbsToNat [10122100416058490895#64, 15551789045973377255#64, 8617542898466512152#64, 679271340751763220#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc415_0)
    (acc428_0_def : leLimbsToNat
            [BitVec.ofNat 64 (acc415_0 >>> (64 * 0)), BitVec.ofNat 64 (acc415_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc415_0 >>> (64 * 2)), BitVec.ofNat 64 (acc415_0 >>> (64 * 3))] *
          leLimbsToNat [14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64, 2445952672640170197#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc428_0)
    (v429_def : BitVec.ofNat 64 (acc428_0 >>> 0) = v429)
    (v430_def : BitVec.ofNat 64 (acc428_0 >>> 64) = v430)
    (v431_def : BitVec.ofNat 64 (acc428_0 >>> 128) = v431)
    (v432_def : BitVec.ofNat 64 (acc428_0 >>> 192) = v432)
    (v433_def : v395 &&& 1#64 = v433)
    (v437_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v433) &&& 255#64 = v437)
    (hbr440 : ¬(v437 != 1#64) = true) :
    ([v349, v351, v353, v355, v429, v430, v431, v432, 3780891978758094845#64, 11037255111966004397#64,
    18446744073709551615#64, 4611686018427387903#64]) = mulW pt k ∧ mulFacts pt k := by
  subst v15_def v22_def v33_def v44_def v57_def v58_def v59_def v60_def v65_def v66_def v67_def v68_def v249_def v263_def v268_def v269_def v270_def v271_def v365_def v366_def v367_def v368_def
  have hz := zflag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def
    v46_def v50_def v51_def v55_def
  have hZ0 : ptZ pt ≠ 0 := by
    apply limbs_ne_zero; intro h; rw [if_pos h] at hz; rw [hz] at hbr56; exact absurd hbr56 (by decide)
  have hr := rflag v77_def v78_def v84_def v85_def v86_def v90_def v91_def v95_def v97_def v101_def
    v102_def v106_def v109_def v110_def v114_def v115_def v119_def
  have hZR : ptZ pt = Fp.R := by
    have h : pt[8]! = 3780891978758094845#64 ∧ pt[9]! = 11037255111966004397#64 ∧
        pt[10]! = 18446744073709551615#64 ∧ pt[11]! = 4611686018427387903#64 := by
      by_contra h; rw [if_neg h] at hr; rw [hr] at hbr120; exact absurd hbr120 (by decide)
    obtain ⟨e0, e1, e2, e3⟩ := h
    show leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!] = Fp.R
    rw [e0, e1, e2, e3]; exact Fp.limbs_R
  have hbase : mulBase pt = [1#64, v142, v143, v144, v145, v151, v152, v153, v154] := by
    rw [mulBase, hZR, toAffine_R]
    dsimp only [ptX, ptY]
    rw [acc141_0_def, acc150_0_def, ← cells4, ← cells4, v142_def, v143_def, v144_def, v145_def,
      v151_def, v152_def, v153_def, v154_def]
    rfl
  have hscal : mulScalar k = [BitVec.ofNat 64 (acc223_0 >>> (64 * 0)),
      BitVec.ofNat 64 (acc223_0 >>> (64 * 1)), BitVec.ofNat 64 (acc223_0 >>> (64 * 2)),
      BitVec.ofNat 64 (acc223_0 >>> (64 * 3))] := by
    rw [mulScalar, cells4', ← acc223_0_def, list4_eta hkl]
  have hl : acc226_1.length = 9 := by rw [← acc226_1_def]; exact post226_12
  have hsum : mulSum pt k = acc248_0 := by
    rw [mulSum, hscal, hbase, ← acc248_0_def, list9_eta hl, ← acc226_1_def]; rfl
  have fl := lt_flag (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v274_def v276_def v277_def v278_def v281_def v282_def v284_def v285_def v286_def
    v287_def v288_def v289_def v290_def v291_def v294_def v295_def
  dsimp only at fl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide]
    at fl
  have hX : leLimbsToNat [acc248_0[1]!, acc248_0[2]!, acc248_0[3]!, acc248_0[4]!] < Fp.p := by
    rw [limbs4]; by_contra hc
    have e : v295 = 1#64 := BitVec.eq_of_toNat_eq (fl.2 (by omega))
    rw [← v362_def, ← v358_def, flag_byte, e] at hbr364; exact absurd hbr364 (by decide)
  have hY : leLimbsToNat [acc248_0[5]!, acc248_0[6]!, acc248_0[7]!, acc248_0[8]!] < Fp.p := by
    have hf : v395 &&& 1#64 = 1#64 := by
      rw [← v437_def, ← v433_def, flag_byte] at hbr440; simpa using hbr440
    have := yflag (N0 := 7409212017489215487) (N1 := 15976914419795035877) v371_def v374_def
      v377_def v379_def v380_def v381_def v382_def v383_def v384_def v385_def v386_def v387_def
      v390_def v392_def v393_def v394_def v395_def (by decide) (by decide) hf
    rw [limbs4]; exact lt_of_lt_of_eq this (by decide)
  have htag : ¬(mulSum pt k)[0]! = 0 := by rw [hsum]; simpa using hbr250
  refine ⟨?_, fun _ => ⟨?_, fun _ => ⟨?_, ?_⟩⟩⟩
  · rw [mulW, if_neg hZ0, if_neg htag, hsum, ← cells_mulR2 acc329_0_def acc348_0_def,
      ← cells_mulR2 acc415_0_def acc428_0_def, ← cells_R, v349_def, v351_def, v353_def, v355_def,
      v429_def, v430_def, v431_def, v432_def]
    rfl
  · rw [hscal, hbase]; exact post226_15
  · rw [hsum]; exact hX
  · rw [hsum]; exact hY

set_option maxRecDepth 4000 in
theorem mul_pathC (pt k : List Word) (hkl : k.length = 4)
    {v15 v18 v22 v23 v24 v28 v29 v33 v34 v35 v39 v40 v44 v45 v46 v50 v51 v55 v135 v136 v137 v138 v143 v144 v145 v146 : Word}
    {acc171_0 : ℕ}
    {v172 v173 v174 v175 : Word}
    {acc180_0 : ℕ}
    {v181 v182 v183 v184 : Word}
    {acc253_0 : ℕ}
    {acc256_1 acc278_0 : List Word}
    {v279 : Word}
    {acc286_0 : List Word}
    (v15_def : pt[8]! = v15)
    (v18_def : (if v15.ult 1#64 = true then 1#64 else 0#64) = v18)
    (v22_def : pt[9]! = v22)
    (v23_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v18) = v23)
    (v24_def : (if v22.ult 1#64 = true then 1#64 else 0#64) = v24)
    (v28_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v24) &&& v23 = v28)
    (v29_def : v28 &&& 255#64 = v29)
    (v33_def : pt[10]! = v33)
    (v34_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v29) = v34)
    (v35_def : (if v33.ult 1#64 = true then 1#64 else 0#64) = v35)
    (v39_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v35) &&& v34 = v39)
    (v40_def : v39 &&& 255#64 = v40)
    (v44_def : pt[11]! = v44)
    (v45_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v40) = v45)
    (v46_def : (if v44.ult 1#64 = true then 1#64 else 0#64) = v46)
    (v50_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v46) &&& v45 = v50)
    (v51_def : v50 &&& 255#64 = v51)
    (v55_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v51) &&& 255#64 = v55)
    (hbr56 : (v55 == 0#64) = true)
    (v135_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          0) =
      v135)
    (v136_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          64) =
      v136)
    (v137_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          128) =
      v137)
    (v138_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          192) =
      v138)
    (v143_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          0) =
      v143)
    (v144_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          64) =
      v144)
    (v145_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          128) =
      v145)
    (v146_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          192) =
      v146)
    (acc171_0_def : leLimbsToNat [v135, v136, v137, v138] * Fp.rInv % Fp.p = acc171_0)
    (v172_def : BitVec.ofNat 64 (acc171_0 >>> 0) = v172)
    (v173_def : BitVec.ofNat 64 (acc171_0 >>> 64) = v173)
    (v174_def : BitVec.ofNat 64 (acc171_0 >>> 128) = v174)
    (v175_def : BitVec.ofNat 64 (acc171_0 >>> 192) = v175)
    (acc180_0_def : leLimbsToNat [v143, v144, v145, v146] * Fp.rInv % Fp.p = acc180_0)
    (v181_def : BitVec.ofNat 64 (acc180_0 >>> 0) = v181)
    (v182_def : BitVec.ofNat 64 (acc180_0 >>> 64) = v182)
    (v183_def : BitVec.ofNat 64 (acc180_0 >>> 128) = v183)
    (v184_def : BitVec.ofNat 64 (acc180_0 >>> 192) = v184)
    (acc253_0_def : leLimbsToNat [k[0]!, k[1]!, k[2]!, k[3]!] * Fq.rInv % Fq.q = acc253_0)
    (post256_12 : (mulLoop
            (scalarBit
              [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)), BitVec.ofNat 64 (acc253_0 >>> (64 * 1)),
                BitVec.ofNat 64 (acc253_0 >>> (64 * 2)), BitVec.ofNat 64 (acc253_0 >>> (64 * 3))])
            0 255
            [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
            [1#64, v172, v173, v174, v175, v181, v182, v183, v184]).1.length =
      9)
    (post256_15 : mulOk
      (scalarBit
        [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)), BitVec.ofNat 64 (acc253_0 >>> (64 * 1)),
          BitVec.ofNat 64 (acc253_0 >>> (64 * 2)), BitVec.ofNat 64 (acc253_0 >>> (64 * 3))])
      0 255 [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
      [1#64, v172, v173, v174, v175, v181, v182, v183, v184])
    (acc256_1_def : (mulLoop
          (scalarBit
            [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)), BitVec.ofNat 64 (acc253_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc253_0 >>> (64 * 2)), BitVec.ofNat 64 (acc253_0 >>> (64 * 3))])
          0 255
          [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
          [1#64, v172, v173, v174, v175, v181, v182, v183, v184]).1 =
      acc256_1)
    (acc278_0_def : completeAddW
        [acc256_1[0]!, acc256_1[1]!, acc256_1[2]!, acc256_1[3]!, acc256_1[4]!, acc256_1[5]!, acc256_1[6]!, acc256_1[7]!,
          acc256_1[8]!]
        [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 11037532056220336127#64,
          2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc278_0)
    (v279_def : acc278_0[0]! = v279)
    (hbr280 : (v279 == 0#64) = true)
    (acc286_0_def : List.replicate 12 0#64 = acc286_0) :
    ([acc286_0[0]!, acc286_0[1]!, acc286_0[2]!, acc286_0[3]!, acc286_0[4]!, acc286_0[5]!, acc286_0[6]!, acc286_0[7]!,
    acc286_0[8]!, acc286_0[9]!, acc286_0[10]!, acc286_0[11]!]) = mulW pt k ∧ mulFacts pt k := by
  subst v15_def v22_def v33_def v44_def v279_def
  have hz := zflag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def
    v46_def v50_def v51_def v55_def
  have hZ0 : ptZ pt ≠ 0 := by
    apply limbs_ne_zero; intro h; rw [if_pos h] at hz; rw [hz] at hbr56; exact absurd hbr56 (by decide)
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at v135_def v136_def v137_def v138_def v143_def v144_def v145_def v146_def
  have hA := toAffine_lt (X := ptX pt) (Y := ptY pt) (Z := ptZ pt) (leLimbsToNat_lt _) (leLimbsToNat_lt _)
  have eA : leLimbsToNat [v135, v136, v137, v138] = (Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).1 := by
    rw [← v135_def, ← v136_def, ← v137_def, ← v138_def, cells4]
    exact leLimbsToNat_natToLeLimbs 4 _ hA.1
  have eB : leLimbsToNat [v143, v144, v145, v146] = (Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).2 := by
    rw [← v143_def, ← v144_def, ← v145_def, ← v146_def, cells4]
    exact leLimbsToNat_natToLeLimbs 4 _ hA.2
  have hbase : mulBase pt = [1#64, v172, v173, v174, v175, v181, v182, v183, v184] := by
    rw [mulBase, ← eA, ← eB, acc171_0_def, acc180_0_def, ← cells4, ← cells4, v172_def, v173_def,
      v174_def, v175_def, v181_def, v182_def, v183_def, v184_def]
    rfl
  have hscal : mulScalar k = [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)),
      BitVec.ofNat 64 (acc253_0 >>> (64 * 1)), BitVec.ofNat 64 (acc253_0 >>> (64 * 2)),
      BitVec.ofNat 64 (acc253_0 >>> (64 * 3))] := by
    rw [mulScalar, cells4', ← acc253_0_def, list4_eta hkl]
  have hl : acc256_1.length = 9 := by rw [← acc256_1_def]; exact post256_12
  have hsum : mulSum pt k = acc278_0 := by
    rw [mulSum, hscal, hbase, ← acc278_0_def, list9_eta hl, ← acc256_1_def]; rfl
  have htag : (mulSum pt k)[0]! = 0 := by rw [hsum]; simpa using hbr280
  refine ⟨?_, fun _ => ⟨?_, fun h => absurd htag h⟩⟩
  · rw [mulW, if_neg hZ0, if_pos htag, ← acc286_0_def]; rfl
  · rw [hscal, hbase]; exact post256_15

set_option maxRecDepth 4000 in
theorem mul_pathD (pt k : List Word) (hkl : k.length = 4)
    {v15 v18 v22 v23 v24 v28 v29 v33 v34 v35 v39 v40 v44 v45 v46 v50 v51 v55 v135 v136 v137 v138 v143 v144 v145 v146 : Word}
    {acc171_0 : ℕ}
    {v172 v173 v174 v175 : Word}
    {acc180_0 : ℕ}
    {v181 v182 v183 v184 : Word}
    {acc253_0 : ℕ}
    {acc256_1 acc278_0 : List Word}
    {v279 v293 v298 v299 v300 v301 v304 v306 v307 v308 v311 v312 v314 v315 v316 v317 v318 v319 v320 v321 v324 v325 : Word}
    {acc359_0 acc378_0 : ℕ}
    {v379 v381 v383 v385 v388 v392 v395 v396 v397 v398 v401 v404 v407 v409 v410 v411 v412 v413 v414 v415 v416 v417 v420 v422 v423 v424 v425 : Word}
    {acc445_0 acc458_0 : ℕ}
    {v459 v460 v461 v462 v463 v467 : Word}
    (v15_def : pt[8]! = v15)
    (v18_def : (if v15.ult 1#64 = true then 1#64 else 0#64) = v18)
    (v22_def : pt[9]! = v22)
    (v23_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v18) = v23)
    (v24_def : (if v22.ult 1#64 = true then 1#64 else 0#64) = v24)
    (v28_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v24) &&& v23 = v28)
    (v29_def : v28 &&& 255#64 = v29)
    (v33_def : pt[10]! = v33)
    (v34_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v29) = v34)
    (v35_def : (if v33.ult 1#64 = true then 1#64 else 0#64) = v35)
    (v39_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v35) &&& v34 = v39)
    (v40_def : v39 &&& 255#64 = v40)
    (v44_def : pt[11]! = v44)
    (v45_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v40) = v45)
    (v46_def : (if v44.ult 1#64 = true then 1#64 else 0#64) = v46)
    (v50_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v46) &&& v45 = v50)
    (v51_def : v50 &&& 255#64 = v51)
    (v55_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v51) &&& 255#64 = v55)
    (hbr56 : (v55 == 0#64) = true)
    (v135_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          0) =
      v135)
    (v136_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          64) =
      v136)
    (v137_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          128) =
      v137)
    (v138_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).1 >>>
          192) =
      v138)
    (v143_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          0) =
      v143)
    (v144_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          64) =
      v144)
    (v145_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          128) =
      v145)
    (v146_def : BitVec.ofNat 64
        ((Fp.toAffine
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][0]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][1]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][2]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][3]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][4]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][5]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][6]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][7]!])
              (leLimbsToNat
                [[pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][8]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][9]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!][10]!,
                  [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!,
                      pt[11]!][11]!])).2 >>>
          192) =
      v146)
    (acc171_0_def : leLimbsToNat [v135, v136, v137, v138] * Fp.rInv % Fp.p = acc171_0)
    (v172_def : BitVec.ofNat 64 (acc171_0 >>> 0) = v172)
    (v173_def : BitVec.ofNat 64 (acc171_0 >>> 64) = v173)
    (v174_def : BitVec.ofNat 64 (acc171_0 >>> 128) = v174)
    (v175_def : BitVec.ofNat 64 (acc171_0 >>> 192) = v175)
    (acc180_0_def : leLimbsToNat [v143, v144, v145, v146] * Fp.rInv % Fp.p = acc180_0)
    (v181_def : BitVec.ofNat 64 (acc180_0 >>> 0) = v181)
    (v182_def : BitVec.ofNat 64 (acc180_0 >>> 64) = v182)
    (v183_def : BitVec.ofNat 64 (acc180_0 >>> 128) = v183)
    (v184_def : BitVec.ofNat 64 (acc180_0 >>> 192) = v184)
    (acc253_0_def : leLimbsToNat [k[0]!, k[1]!, k[2]!, k[3]!] * Fq.rInv % Fq.q = acc253_0)
    (post256_12 : (mulLoop
            (scalarBit
              [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)), BitVec.ofNat 64 (acc253_0 >>> (64 * 1)),
                BitVec.ofNat 64 (acc253_0 >>> (64 * 2)), BitVec.ofNat 64 (acc253_0 >>> (64 * 3))])
            0 255
            [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
            [1#64, v172, v173, v174, v175, v181, v182, v183, v184]).1.length =
      9)
    (post256_15 : mulOk
      (scalarBit
        [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)), BitVec.ofNat 64 (acc253_0 >>> (64 * 1)),
          BitVec.ofNat 64 (acc253_0 >>> (64 * 2)), BitVec.ofNat 64 (acc253_0 >>> (64 * 3))])
      0 255 [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
      [1#64, v172, v173, v174, v175, v181, v182, v183, v184])
    (acc256_1_def : (mulLoop
          (scalarBit
            [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)), BitVec.ofNat 64 (acc253_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc253_0 >>> (64 * 2)), BitVec.ofNat 64 (acc253_0 >>> (64 * 3))])
          0 255
          [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 2#64, 0#64, 0#64, 0#64]
          [1#64, v172, v173, v174, v175, v181, v182, v183, v184]).1 =
      acc256_1)
    (acc278_0_def : completeAddW
        [acc256_1[0]!, acc256_1[1]!, acc256_1[2]!, acc256_1[3]!, acc256_1[4]!, acc256_1[5]!, acc256_1[6]!, acc256_1[7]!,
          acc256_1[8]!]
        [1#64, 11037532056220336128#64, 2469829653914515739#64, 0#64, 4611686018427387904#64, 11037532056220336127#64,
          2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc278_0)
    (v279_def : acc278_0[0]! = v279)
    (hbr280 : ¬(v279 == 0#64) = true)
    (v293_def : acc278_0[0]! = v293)
    (hbr294 : ¬(v293 == 0#64) = true)
    (v298_def : acc278_0[1]! = v298)
    (v299_def : acc278_0[2]! = v299)
    (v300_def : acc278_0[3]! = v300)
    (v301_def : acc278_0[4]! = v301)
    (v304_def : (if (v298 + 7409212017489215487#64).ult v298 = true then 1#64 else 0#64) = v304)
    (v306_def : v299 + (v304 + 18446744073709551615#64) = v306)
    (v307_def : (if v306.ult v299 = true then 1#64 else 0#64) = v307)
    (v308_def : v304 + (18446744073709551615#64 + v307) = v308)
    (v311_def : (if (v306 + 15976914419795035877#64).ult v306 = true then 1#64 else 0#64) = v311)
    (v312_def : v308 + v311 = v312)
    (v314_def : (v312 + 18446744073709551615#64).sshiftRight 63 = v314)
    (v315_def : v314 + v300 = v315)
    (v316_def : (if v315.ult v314 = true then 1#64 else 0#64) = v316)
    (v317_def : v314 + v316 = v317)
    (v318_def : v317.sshiftRight 63 = v318)
    (v319_def : v301 + v318 = v319)
    (v320_def : (if v319.ult v301 = true then 1#64 else 0#64) = v320)
    (v321_def : v318 + v320 = v321)
    (v324_def : (if (v319 + 13835058055282163712#64).ult v319 = true then 1#64 else 0#64) = v324)
    (v325_def : v321 + v324 = v325)
    (acc359_0_def : leLimbsToNat [v298, v299, v300, v301] *
          leLimbsToNat [10122100416058490895#64, 15551789045973377255#64, 8617542898466512152#64, 679271340751763220#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc359_0)
    (acc378_0_def : leLimbsToNat
            [BitVec.ofNat 64 (acc359_0 >>> (64 * 0)), BitVec.ofNat 64 (acc359_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc359_0 >>> (64 * 2)), BitVec.ofNat 64 (acc359_0 >>> (64 * 3))] *
          leLimbsToNat [14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64, 2445952672640170197#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc378_0)
    (v379_def : BitVec.ofNat 64 (acc378_0 >>> 0) = v379)
    (v381_def : BitVec.ofNat 64 (acc378_0 >>> 64) = v381)
    (v383_def : BitVec.ofNat 64 (acc378_0 >>> 128) = v383)
    (v385_def : BitVec.ofNat 64 (acc378_0 >>> 192) = v385)
    (v388_def : v325 + 1#64 &&& 1#64 = v388)
    (v392_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v388) &&& 255#64 = v392)
    (hbr394 : ¬(v392 != 1#64) = true)
    (v395_def : acc278_0[5]! = v395)
    (v396_def : acc278_0[6]! = v396)
    (v397_def : acc278_0[7]! = v397)
    (v398_def : acc278_0[8]! = v398)
    (v401_def : (if (v395 + 7409212017489215487#64).ult v395 = true then 1#64 else 0#64) = v401)
    (v404_def : (18446744073709551615#64 + v401).sshiftRight 63 = v404)
    (v407_def : (if (v396 + 15976914419795035877#64).ult v396 = true then 1#64 else 0#64) = v407)
    (v409_def : 18446744073709551615#64 + (v407 + v404) = v409)
    (v410_def : v396 + (15976914419795035877#64 + v404) = v410)
    (v411_def : (if v410.ult (v396 + 15976914419795035877#64) = true then 1#64 else 0#64) = v411)
    (v412_def : v409 + v411 = v412)
    (v413_def : v412.sshiftRight 63 = v413)
    (v414_def : v413 + v397 = v414)
    (v415_def : (if v414.ult v413 = true then 1#64 else 0#64) = v415)
    (v416_def : v413 + v415 = v416)
    (v417_def : v416.sshiftRight 63 = v417)
    (v420_def : (if (v398 + 13835058055282163712#64).ult v398 = true then 1#64 else 0#64) = v420)
    (v422_def : 1#64 + (v420 + v417) = v422)
    (v423_def : v398 + (13835058055282163712#64 + v417) = v423)
    (v424_def : (if v423.ult (v398 + 13835058055282163712#64) = true then 1#64 else 0#64) = v424)
    (v425_def : v422 + v424 = v425)
    (acc445_0_def : leLimbsToNat [v395, v396, v397, v398] *
          leLimbsToNat [10122100416058490895#64, 15551789045973377255#64, 8617542898466512152#64, 679271340751763220#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc445_0)
    (acc458_0_def : leLimbsToNat
            [BitVec.ofNat 64 (acc445_0 >>> (64 * 0)), BitVec.ofNat 64 (acc445_0 >>> (64 * 1)),
              BitVec.ofNat 64 (acc445_0 >>> (64 * 2)), BitVec.ofNat 64 (acc445_0 >>> (64 * 3))] *
          leLimbsToNat [14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64, 2445952672640170197#64] %
        leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] =
      acc458_0)
    (v459_def : BitVec.ofNat 64 (acc458_0 >>> 0) = v459)
    (v460_def : BitVec.ofNat 64 (acc458_0 >>> 64) = v460)
    (v461_def : BitVec.ofNat 64 (acc458_0 >>> 128) = v461)
    (v462_def : BitVec.ofNat 64 (acc458_0 >>> 192) = v462)
    (v463_def : v425 &&& 1#64 = v463)
    (v467_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v463) &&& 255#64 = v467)
    (hbr470 : ¬(v467 != 1#64) = true) :
    ([v379, v381, v383, v385, v459, v460, v461, v462, 3780891978758094845#64, 11037255111966004397#64,
    18446744073709551615#64, 4611686018427387903#64]) = mulW pt k ∧ mulFacts pt k := by
  subst v15_def v22_def v33_def v44_def v279_def v293_def v298_def v299_def v300_def v301_def v395_def v396_def v397_def v398_def
  have hz := zflag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def
    v46_def v50_def v51_def v55_def
  have hZ0 : ptZ pt ≠ 0 := by
    apply limbs_ne_zero; intro h; rw [if_pos h] at hz; rw [hz] at hbr56; exact absurd hbr56 (by decide)
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at v135_def v136_def v137_def v138_def v143_def v144_def v145_def v146_def
  have hA := toAffine_lt (X := ptX pt) (Y := ptY pt) (Z := ptZ pt) (leLimbsToNat_lt _) (leLimbsToNat_lt _)
  have eA : leLimbsToNat [v135, v136, v137, v138] = (Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).1 := by
    rw [← v135_def, ← v136_def, ← v137_def, ← v138_def, cells4]
    exact leLimbsToNat_natToLeLimbs 4 _ hA.1
  have eB : leLimbsToNat [v143, v144, v145, v146] = (Fp.toAffine (ptX pt) (ptY pt) (ptZ pt)).2 := by
    rw [← v143_def, ← v144_def, ← v145_def, ← v146_def, cells4]
    exact leLimbsToNat_natToLeLimbs 4 _ hA.2
  have hbase : mulBase pt = [1#64, v172, v173, v174, v175, v181, v182, v183, v184] := by
    rw [mulBase, ← eA, ← eB, acc171_0_def, acc180_0_def, ← cells4, ← cells4, v172_def, v173_def,
      v174_def, v175_def, v181_def, v182_def, v183_def, v184_def]
    rfl
  have hscal : mulScalar k = [BitVec.ofNat 64 (acc253_0 >>> (64 * 0)),
      BitVec.ofNat 64 (acc253_0 >>> (64 * 1)), BitVec.ofNat 64 (acc253_0 >>> (64 * 2)),
      BitVec.ofNat 64 (acc253_0 >>> (64 * 3))] := by
    rw [mulScalar, cells4', ← acc253_0_def, list4_eta hkl]
  have hl : acc256_1.length = 9 := by rw [← acc256_1_def]; exact post256_12
  have hsum : mulSum pt k = acc278_0 := by
    rw [mulSum, hscal, hbase, ← acc278_0_def, list9_eta hl, ← acc256_1_def]; rfl
  have fl := lt_flag (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v304_def v306_def v307_def v308_def v311_def v312_def v314_def v315_def v316_def
    v317_def v318_def v319_def v320_def v321_def v324_def v325_def
  dsimp only at fl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide]
    at fl
  have hX : leLimbsToNat [acc278_0[1]!, acc278_0[2]!, acc278_0[3]!, acc278_0[4]!] < Fp.p := by
    rw [limbs4]; by_contra hc
    have e : v325 = 1#64 := BitVec.eq_of_toNat_eq (fl.2 (by omega))
    rw [← v392_def, ← v388_def, flag_byte, e] at hbr394; exact absurd hbr394 (by decide)
  have hY : leLimbsToNat [acc278_0[5]!, acc278_0[6]!, acc278_0[7]!, acc278_0[8]!] < Fp.p := by
    have hf : v425 &&& 1#64 = 1#64 := by
      rw [← v467_def, ← v463_def, flag_byte] at hbr470; simpa using hbr470
    have := yflag (N0 := 7409212017489215487) (N1 := 15976914419795035877) v401_def v404_def
      v407_def v409_def v410_def v411_def v412_def v413_def v414_def v415_def v416_def v417_def
      v420_def v422_def v423_def v424_def v425_def (by decide) (by decide) hf
    rw [limbs4]; exact lt_of_lt_of_eq this (by decide)
  have htag : ¬(mulSum pt k)[0]! = 0 := by rw [hsum]; simpa using hbr280
  refine ⟨?_, fun _ => ⟨?_, fun _ => ⟨?_, ?_⟩⟩⟩
  · rw [mulW, if_neg hZ0, if_neg htag, hsum, ← cells_mulR2 acc359_0_def acc378_0_def,
      ← cells_mulR2 acc445_0_def acc458_0_def, ← cells_R, v379_def, v381_def, v383_def, v385_def,
      v459_def, v460_def, v461_def, v462_def]
    rfl
  · rw [hscal, hbase]; exact post256_15
  · rw [hsum]; exact hX
  · rw [hsum]; exact hY

set_option maxRecDepth 4000 in
theorem mul_pathE (pt k : List Word)
    {v15 v18 v22 v23 v24 v28 v29 v33 v34 v35 v39 v40 v44 v45 v46 v50 v51 v55 : Word}
    {acc62_0 : List Word}
    (v15_def : pt[8]! = v15)
    (v18_def : (if v15.ult 1#64 = true then 1#64 else 0#64) = v18)
    (v22_def : pt[9]! = v22)
    (v23_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v18) = v23)
    (v24_def : (if v22.ult 1#64 = true then 1#64 else 0#64) = v24)
    (v28_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v24) &&& v23 = v28)
    (v29_def : v28 &&& 255#64 = v29)
    (v33_def : pt[10]! = v33)
    (v34_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v29) = v34)
    (v35_def : (if v33.ult 1#64 = true then 1#64 else 0#64) = v35)
    (v39_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v35) &&& v34 = v39)
    (v40_def : v39 &&& 255#64 = v40)
    (v44_def : pt[11]! = v44)
    (v45_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v40) = v45)
    (v46_def : (if v44.ult 1#64 = true then 1#64 else 0#64) = v46)
    (v50_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v46) &&& v45 = v50)
    (v51_def : v50 &&& 255#64 = v51)
    (v55_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v51) &&& 255#64 = v55)
    (hbr56 : ¬(v55 == 0#64) = true)
    (acc62_0_def : List.replicate 12 0#64 = acc62_0) :
    ([acc62_0[0]!, acc62_0[1]!, acc62_0[2]!, acc62_0[3]!, acc62_0[4]!, acc62_0[5]!, acc62_0[6]!, acc62_0[7]!,
    acc62_0[8]!, acc62_0[9]!, acc62_0[10]!, acc62_0[11]!]) = mulW pt k ∧ mulFacts pt k := by
  subst v15_def v22_def v33_def v44_def
  have hz := zflag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def
    v46_def v50_def v51_def v55_def
  have hZ : ptZ pt = 0 := by
    apply limbs_eq_zero; by_contra h; rw [if_neg h] at hz; rw [hz] at hbr56; exact absurd hbr56 (by decide)
  refine ⟨?_, fun h => absurd hZ h⟩
  rw [mulW, if_pos hZ, ← acc62_0_def]; rfl

end Cases.Zip2005
