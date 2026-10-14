/-
  Cases.Zip2005.MontTailR

  The conditional subtraction at the end of the guest's full Montgomery
  product (`Fp::from_raw`, `(a * b)` over software limbs): limbs 0–2 as in
  `Cases.Zip2005.MontTail`, but the top limb of `T` is not a word the code holds. It is
  `t7 + c₁ + c₂ + c₃` (the product's top limb plus the reduction's carries), and
  `t7 - 2^62` is formed as `t7 ||| 0xC000…` (so `t7 < 2^62`).
-/

import Cases.Zip2005.Field.MontTail

namespace Cases.Zip2005

open RiscvZkvm.Rv64

theorem eq_of_add_mul {t q s : Nat} (h : t + 2 ^ 256 * q = s) (hs : s < 2 ^ 256) : t = s := by
  omega

theorem mod_of_tail {T R m : Nat} (hT : T < 2 * m) (h1 : T < m → R = T) (h2 : m ≤ T → R + m = T) :
    R = T % m := by
  by_cases h : T < m
  · rw [h1 h, Nat.mod_eq_of_lt h]
  · have e := h2 (by omega)
    rw [← e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem or_c000 {t : Word} (ht : t.toNat < 2 ^ 62) :
    (t ||| 13835058055282163712#64).toNat = t.toNat + 13835058055282163712 := by
  have hand : t &&& 13835058055282163712#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    by_cases h : i < 62
    · rw [show (13835058055282163712#64).getLsbD i = false by
        rw [BitVec.getLsbD_ofNat]; simp only [hi, decide_true, Bool.true_and]
        rw [show (13835058055282163712 : Nat) = 3 * 2 ^ 62 by norm_num, Nat.testBit_mul_two_pow]
        simp [h]]
      simp
    · rw [BitVec.getLsbD, Nat.testBit_lt_two_pow (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand, BitVec.toNat_add, Bn.toNat_ofNat']
  omega

/-- Limb 3 of `T - p`: `v263` is the final no-borrow flag. -/
theorem tail_s3r {t7 c1 c2 c3 v250 v253 v254 v255 v256 v257 v258 v259 v260 v261 v262 v263 : Word}
    (ht7 : t7.toNat < 2 ^ 62) (hc1 : c1.toNat ≤ 1) (hc2 : c2.toNat ≤ 1)
    (h250 : v250.toNat = 0 ∨ v250.toNat = 2 ^ 64 - 1)
    (ha3 : t7.toNat + c1.toNat + c2.toNat + c3.toNat < 2 ^ 64)
    (v253_def : t7 ||| 13835058055282163712#64 = v253)
    (v254_def : v253 + c1 = v254)
    (v255_def : v254 + c2 = v255)
    (v256_def : (if v255.ult v253 = true then 1#64 else 0#64) = v256)
    (v257_def : v255 + c3 = v257)
    (v258_def : (if v257.ult v255 = true then 1#64 else 0#64) = v258)
    (v259_def : v256 + v258 = v259)
    (v260_def : v259 + v250 = v260)
    (v261_def : v257 + v250 = v261)
    (v262_def : (if v261.ult v257 = true then 1#64 else 0#64) = v262)
    (v263_def : v260 + v262 = v263) :
    v263.toNat ≤ 1 ∧
      (v250.toNat = 0 → t7.toNat + c1.toNat + c2.toNat + c3.toNat + 2 ^ 64 =
        2 ^ 62 + v261.toNat + 2 ^ 64 * v263.toNat) ∧
      (v250.toNat = 2 ^ 64 - 1 → t7.toNat + c1.toNat + c2.toNat + c3.toNat + 2 ^ 64 =
        2 ^ 62 + v261.toNat + 2 ^ 64 * v263.toNat + 1) := by
  have h253 := or_c000 ht7
  rw [v253_def] at h253
  -- the two small adds, one overflow test
  have e255 : v255.toNat + 2 ^ 64 * v256.toNat = v253.toNat + c1.toNat + c2.toNat := by
    subst v254_def v255_def v256_def
    rw [BitVec.toNat_add, BitVec.toNat_add]
    by_cases h : (v253 + c1 + c2).ult v253 = true
    · rw [if_pos h]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add] at h
      rw [show (1#64).toNat = 1 from rfl]
      omega
    · rw [if_neg h]
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add] at h
      rw [show (0#64).toNat = 0 from rfl]
      omega
  clear v254_def
  bn_lin
  rcases h250 with h1 | h1 <;>
  rcases (by omega : v256.toNat = 0 ∨ v256.toNat = 1) with h2 | h2 <;>
  rcases (by omega : v258.toNat = 0 ∨ v258.toNat = 1) with h3 | h3 <;>
  rcases (by omega : v262.toNat = 0 ∨ v262.toNat = 1) with h4 | h4 <;>
  omega

set_option maxRecDepth 20000 in
theorem mont_sub_tail_r {P0 N0 P1 N1 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hP0 : 0 < P0 ∧ 0 < N0) (hP1 : 0 < P1 ∧ 0 < N1)
    {a0 a1 a2 t7 c1 c2 c3 v235 v239 v240 v241 v243 v244 v246 v247 v248 v249 v250 v253 v254 v255
      v256 v257 v258 v259 v260 v261 v262 v263 v265 v266 v267 v268 v269 v270 v271 v272 v273 v274
      v275 v278 v279 v280 : Word}
    (ht7 : t7.toNat < 2 ^ 62) (hc1 : c1.toNat ≤ 1) (hc2 : c2.toNat ≤ 1)
    (ha3 : t7.toNat + c1.toNat + c2.toNat + c3.toNat < 2 ^ 64)
    (v235_def : (if (a0 + BitVec.ofNat 64 N0).ult a0 = true then 1#64 else 0#64) = v235)
    (v239_def : a1 + (v235 + 18446744073709551615#64) = v239)
    (v240_def : (if v239.ult a1 = true then 1#64 else 0#64) = v240)
    (v241_def : v235 + (18446744073709551615#64 + v240) = v241)
    (v243_def : (if (v239 + BitVec.ofNat 64 N1).ult v239 = true then 1#64 else 0#64) = v243)
    (v244_def : v241 + v243 = v244)
    (v246_def : (v244 + 18446744073709551615#64).sshiftRight 63 = v246)
    (v247_def : v246 + a2 = v247)
    (v248_def : (if v247.ult v246 = true then 1#64 else 0#64) = v248)
    (v249_def : v246 + v248 = v249)
    (v250_def : v249.sshiftRight 63 = v250)
    (v253_def : t7 ||| 13835058055282163712#64 = v253)
    (v254_def : v253 + c1 = v254)
    (v255_def : v254 + c2 = v255)
    (v256_def : (if v255.ult v253 = true then 1#64 else 0#64) = v256)
    (v257_def : v255 + c3 = v257)
    (v258_def : (if v257.ult v255 = true then 1#64 else 0#64) = v258)
    (v259_def : v256 + v258 = v259)
    (v260_def : v259 + v250 = v260)
    (v261_def : v257 + v250 = v261)
    (v262_def : (if v261.ult v257 = true then 1#64 else 0#64) = v262)
    (v263_def : v260 + v262 = v263)
    (v265_def : v263 + 18446744073709551615#64 &&& BitVec.ofNat 64 P0 = v265)
    (v266_def : v265 + (a0 + BitVec.ofNat 64 N0) = v266)
    (v267_def : (if v266.ult v265 = true then 1#64 else 0#64) = v267)
    (v268_def : v263 + 18446744073709551615#64 &&& BitVec.ofNat 64 P1 = v268)
    (v269_def : v268 + (v239 + BitVec.ofNat 64 N1) = v269)
    (v270_def : (if v269.ult v268 = true then 1#64 else 0#64) = v270)
    (v271_def : v269 + v267 = v271)
    (v272_def : (if v271.ult v269 = true then 1#64 else 0#64) = v272)
    (v273_def : v270 + v272 = v273)
    (v274_def : v273 + v247 = v274)
    (v275_def : (if v274.ult v273 = true then 1#64 else 0#64) = v275)
    (v278_def : v263 + 18446744073709551615#64 &&& 4611686018427387904#64 = v278)
    (v279_def : v278 + v261 = v279)
    (v280_def : v279 + v275 = v280) :
    let T := a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat +
      2 ^ 192 * (t7.toNat + c1.toNat + c2.toNat + c3.toNat)
    let R := v266.toNat + 2 ^ 64 * v271.toNat + 2 ^ 128 * v274.toNat + 2 ^ 192 * v280.toNat
    (T < (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) → R = T) ∧
      ((P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) ≤ T → R + (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) = T) := by
  intro T R
  obtain ⟨h244, e1⟩ := tail_s1 hN0 hN1 hP0 hP1 v235_def v239_def v240_def v241_def v243_def v244_def
  have e2 := tail_s2 h244 v246_def v247_def v248_def v249_def v250_def
  have h250 : v250.toNat = 0 ∨ v250.toNat = 2 ^ 64 - 1 := by omega
  obtain ⟨h263, e3, e3'⟩ := tail_s3r ht7 hc1 hc2 h250 ha3 v253_def v254_def v255_def v256_def
    v257_def v258_def v259_def v260_def v261_def v262_def v263_def
  obtain ⟨e4, e4'⟩ := tail_s4 hN0 hN1 hP0 hP1 (v94 := a0) (v116 := v239) (v124 := v247)
    (d3 := v261) h263 v265_def v266_def v267_def v268_def v269_def v270_def v271_def v272_def
    v273_def v274_def v275_def v278_def v279_def v280_def
  exact tail_combine (a0 := a0.toNat) (a1 := a1.toNat) (a2 := a2.toNat)
    (a3 := t7.toNat + c1.toNat + c2.toNat + c3.toNat) (d3 := v261.toNat) (b3 := v263.toNat)
    (r0 := v266.toNat) (r1 := v271.toNat) (r2 := v274.toNat) (r3 := v280.toNat)
    hN0 hN1 rfl rfl rfl rfl e1 e2 h263 e3 e3' e4 e4' v266.isLt v271.isLt v274.isLt
    v280.isLt v247.isLt (a0 + BitVec.ofNat 64 N0).isLt (v239 + BitVec.ofNat 64 N1).isLt v261.isLt

/-- `tail_s1` as the field addition compiles it: the borrow into limb 1 is
    folded as `b + (-1 + a1)` and tested against `b - 1`. -/
theorem tail_s1b {P0 N0 P1 N1 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hP0 : 0 < P0 ∧ 0 < N0) (hP1 : 0 < P1 ∧ 0 < N1) {a0 a1 v152 v156 v157 v158 v160 v161 : Word}
    (v152_def : (if (a0 + BitVec.ofNat 64 N0).ult a0 = true then 1#64 else 0#64) = v152)
    (v156_def : v152 + (18446744073709551615#64 + a1) = v156)
    (v157_def : (if v156.ult (v152 + 18446744073709551615#64) = true then 1#64 else 0#64) = v157)
    (v158_def : v152 + (18446744073709551615#64 + v157) = v158)
    (v160_def : (if (v156 + BitVec.ofNat 64 N1).ult v156 = true then 1#64 else 0#64) = v160)
    (v161_def : v158 + v160 = v161) :
    v161.toNat ≤ 1 ∧
      a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 =
        P0 + 2 ^ 64 * P1 +
          (a0 + BitVec.ofNat 64 N0).toNat + 2 ^ 64 * (v156 + BitVec.ofNat 64 N1).toNat +
          2 ^ 128 * v161.toNat := by
  have e152 : v152.toNat = 0 ∨ v152.toNat = 1 := by
    subst v152_def; split <;> simp
  have h157 : v157.toNat = 0 ∨ v157.toNat = 1 := by
    subst v157_def; split <;> simp
  have h160 : v160.toNat = 0 ∨ v160.toNat = 1 := by
    subst v160_def; split <;> simp
  -- `v157` is the borrow of `a1 - (1 - v152)`
  have e157 : v157.toNat = if v152.toNat = 0 ∧ 1 ≤ a1.toNat then 1 else 0 := by
    subst v157_def v156_def
    rcases e152 with h | h
    · have : v152 = 0#64 := BitVec.eq_of_toNat_eq h
      subst this
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, Bn.toNat_ofNat']
      have := a1.isLt
      by_cases ha : 1 ≤ a1.toNat
      · rw [if_pos (by simp; omega), if_pos ⟨rfl, ha⟩]; rfl
      · rw [if_neg (by simp; omega), if_neg (by omega)]; rfl
    · have : v152 = 1#64 := BitVec.eq_of_toNat_eq h
      subst this
      simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, Bn.toNat_ofNat']
      rw [if_neg (by simp)]; simp
  clear v157_def
  bn_lin
  rcases e152 with h1 | h1 <;>
  rcases h157 with h2 | h2 <;>
  rcases h160 with h3 | h3 <;>
  (rw [h1] at e157; split at e157 <;> omega)

set_option maxRecDepth 20000 in
/-- The conditional subtraction after a field addition `T = A + B` (`T < 2p`). -/
theorem add_sub_tail {P0 N0 P1 N1 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hP0 : 0 < P0 ∧ 0 < N0) (hP1 : 0 < P1 ∧ 0 < N1)
    {a0 a1 a2 a3 v152 v156 v157 v158 v160 v161 v163 v164 v165 v166 v167 v168 v169 v170 v174 v175
      v177 v178 v179 v180 v181 v182 v183 v184 v185 v186 v187 v188 v189 v190 : Word}
    (v152_def : (if (a0 + BitVec.ofNat 64 N0).ult a0 = true then 1#64 else 0#64) = v152)
    (v156_def : v152 + (18446744073709551615#64 + a1) = v156)
    (v157_def : (if v156.ult (v152 + 18446744073709551615#64) = true then 1#64 else 0#64) = v157)
    (v158_def : v152 + (18446744073709551615#64 + v157) = v158)
    (v160_def : (if (v156 + BitVec.ofNat 64 N1).ult v156 = true then 1#64 else 0#64) = v160)
    (v161_def : v158 + v160 = v161)
    (v163_def : (v161 + 18446744073709551615#64).sshiftRight 63 = v163)
    (v164_def : v163 + a2 = v164)
    (v165_def : (if v164.ult v163 = true then 1#64 else 0#64) = v165)
    (v166_def : v163 + v165 = v166)
    (v167_def : v166.sshiftRight 63 = v167)
    (v168_def : a3 + v167 = v168)
    (v169_def : (if v168.ult a3 = true then 1#64 else 0#64) = v169)
    (v170_def : v167 + v169 = v170)
    (v174_def : (if (v168 + 13835058055282163712#64).ult v168 = true then 1#64 else 0#64) = v174)
    (v175_def : v170 + v174 = v175)
    (v177_def : v175 + 18446744073709551615#64 &&& BitVec.ofNat 64 P0 = v177)
    (v178_def : v177 + (a0 + BitVec.ofNat 64 N0) = v178)
    (v179_def : (if v178.ult v177 = true then 1#64 else 0#64) = v179)
    (v180_def : v175 + 18446744073709551615#64 &&& BitVec.ofNat 64 P1 = v180)
    (v181_def : v180 + (v156 + BitVec.ofNat 64 N1) = v181)
    (v182_def : (if v181.ult v180 = true then 1#64 else 0#64) = v182)
    (v183_def : v181 + v179 = v183)
    (v184_def : (if v183.ult v181 = true then 1#64 else 0#64) = v184)
    (v185_def : v182 + v184 = v185)
    (v186_def : v185 + v164 = v186)
    (v187_def : (if v186.ult v185 = true then 1#64 else 0#64) = v187)
    (v188_def : v175 + 18446744073709551615#64 &&& 4611686018427387904#64 = v188)
    (v189_def : v188 + (v168 + 13835058055282163712#64) = v189)
    (v190_def : v189 + v187 = v190) :
    let T := a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat
    let R := v178.toNat + 2 ^ 64 * v183.toNat + 2 ^ 128 * v186.toNat + 2 ^ 192 * v190.toNat
    (T < (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) → R = T) ∧
      ((P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) ≤ T → R + (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) = T) := by
  intro T R
  obtain ⟨h161, e1⟩ := tail_s1b hN0 hN1 hP0 hP1 v152_def v156_def v157_def v158_def v160_def v161_def
  have e2 := tail_s2 h161 v163_def v164_def v165_def v166_def v167_def
  have h167 : v167.toNat = 0 ∨ v167.toNat = 2 ^ 64 - 1 := by omega
  obtain ⟨h175, e3, e3'⟩ := tail_s3 h167 v168_def v169_def v170_def v174_def v175_def
  obtain ⟨e4, e4'⟩ := tail_s4 hN0 hN1 hP0 hP1 (v94 := a0) (v116 := v156) (v124 := v164)
    (d3 := v168 + 13835058055282163712#64) h175 v177_def v178_def v179_def v180_def v181_def
    v182_def v183_def v184_def v185_def v186_def v187_def v188_def v189_def v190_def
  exact tail_combine (a0 := a0.toNat) (a1 := a1.toNat) (a2 := a2.toNat) (a3 := a3.toNat)
    (d3 := (v168 + 13835058055282163712#64).toNat) (b3 := v175.toNat)
    (r0 := v178.toNat) (r1 := v183.toNat) (r2 := v186.toNat) (r3 := v190.toNat)
    hN0 hN1 rfl rfl rfl rfl e1 e2 h175 e3 e3' e4 e4' v178.isLt v183.isLt v186.isLt
    v190.isLt v164.isLt (a0 + BitVec.ofNat 64 N0).isLt (v156 + BitVec.ofNat 64 N1).isLt
    (v168 + 13835058055282163712#64).isLt

/-- The final borrow of `T - p` (stages 1–3), as the comparison `T < p`. -/
theorem borrow_flag {P0 P1 a0 a1 a2 a3 d0 d1 d2 d3 b1 b2 b3 Pp T : Nat}
    (hPp : Pp = P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62)
    (hT : T = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3)
    (e1 : a0 + 2 ^ 64 * a1 + 2 ^ 128 = P0 + 2 ^ 64 * P1 + d0 + 2 ^ 64 * d1 + 2 ^ 128 * b1)
    (e2 : b2 = 0 ∧ a2 + b1 = d2 + 1 ∨ b2 = 2 ^ 64 - 1 ∧ a2 + b1 + 2 ^ 64 = d2 + 1)
    (h3 : b3 ≤ 1)
    (e3 : b2 = 0 → a3 + 2 ^ 64 = 2 ^ 62 + d3 + 2 ^ 64 * b3)
    (e3' : b2 = 2 ^ 64 - 1 → a3 + 2 ^ 64 = 2 ^ 62 + d3 + 2 ^ 64 * b3 + 1)
    (hd0 : d0 < 2 ^ 64) (hd1 : d1 < 2 ^ 64) (hd2 : d2 < 2 ^ 64) (hd3 : d3 < 2 ^ 64) :
    (T < Pp → b3 = 0) ∧ (Pp ≤ T → b3 = 1) := by
  have key : T + 2 ^ 256 = Pp + (d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3) + 2 ^ 256 * b3 := by
    rcases e2 with ⟨h2, e2⟩ | ⟨h2, e2⟩
    · have e3 := e3 h2; rw [hT, hPp]; linarith
    · have e3 := e3' h2; rw [hT, hPp]; linarith
  have hD : d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 < 2 ^ 256 := by omega
  clear e1 e2 e3 e3' hT hPp
  generalize d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 = D at key hD
  constructor <;> intro h <;> omega

/-- `x < p` as the borrow chain of `from_repr` computes it (`to_repr`'s stages 1–3). -/
theorem lt_flag {P0 N0 P1 N1 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hP0 : 0 < P0 ∧ 0 < N0) (hP1 : 0 < P1 ∧ 0 < N1)
    {a0 a1 a2 a3 v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127 v128 v129 v130 v134
      v135 : Word}
    (v112_def : (if (a0 + BitVec.ofNat 64 N0).ult a0 = true then 1#64 else 0#64) = v112)
    (v116_def : a1 + (v112 + 18446744073709551615#64) = v116)
    (v117_def : (if v116.ult a1 = true then 1#64 else 0#64) = v117)
    (v118_def : v112 + (18446744073709551615#64 + v117) = v118)
    (v120_def : (if (v116 + BitVec.ofNat 64 N1).ult v116 = true then 1#64 else 0#64) = v120)
    (v121_def : v118 + v120 = v121)
    (v123_def : (v121 + 18446744073709551615#64).sshiftRight 63 = v123)
    (v124_def : v123 + a2 = v124)
    (v125_def : (if v124.ult v123 = true then 1#64 else 0#64) = v125)
    (v126_def : v123 + v125 = v126)
    (v127_def : v126.sshiftRight 63 = v127)
    (v128_def : a3 + v127 = v128)
    (v129_def : (if v128.ult a3 = true then 1#64 else 0#64) = v129)
    (v130_def : v127 + v129 = v130)
    (v134_def : (if (v128 + 13835058055282163712#64).ult v128 = true then 1#64 else 0#64) = v134)
    (v135_def : v130 + v134 = v135) :
    let T := a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat
    (T < (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) → v135.toNat = 0) ∧
      ((P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) ≤ T → v135.toNat = 1) := by
  intro T
  obtain ⟨h121, e1⟩ := tail_s1 hN0 hN1 hP0 hP1 v112_def v116_def v117_def v118_def v120_def v121_def
  have e2 := tail_s2 h121 v123_def v124_def v125_def v126_def v127_def
  have h127 : v127.toNat = 0 ∨ v127.toNat = 2 ^ 64 - 1 := by omega
  obtain ⟨h135, e3, e3'⟩ := tail_s3 h127 v128_def v129_def v130_def v134_def v135_def
  exact borrow_flag (a0 := a0.toNat) (a1 := a1.toNat) (a2 := a2.toNat) (a3 := a3.toNat)
    (d3 := (v128 + 13835058055282163712#64).toNat) (b3 := v135.toNat) rfl rfl e1 e2 h135 e3 e3'
    (a0 + BitVec.ofNat 64 N0).isLt (v116 + BitVec.ofNat 64 N1).isLt v124.isLt
    (v128 + 13835058055282163712#64).isLt

end Cases.Zip2005
