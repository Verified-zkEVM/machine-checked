/-
  Cases.Zip2005.MontTail

  The final conditional subtraction of a Montgomery reduction modulo the Pallas
  base field `p` (limbs `p0, p1, 0, 2^62`), as the guest's `to_repr` compiles
  it: a borrow chain for `T - p` whose final borrow, spread by `sra 63` into a
  mask, selects `p` to add back.
-/

import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Field.Fp

namespace Cases.Zip2005

open RiscvZkvm.Rv64

/-- Limbs 0 and 1 of `T - p`: `v121` is the no-borrow flag. -/
theorem tail_s1 {P0 N0 P1 N1 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hP0 : 0 < P0 ∧ 0 < N0) (hP1 : 0 < P1 ∧ 0 < N1) {v94 v97 v112 v116 v117 v118 v120 v121 : Word}
    (v112_def : (if (v94 + BitVec.ofNat 64 N0).ult v94 = true then 1#64 else 0#64) = v112)
    (v116_def : v97 + (v112 + 18446744073709551615#64) = v116)
    (v117_def : (if v116.ult v97 = true then 1#64 else 0#64) = v117)
    (v118_def : v112 + (18446744073709551615#64 + v117) = v118)
    (v120_def : (if (v116 + BitVec.ofNat 64 N1).ult v116 = true then 1#64 else 0#64) = v120)
    (v121_def : v118 + v120 = v121) :
    v121.toNat ≤ 1 ∧
      v94.toNat + 2 ^ 64 * v97.toNat + 2 ^ 128 =
        P0 + 2 ^ 64 * P1 +
          (v94 + BitVec.ofNat 64 N0).toNat + 2 ^ 64 * (v116 + BitVec.ofNat 64 N1).toNat +
          2 ^ 128 * v121.toNat := by
  bn_lin
  rcases (by omega : v112.toNat = 0 ∨ v112.toNat = 1) with h1 | h1 <;>
  rcases (by omega : v117.toNat = 0 ∨ v117.toNat = 1) with h2 | h2 <;>
  rcases (by omega : v120.toNat = 0 ∨ v120.toNat = 1) with h3 | h3 <;>
  omega

/-- Limb 2 (`p2 = 0`): the borrow in is `1 - v121`, the borrow out the mask `v127`. -/
theorem tail_s2 {v104 v121 v123 v124 v125 v126 v127 : Word} (h121 : v121.toNat ≤ 1)
    (v123_def : (v121 + 18446744073709551615#64).sshiftRight 63 = v123)
    (v124_def : v123 + v104 = v124)
    (v125_def : (if v124.ult v123 = true then 1#64 else 0#64) = v125)
    (v126_def : v123 + v125 = v126)
    (v127_def : v126.sshiftRight 63 = v127) :
    (v127.toNat = 0 ∧ v104.toNat + v121.toNat = v124.toNat + 1) ∨
      (v127.toNat = 2 ^ 64 - 1 ∧ v104.toNat + v121.toNat + 2 ^ 64 = v124.toNat + 1) := by
  bn_lin
  have s1 := Bn.sar_fact v123_def
  have s2 := Bn.sar_fact v127_def
  rcases (by omega : v121.toNat = 0 ∨ v121.toNat = 1) with h1 | h1 <;>
  rcases (by omega : v125.toNat = 0 ∨ v125.toNat = 1) with h2 | h2 <;>
  omega

/-- Limb 3 (`p3 = 2^62`): `v135` is the final no-borrow flag. -/
theorem tail_s3 {v106 v127 v128 v129 v130 v134 v135 : Word}
    (h127 : v127.toNat = 0 ∨ v127.toNat = 2 ^ 64 - 1)
    (v128_def : v106 + v127 = v128)
    (v129_def : (if v128.ult v106 = true then 1#64 else 0#64) = v129)
    (v130_def : v127 + v129 = v130)
    (v134_def : (if (v128 + 13835058055282163712#64).ult v128 = true then 1#64 else 0#64) = v134)
    (v135_def : v130 + v134 = v135) :
    v135.toNat ≤ 1 ∧
      (v127.toNat = 0 → v106.toNat + 2 ^ 64 =
        2 ^ 62 + (v128 + 13835058055282163712#64).toNat + 2 ^ 64 * v135.toNat) ∧
      (v127.toNat = 2 ^ 64 - 1 → v106.toNat + 2 ^ 64 =
        2 ^ 62 + (v128 + 13835058055282163712#64).toNat + 2 ^ 64 * v135.toNat + 1) := by
  bn_lin
  rcases h127 with h1 | h1 <;>
  rcases (by omega : v129.toNat = 0 ∨ v129.toNat = 1) with h2 | h2 <;>
  rcases (by omega : v134.toNat = 0 ∨ v134.toNat = 1) with h3 | h3 <;>
  omega

set_option maxHeartbeats 2000000 in
/-- The add-back: `p`, masked by the borrow, added to the difference `D`. -/
theorem tail_s4 {P0 N0 P1 N1 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hP0 : 0 < P0 ∧ 0 < N0) (hP1 : 0 < P1 ∧ 0 < N1) {v94 v116 v124 d3 v135 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147
      v150 v151 v152 : Word} (h135 : v135.toNat ≤ 1)
    (v137_def : v135 + 18446744073709551615#64 &&& BitVec.ofNat 64 P0 = v137)
    (v138_def : v137 + (v94 + BitVec.ofNat 64 N0) = v138)
    (v139_def : (if v138.ult v137 = true then 1#64 else 0#64) = v139)
    (v140_def : v135 + 18446744073709551615#64 &&& BitVec.ofNat 64 P1 = v140)
    (v141_def : v140 + (v116 + BitVec.ofNat 64 N1) = v141)
    (v142_def : (if v141.ult v140 = true then 1#64 else 0#64) = v142)
    (v143_def : v141 + v139 = v143)
    (v144_def : (if v143.ult v141 = true then 1#64 else 0#64) = v144)
    (v145_def : v142 + v144 = v145)
    (v146_def : v145 + v124 = v146)
    (v147_def : (if v146.ult v145 = true then 1#64 else 0#64) = v147)
    (v150_def : v135 + 18446744073709551615#64 &&& 4611686018427387904#64 = v150)
    (v151_def : v150 + d3 = v151)
    (v152_def : v151 + v147 = v152) :
    let D := (v94 + BitVec.ofNat 64 N0).toNat + 2 ^ 64 * (v116 + BitVec.ofNat 64 N1).toNat +
      2 ^ 128 * v124.toNat + 2 ^ 192 * d3.toNat
    let R := v138.toNat + 2 ^ 64 * v143.toNat + 2 ^ 128 * v146.toNat + 2 ^ 192 * v152.toNat
    (v135.toNat = 1 → R = D) ∧
      (v135.toNat = 0 → R + 2 ^ 256 * ((D + (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62)) / 2 ^ 256) = D + (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62)) := by
  intro D R
  have m1 := Bn.mask_and h135 v137_def
  have m2 := Bn.mask_and h135 v140_def
  have m3 := Bn.mask_and h135 v150_def
  simp only [Bn.toNat_ofNat'] at m1 m2 m3
  bn_lin
  rcases (by omega : v135.toNat = 0 ∨ v135.toNat = 1) with h1 | h1 <;>
  rcases (by omega : v139.toNat = 0 ∨ v139.toNat = 1) with h2 | h2 <;>
  rcases (by omega : v142.toNat = 0 ∨ v142.toNat = 1) with h3 | h3 <;>
  rcases (by omega : v144.toNat = 0 ∨ v144.toNat = 1) with h4 | h4 <;>
  rcases (by omega : v147.toNat = 0 ∨ v147.toNat = 1) with h5 | h5 <;>
  constructor <;> intro h <;> omega

/-- The four stages, as arithmetic. -/
theorem tail_combine {P0 N0 P1 N1 a0 a1 a2 a3 r0 r1 r2 r3 d0 d1 d2 d3 b1 b2 b3 Pp D R T : Nat}
    (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hPp : Pp = P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62)
    (hD : D = d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3)
    (hR : R = r0 + 2 ^ 64 * r1 + 2 ^ 128 * r2 + 2 ^ 192 * r3)
    (hT : T = a0 + 2 ^ 64 * a1 + 2 ^ 128 * a2 + 2 ^ 192 * a3)
    (e1 : a0 + 2 ^ 64 * a1 + 2 ^ 128 = P0 + 2 ^ 64 * P1 + d0 + 2 ^ 64 * d1 + 2 ^ 128 * b1)
    (e2 : b2 = 0 ∧ a2 + b1 = d2 + 1 ∨ b2 = 2 ^ 64 - 1 ∧ a2 + b1 + 2 ^ 64 = d2 + 1)
    (h3 : b3 ≤ 1)
    (e3 : b2 = 0 → a3 + 2 ^ 64 = 2 ^ 62 + d3 + 2 ^ 64 * b3)
    (e3' : b2 = 2 ^ 64 - 1 → a3 + 2 ^ 64 = 2 ^ 62 + d3 + 2 ^ 64 * b3 + 1)
    (e4 : b3 = 1 → R = D) (e4' : b3 = 0 → R + 2 ^ 256 * ((D + Pp) / 2 ^ 256) = D + Pp)
    (hr0 : r0 < 2 ^ 64) (hr1 : r1 < 2 ^ 64) (hr2 : r2 < 2 ^ 64) (hr3 : r3 < 2 ^ 64)
    (hd2 : d2 < 2 ^ 64) (hd0 : d0 < 2 ^ 64) (hd1 : d1 < 2 ^ 64) (hd3 : d3 < 2 ^ 64) :
    (T < Pp → R = T) ∧ (Pp ≤ T → R + Pp = T) := by
  have hDlt : D < 2 ^ 256 := by rw [hD]; omega
  have hRlt : R < 2 ^ 256 := by rw [hR]; omega
  have hPlt : Pp < 2 ^ 256 := by rw [hPp]; omega
  have key : T + 2 ^ 256 = Pp + D + 2 ^ 256 * b3 := by
    rcases e2 with ⟨h2, e2⟩ | ⟨h2, e2⟩
    · have e3 := e3 h2; rw [hT, hPp, hD]; linarith
    · have e3 := e3' h2; rw [hT, hPp, hD]; linarith
  clear e1 e2 e3 e3' hR hD hT hPp hr0 hr1 hr2 hr3 hd0 hd1 hd2 hd3 hN0 hN1
  rcases (by omega : b3 = 0 ∨ b3 = 1) with h4 | h4
  · have e4 := e4' h4
    generalize (D + Pp) / 2 ^ 256 = q at e4
    constructor <;> intro h <;> omega
  · have e4 := e4 h4
    constructor <;> intro h <;> omega

theorem mont_sub_tail {P0 N0 P1 N1 : Nat} (hN0 : N0 + P0 = 2 ^ 64) (hN1 : N1 + P1 = 2 ^ 64)
    (hP0 : 0 < P0 ∧ 0 < N0) (hP1 : 0 < P1 ∧ 0 < N1) {v94 v97 v104 v106 v112 v116 v117 v118 v120 v121 v123 v124 v125 v126 v127
      v128 v129 v130 v134 v135 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v150 v151
      v152 : Word}
    (v112_def : (if (v94 + BitVec.ofNat 64 N0).ult v94 = true then 1#64 else 0#64) = v112)
    (v116_def : v97 + (v112 + 18446744073709551615#64) = v116)
    (v117_def : (if v116.ult v97 = true then 1#64 else 0#64) = v117)
    (v118_def : v112 + (18446744073709551615#64 + v117) = v118)
    (v120_def : (if (v116 + BitVec.ofNat 64 N1).ult v116 = true then 1#64 else 0#64) = v120)
    (v121_def : v118 + v120 = v121)
    (v123_def : (v121 + 18446744073709551615#64).sshiftRight 63 = v123)
    (v124_def : v123 + v104 = v124)
    (v125_def : (if v124.ult v123 = true then 1#64 else 0#64) = v125)
    (v126_def : v123 + v125 = v126)
    (v127_def : v126.sshiftRight 63 = v127)
    (v128_def : v106 + v127 = v128)
    (v129_def : (if v128.ult v106 = true then 1#64 else 0#64) = v129)
    (v130_def : v127 + v129 = v130)
    (v134_def : (if (v128 + 13835058055282163712#64).ult v128 = true then 1#64 else 0#64) = v134)
    (v135_def : v130 + v134 = v135)
    (v137_def : v135 + 18446744073709551615#64 &&& BitVec.ofNat 64 P0 = v137)
    (v138_def : v137 + (v94 + BitVec.ofNat 64 N0) = v138)
    (v139_def : (if v138.ult v137 = true then 1#64 else 0#64) = v139)
    (v140_def : v135 + 18446744073709551615#64 &&& BitVec.ofNat 64 P1 = v140)
    (v141_def : v140 + (v116 + BitVec.ofNat 64 N1) = v141)
    (v142_def : (if v141.ult v140 = true then 1#64 else 0#64) = v142)
    (v143_def : v141 + v139 = v143)
    (v144_def : (if v143.ult v141 = true then 1#64 else 0#64) = v144)
    (v145_def : v142 + v144 = v145)
    (v146_def : v145 + v124 = v146)
    (v147_def : (if v146.ult v145 = true then 1#64 else 0#64) = v147)
    (v150_def : v135 + 18446744073709551615#64 &&& 4611686018427387904#64 = v150)
    (v151_def : v150 + (v128 + 13835058055282163712#64) = v151)
    (v152_def : v151 + v147 = v152) :
    let T := v94.toNat + 2 ^ 64 * v97.toNat + 2 ^ 128 * v104.toNat + 2 ^ 192 * v106.toNat
    let R := v138.toNat + 2 ^ 64 * v143.toNat + 2 ^ 128 * v146.toNat + 2 ^ 192 * v152.toNat
    (T < (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) → R = T) ∧ ((P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) ≤ T → R + (P0 + 2 ^ 64 * P1 + 2 ^ 192 * 2 ^ 62) = T) := by
  intro T R
  obtain ⟨h121, e1⟩ := tail_s1 hN0 hN1 hP0 hP1 v112_def v116_def v117_def v118_def v120_def v121_def
  have e2 := tail_s2 h121 v123_def v124_def v125_def v126_def v127_def
  have h127 : v127.toNat = 0 ∨ v127.toNat = 2 ^ 64 - 1 := by omega
  obtain ⟨h135, e3, e3'⟩ := tail_s3 h127 v128_def v129_def v130_def v134_def v135_def
  obtain ⟨e4, e4'⟩ := tail_s4 hN0 hN1 hP0 hP1 (v94 := v94) (v116 := v116) (v124 := v124)
    (d3 := v128 + 13835058055282163712#64) h135
    v137_def v138_def v139_def v140_def v141_def v142_def v143_def v144_def v145_def v146_def
    v147_def v150_def v151_def v152_def
  have := v138.isLt; have := v143.isLt; have := v146.isLt; have := v152.isLt
  have := (v94 + BitVec.ofNat 64 N0).isLt; have := (v116 + BitVec.ofNat 64 N1).isLt
  have := v124.isLt; have := (v128 + 13835058055282163712#64).isLt
  exact tail_combine hN0 hN1 rfl rfl rfl rfl e1 e2 h135 e3 e3' e4 e4' v138.isLt v143.isLt v146.isLt
    v152.isLt v124.isLt (v94 + BitVec.ofNat 64 N0).isLt (v116 + BitVec.ofNat 64 N1).isLt
    (v128 + 13835058055282163712#64).isLt

end Cases.Zip2005
