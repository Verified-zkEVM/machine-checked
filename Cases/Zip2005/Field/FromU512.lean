import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Field.MontTailR
import Cases.Zip2005.Image.F_78028718
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
/-- `Fp::from_u512`: the low half times `R2` plus the high half times `R3`, each
    through `UINT256_MUL` and a reduction by `R⁻¹`, added in software. -/
theorem fp_from_u512_spec {P : Prop} (s : MachineState) (ra a0 a1 sp : Word) (x : List Word)
    (hxl : x.length = 8)
    (hpc : s.pc = 0x78028718#64) (hcode : CodeAt F_78028718.base F_78028718.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xf0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 x s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 8)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd : Disjoint a0 4 a1 8)
    (hd0 : Disjoint (sp - 0xf0#64) 30 a0 4) (hd1 : Disjoint (sp - 0xf0#64) 30 a1 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xf0#64, 30), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4 (Fp.add
        (Fp.mul (leLimbsToNat [x[0]!, x[1]!, x[2]!, x[3]!]) Fp.R2)
        (Fp.mul (leLimbsToNat [x[4]!, x[5]!, x[6]!, x[7]!]) Fp.R3))) t → Safe P t) :
    Safe P s := by
  obtain ⟨O, hO, hOlen⟩ := Region.exists_junk a0 4 s
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0xf0#64) 30 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xf0#64) 30 := hstk.frame 30 (by decide)
  have hu := Unchanged.refl [(sp - 0xf0#64, 30), (a0, 4)] s
  sym_exec [uint256_mulmod_spec]
  sym_close hk
  bn_lin
  have hAl : acc82_0 < Fp.p := by rw [← acc82_0_def, Fp.limbs_p]; exact Nat.mod_lt _ Fp.p_pos
  have hBl : acc128_0 < Fp.p := by rw [← acc128_0_def, Fp.limbs_p]; exact Nat.mod_lt _ Fp.p_pos
  have hA : v83.toNat + 2^64 * v84.toNat + 2^128 * v85.toNat + 2^192 * v86.toNat = acc82_0 := by
    have h := leLimbsToNat_natToLeLimbs 4 acc82_0 (lt_trans hAl Fp.p_lt)
    rw [← cells4, v83_def, v84_def, v85_def, v86_def] at h
    rw [← h]; simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hB : v129.toNat + 2^64 * v130.toNat + 2^128 * v131.toNat + 2^192 * v132.toNat = acc128_0 := by
    have h := leLimbsToNat_natToLeLimbs 4 acc128_0 (lt_trans hBl Fp.p_lt)
    rw [← cells4, v129_def, v130_def, v131_def, v132_def] at h
    rw [← h]; simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have eT : v133.toNat + 2^64 * v137.toNat + 2^128 * v142.toNat + 2^192 * v146.toNat
      + 2 ^ 256 * ((v132.toNat + v86.toNat) / 18446744073709551616
        + (v145.toNat + v144.toNat) / 18446744073709551616)
      = acc82_0 + acc128_0 := by
    rw [← hA, ← hB]
    linarith only [hz_0, hz_1, hn_v133, hn_v134, hn_v135, hn_v136, hn_v137, hn_v138, hn_v139, hn_v140,
      hn_v141, hn_v142, hn_v143, hn_v144, hn_v145, hn_v146]
  have hp2 : Fp.p < 2 ^ 255 := by decide
  have hT := eq_of_add_mul eT (by omega)
  have tl := add_sub_tail (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v152_def v156_def v157_def v158_def v160_def v161_def v163_def v164_def v165_def
    v166_def v167_def v168_def v169_def v170_def v174_def v175_def v177_def v178_def v179_def
    v180_def v181_def v182_def v183_def v184_def v185_def v186_def v187_def v188_def v189_def
    v190_def
  dsimp only at tl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide,
    hT] at tl
  have hR := mod_of_tail (by omega) tl.1 tl.2
  have hAm : acc82_0 = Fp.mul (leLimbsToNat [v15, v16, v17, v18]) Fp.R2 := by
    rw [← acc82_0_def, ← acc61_0_def]
    simp only [cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_R2, Fp.limbs_mod]
    rw [Fp.mul]
  have hBm : acc128_0 = Fp.mul (leLimbsToNat [v19, v21, v23, v25]) Fp.R3 := by
    rw [← acc128_0_def, ← acc115_0_def]
    simp only [cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_R3, Fp.limbs_mod]
    rw [Fp.mul]
  have hRe : leLimbsToNat [v178, v183, v186, v190] =
      v178.toNat + 2^64 * v183.toNat + 2^128 * v186.toNat + 2^192 * v190.toNat := by
    simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have hout : [v178, v183, v186, v190] = natToLeLimbs 4 (Fp.add
      (Fp.mul (leLimbsToNat [v15, v16, v17, v18]) Fp.R2)
      (Fp.mul (leLimbsToNat [v19, v21, v23, v25]) Fp.R3)) := by
    rw [Fp.add, ← hAm, ← hBm, ← hR, ← hRe]
    exact (natToLeLimbs_leLimbsToNat _).symm
  rw [← v15_def, ← v16_def, ← v17_def, ← v18_def, ← v19_def, ← v21_def, ← v23_def, ← v25_def] at hout
  exact hout

end Cases.Zip2005
