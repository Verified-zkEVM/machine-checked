import Cases.Zip2005.Field.FromRepr
import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Image.F_78022848
import Cases.Zip2005.Image.Ro

/-!
# `NullifierDerivingKey::from_bytes`

A 32-byte slice (any other length is `None`), `Fp::from_repr`, and the `CtOption` unwrapped
into an `Option`: tag `1` and the four limbs when the bytes are canonical, tag `0` otherwise
(the `assert_failed` path needs the flag byte to be neither `0` nor `1`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem nullifier_deriving_key_from_bytes_spec {P : Prop} (s : MachineState) (ra sp a0 a1 len : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x78022848#64) (hcode : CodeAt F_78022848.base F_78022848.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x110 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = len)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x110#64) 34 a0 5) (hd_a1 : Disjoint (sp - 0x110#64) 34 a1 4)
    (he_a1 : Disjoint a0 5 a1 4)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x110#64, 34), (a0, 5)] s t →
      tag = (if len = 32#64 ∧ leLimbsToNat [b0, b1, b2, b3] < Fp.p then 1#64 else 0#64) → L.length = 4 →
      (len = 32#64 → leLimbsToNat [b0, b1, b2, b3] < Fp.p →
        L = natToLeLimbs 4 (Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2)) →
      Region a0 (tag :: L) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 34 := hstk.frame 34 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hokW.sub' 22 12 (by decide) (by bv_omega)
  -- the frame: [8, 0x28) the four words, [0x28, 0x50) the `CtOption`, saved registers
  obtain ⟨FW, hFW, hFWl⟩ := Region.exists_junk (sp - 0x58#64) 4 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x38#64) 5 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokWd : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x58#64) 4 := hokF.sub' 1 4 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x38#64) 5 := hokF.sub' 5 5 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokF.sub' 10 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x110#64, 34), (a0, 5)] s
  have hlo := hstk.lo
  sym_exec [fp_from_repr_spec, hpaf]
  · -- the slice is not 32 bytes long
    have hlen : ¬ len = 32#64 := bne_iff_ne.mp hbr5
    sym_close (hk _ _ _)
    all_goals first
      | rfl
      | exact (if_neg (fun h => hlen h.1)).symm
      | (intro h; exact absurd h hlen)
  all_goals
    have hlen : len = 32#64 := by
      by_contra h
      exact hbr5 (bne_iff_ne.mpr h)
  -- the encoding's words, reassembled from bytes
  all_goals
    have hb3 : v27 = b3 := by
      rw [← v27_def, ← v26_def, ← v25_def, ← v24_def, ← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def, ← v14_def, ← v13_def, ← v12_def, ← v11_def, ← v10_def, ← v9_def, ← v8_def, ← v7_def, ← v6_def]
      exact bytes_word b3
  all_goals
    have hb2 : v49 = b2 := by
      rw [← v49_def, ← v48_def, ← v47_def, ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v34_def, ← v33_def, ← v32_def, ← v31_def, ← v30_def, ← v29_def, ← v28_def]
      exact bytes_word b2
  all_goals
    have hb1 : v71 = b1 := by
      rw [← v71_def, ← v70_def, ← v69_def, ← v68_def, ← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def, ← v56_def, ← v55_def, ← v54_def, ← v53_def, ← v52_def, ← v51_def, ← v50_def]
      exact bytes_word b1
  all_goals
    have hb0 : v93 = b0 := by
      rw [← v93_def, ← v92_def, ← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def, ← v76_def, ← v75_def, ← v74_def, ← v73_def, ← v72_def]
      exact bytes_word b0
  all_goals subst hb0 hb1 hb2 hb3 hlen
  -- the `is_some` byte decides the branch
  all_goals rw [extractByte_replaceByte _ _ (by decide)] at v103_def
  all_goals by_cases hc : leLimbsToNat [v93, v71, v49, v27] < Fp.p
  all_goals simp only [hc, ↓reduceIte] at v103_def
  all_goals subst v103_def
  all_goals first
    | exact absurd hbr104 (by decide)
    | exact (hbr104 (by decide)).elim
    | skip
  · -- `None`: the bytes are not canonical
    sym_close (hk _ _ _)
    all_goals rfl
  · -- `Some`: the tag and the four limbs (the mask is all ones)
    sym_close (hk _ _ _)
    all_goals first
      | rfl
      | exact (if_pos ⟨rfl, hc⟩).symm
      | (intro _ _
         rw [← v113_def, ← v114_def, ← v115_def, ← v116_def, ← v112_def,
           show -(BitVec.zeroExtend 64 1#8) = 18446744073709551615#64 by decide, and_allOnes', and_allOnes',
           and_allOnes', and_allOnes', ← v105_def, ← v106_def, ← v107_def, ← v108_def, natToLeLimbs_four]
         try rfl)

end Cases.Zip2005
