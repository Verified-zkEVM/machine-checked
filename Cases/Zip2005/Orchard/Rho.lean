import Cases.Zip2005.Field.FromRepr
import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Image.F_7801ddd8
import Cases.Zip2005.Image.Ro

/-!
# `Rho::from_bytes`

`pallas::Base::from_repr(bytes).map(Rho)`: the 32 bytes are reassembled into four words on
the stack, `Fp::from_repr` fills a `CtOption<Fp>` in the frame, and `map` copies it out with
the limbs masked by `is_some` (`ctLimbs`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem rho_from_bytes_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7801ddd8#64) (hcode : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x110 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x110#64) 34 a0 5) (hd_a1 : Disjoint (sp - 0x110#64) 34 a1 4)
    (he_a1 : Disjoint a0 5 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x110#64, 34), (a0, 5)] s t →
      Region a0 (ctLimbs (leLimbsToNat [b0, b1, b2, b3] < Fp.p)
        (natToLeLimbs 4 (Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2)) O[4]!) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 34 := hstk.frame 34 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hokW.sub' 22 12 (by decide) (by bv_omega)
  -- the frame: [8, 0x28) the `CtOption<Fp>`, [0x30, 0x50) the four words, saved registers
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x58#64) 5 s
  obtain ⟨FW, hFW, hFWl⟩ := Region.exists_junk (sp - 0x30#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x58#64) 5 := hokF.sub' 1 5 (by decide) (by bv_omega)
  have hokWd : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 4 := hokF.sub' 6 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokF.sub' 10 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x110#64, 34), (a0, 5)] s
  have hlo := hstk.lo
  sym_exec [fp_from_repr_spec]
  -- the encoding's words, reassembled from bytes
  have hb3 : v25 = b3 := by
    rw [← v25_def, ← v24_def, ← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def, ← v14_def, ← v13_def, ← v12_def, ← v11_def, ← v10_def, ← v9_def, ← v8_def, ← v7_def, ← v6_def, ← v5_def, ← v4_def]
    exact bytes_word b3
  have hb2 : v47 = b2 := by
    rw [← v47_def, ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v34_def, ← v33_def, ← v32_def, ← v31_def, ← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def]
    exact bytes_word b2
  have hb1 : v69 = b1 := by
    rw [← v69_def, ← v68_def, ← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def, ← v56_def, ← v55_def, ← v54_def, ← v53_def, ← v52_def, ← v51_def, ← v50_def, ← v49_def, ← v48_def]
    exact bytes_word b1
  have hb0 : v91 = b0 := by
    rw [← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def, ← v76_def, ← v75_def, ← v74_def, ← v73_def, ← v72_def, ← v71_def, ← v70_def]
    exact bytes_word b0
  subst hb0 hb1 hb2 hb3
  -- the `is_some` byte and the masks
  rw [extractByte_replaceByte _ _ (by decide)] at v101_def
  rw [← v115_def, ← v101_def, trunc8_zext] at hR1
  rw [← v107_def, ← v108_def, ← v109_def, ← v110_def, ← v102_def, ← v101_def, zext_if8,
    ← v103_def, ← v104_def, ← v105_def, ← v106_def] at hR1
  simp only [and_negbw, decide_eq_true_eq, Nat.shiftRight_zero] at hR1
  sym_close hk
  rw [natToLeLimbs_four, ctLimbs_four]

end Cases.Zip2005
