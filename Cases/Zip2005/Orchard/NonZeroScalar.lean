/-
  Cases.Zip2005.NonZeroScalar

  `NonZeroPallasScalar::from_bytes` (`0x7802018c`): `Fq::from_repr` of the 32 bytes, the value
  masked by the `CtOption` flag, the flag conjoined with the value being non-zero (`ct_eq` with
  zero, through `black_box`).
-/

import Cases.Zip2005.Field.FqFromRepr
import RiscvZkvm.Rv64.Logic.ByteOps
import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Field.Cells4
import Cases.Zip2005.Image.F_7802018c
import Cases.Zip2005.Image.F_780232f4
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- The `zip32` crate's copy of `subtle::black_box::<u8>` (`0x780232f4`). -/
theorem black_box_zip32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp v : Word)
    (hpc : s.pc = 0x780232f4#64) (hcode : CodeAt F_780232f4.base F_780232f4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp) (ha0 : s.getReg .x10 = v)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2)] s t →
      t.getReg .x10 = BitVec.zeroExtend 64 (BitVec.truncate 8 v) → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hF, hFlen⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(sp - 0x10#64, 2)] s
  sym_exec
  sym_close hk
  sym_subst
  rw [hx10, extractByte_replaceByte _ 7 (by decide)]

/-! ## The model -/

/-- `NonZeroPallasScalar::from_bytes`: the `CtOption`'s value, `Fq::from_repr` of the bytes
(Montgomery form), zero when they are not a canonical scalar … -/
def nzScalarW (x : Nat) : List Word :=
  if x < Fq.q then natToLeLimbs 4 (Fq.mul x Fq.R2) else [0#64, 0#64, 0#64, 0#64]

/-- … and its flag: canonical and non-zero. -/
def nzScalarFlag (x : Nat) : BitVec 8 :=
  if x < Fq.q ∧ Fq.mul x Fq.R2 ≠ 0 then 1#8 else 0#8

theorem nz_flag_word (x : Nat) (o f : Word)
    (hf : BitVec.zeroExtend 64 (extractByte (replaceByte o 0 (if x < Fq.q then 1#8 else 0#8)) 0) = f) :
    f = if x < Fq.q then 1#64 else 0#64 := by
  subst hf
  have e := extractByte_replaceByte_same o 0 (if x < Fq.q then 1#8 else 0#8)
  simp only [Fin.val_zero] at e
  rw [e]
  split <;> rfl

theorem nz_cells (x : Nat) (f v107 v108 v109 v110 v111 : Word)
    (hf : f = if x < Fq.q then 1#64 else 0#64) (h107 : -f = v107)
    (h108 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 0) = v108)
    (h109 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 64) = v109)
    (h110 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 128) = v110)
    (h111 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 192) = v111) :
    [v108 &&& v107, v109 &&& v107, v110 &&& v107, v111 &&& v107] = nzScalarW x := by
  subst h107 h108 h109 h110 h111 hf
  unfold nzScalarW
  rw [natToLeLimbs_cells4]
  split
  · simp only [BitVec.neg_one_eq_allOnes, BitVec.and_allOnes, Nat.shiftRight_zero]
  · simp only [BitVec.neg_zero, BitVec.and_zero]

theorem nz_flag (x : Nat) (f v107 v108 v109 v110 v111 v112 v113 v114 v115 v129 v130 v138 : Word)
    (hf : f = if x < Fq.q then 1#64 else 0#64) (h107 : -f = v107)
    (h108 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 0) = v108)
    (h109 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 64) = v109)
    (h110 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 128) = v110)
    (h111 : BitVec.ofNat 64 (Fq.mul x Fq.R2 >>> 192) = v111)
    (h112 : v108 &&& v107 = v112) (h113 : v109 &&& v107 = v113) (h114 : v110 &&& v107 = v114)
    (h115 : v111 &&& v107 = v115)
    (h129 : bw (decide (v112 = 0#64 ∧ v113 = 0#64 ∧ v114 = 0#64 ∧ v115 = 0#64)) ^^^
      18446744073709551615#64 = v129)
    (h130 : v129 &&& 1#64 = v130)
    (h138 : f &&& BitVec.zeroExtend 64 (BitVec.truncate 8 v130) = v138) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 8 v138)) = nzScalarFlag x := by
  have hc := nz_cells x f v107 v108 v109 v110 v111 hf h107 h108 h109 h110 h111
  rw [h112, h113, h114, h115] at hc
  subst h138 h130 h129
  unfold nzScalarFlag
  by_cases hx : x < Fq.q
  · have hm : Fq.mul x Fq.R2 < 2 ^ 256 := lt_trans (Fq.mul_lt _ _) Fq.q_lt
    simp only [nzScalarW, hx, if_true, natToLeLimbs_cells4, List.cons.injEq, and_true] at hc
    obtain ⟨e112, e113, e114, e115⟩ := hc
    subst hf
    rw [if_pos hx, e112, e113, e114, e115]
    by_cases hz : Fq.mul x Fq.R2 = 0
    · rw [if_neg (fun h => h.2 hz), decide_eq_true ((cells4_eq_zero_iff _ hm).mpr hz)]
      rfl
    · rw [if_pos ⟨hx, hz⟩, decide_eq_false (fun h => hz ((cells4_eq_zero_iff _ hm).mp h))]
      rfl
  · subst hf
    rw [if_neg hx, if_neg (fun h => hx h.1)]
    simp only [BitVec.zero_and]
    rfl

/-! ## The function -/

theorem nonzero_scalar_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word)
    (x0 x1 x2 x3 : Word) (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7802018c#64) (hcode : CodeAt F_7802018c.base F_7802018c.prog s)
    (hcodeR : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeE : CodeAt F_7802e8ec.base F_7802e8ec.prog s)
    (hcodeZ : CodeAt F_780232f4.base F_780232f4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x150 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5) (hd : Disjoint a0 5 a1 4)
    (hd0 : Disjoint (sp - 0x150#64) 42 a0 5) (hd1 : Disjoint (sp - 0x150#64) 42 a1 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x150#64, 42), (a0, 5)] s t →
      Region a0 (nzScalarW (leLimbsToNat [x0, x1, x2, x3]) ++
        [replaceByte O[4]! 0 (nzScalarFlag (leLimbsToNat [x0, x1, x2, x3]))]) t → SafeN Gd n P t) :
    SafeN Gd n P s := by
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0xa0#64) 20 s
  obtain ⟨G, hG, hGl⟩ := Region.exists_junk (sp - 0x150#64) 22 s
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x150#64) 42 := hstk.frame 42 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa0#64) 20 := hokW.sub' 22 20 (by decide) (by bv_omega)
  have hokG : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x150#64) 22 := hokW.sub' 0 22 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x150#64, 42), (a0, 5)] s
  have hlo := hstk.lo
  sym_exec [fq_from_repr_spec, fq_ct_eq_spec, black_box_zip32_spec]
  -- the four words of the input, byte by byte
  have hx3 : v30 = x3 := by
    rw [← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def, ← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def, ← v14_def, ← v13_def, ← v12_def, ← v11_def, ← v10_def, ← v9_def]
    exact bytes_word x3
  have hx2 : v52 = x2 := by
    rw [← v52_def, ← v51_def, ← v50_def, ← v49_def, ← v48_def, ← v47_def, ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v34_def, ← v33_def, ← v32_def, ← v31_def]
    exact bytes_word x2
  have hx1 : v74 = x1 := by
    rw [← v74_def, ← v73_def, ← v72_def, ← v71_def, ← v70_def, ← v69_def, ← v68_def, ← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def, ← v56_def, ← v55_def, ← v54_def, ← v53_def]
    exact bytes_word x1
  have hx0 : v96 = x0 := by
    rw [← v96_def, ← v95_def, ← v94_def, ← v93_def, ← v92_def, ← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def, ← v76_def, ← v75_def]
    exact bytes_word x0
  rw [hx0, hx1, hx2, hx3] at v106_def v108_def v109_def v110_def v111_def
  have hf := nz_flag_word _ _ _ v106_def
  have hc := nz_cells _ _ _ _ _ _ _ hf v107_def v108_def v109_def v110_def v111_def
  have hfl := nz_flag _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf v107_def v108_def v109_def v110_def v111_def
    v112_def v113_def v114_def v115_def v129_def v130_def v138_def
  have e : [v112, v113, v114, v115, v142] = nzScalarW (leLimbsToNat [x0, x1, x2, x3]) ++
      [replaceByte O[4]! 0 (nzScalarFlag (leLimbsToNat [x0, x1, x2, x3]))] := by
    rw [← v142_def, hfl, ← hc, ← v112_def, ← v113_def, ← v114_def, ← v115_def]
    rfl
  have hR : Region a0 (nzScalarW (leLimbsToNat [x0, x1, x2, x3]) ++
      [replaceByte O[4]! 0 (nzScalarFlag (leLimbsToNat [x0, x1, x2, x3]))]) s_152 :=
    Eq.mp (congrArg (fun L => Region a0 L s_152) e) hR1
  sym_close hk

end Cases.Zip2005
