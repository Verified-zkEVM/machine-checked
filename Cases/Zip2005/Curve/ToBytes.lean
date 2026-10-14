import Cases.Zip2005.Curve.ToAffine
import Cases.Zip2005.Curve.MulModel
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Curve.PointBytes
import Cases.Zip2005.Image.F_78025654
import Cases.Zip2005.Image.Ro

/-!
# `Ep::to_bytes`

`to_affine`, the identity test through `black_box`; the identity encodes as 32 zero bytes
(`memset`), otherwise `x.to_repr()` with the parity of `y.to_repr()` in the top bit. Since the
affine identity is `(0, 0)`, both are `x_canonical + 2^255 · (y_canonical mod 2)`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym


/-- The limbs of a value below `2^256`, reassembled. -/
theorem leLimbs_ofNat_shifts (X : Nat) (h : X < 2 ^ 256) :
    leLimbsToNat [BitVec.ofNat 64 X, BitVec.ofNat 64 (X >>> 64), BitVec.ofNat 64 (X >>> 128),
      BitVec.ofNat 64 (X >>> 192)] = X := by
  have hX := leLimbsToNat_natToLeLimbs 4 X (by simpa using h)
  rwa [natToLeLimbs_four] at hX

/-- Adding the sign bit at 255 leaves the three low limbs alone. -/
theorem encode_low (Xc b j : Nat) (hj : j + 64 ≤ 255) :
    BitVec.ofNat 64 ((Xc + 2 ^ 255 * b) >>> j) = BitVec.ofNat 64 (Xc >>> j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have e1 : 2 ^ 255 * b = 2 ^ j * (2 ^ 64 * (2 ^ (255 - j - 64) * b)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add,
      show j + 64 + (255 - j - 64) = 255 by omega]
  rw [e1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.add_mul_mod_self_left]

/-- The top limb: the byte written back is the old top byte with the parity of `y` in bit 7. -/
theorem encode_top (Xc Yc : Nat) (hX : Xc < 2 ^ 255) :
    replaceByte (BitVec.ofNat 64 (Xc >>> 192)) 7
      (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte (BitVec.ofNat 64 (Xc >>> 192)) 7) |||
        BitVec.zeroExtend 64 (BitVec.truncate 8
          (BitVec.zeroExtend 64 (extractByte (BitVec.ofNat 64 (Yc >>> 0)) 0) &&& 1#64)) <<< 7)) =
    BitVec.ofNat 64 ((Xc + 2 ^ 255 * (Yc % 2)) >>> 192) := by
  have hb : Xc.testBit 255 = false := Nat.testBit_lt_two_pow hX
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_replaceByte _ _ _ _ hi]
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ofNat, Nat.testBit_shiftRight, Nat.shiftRight_zero]
  have key : ∀ j, j < 255 → (2 ^ 255 + Xc).testBit j = Xc.testBit j :=
    fun j hj => Nat.testBit_two_pow_add_gt hj Xc
  have key255 : (2 ^ 255 + Xc).testBit 255 = true := by
    rw [Nat.testBit_two_pow_add_eq, hb]; rfl
  simp only [Nat.reducePow] at key key255
  rcases Nat.mod_two_eq_zero_or_one Yc with h | h <;> rw [h]
  · simp only [Nat.mul_zero, Nat.add_zero]
    interval_cases i <;> simp [Nat.testBit_zero, h, hb]
  · simp only [Nat.mul_one, Nat.add_comm Xc]
    interval_cases i <;> simp [key, key255, Nat.testBit_zero, h, hb]

/-- The non-identity branch of `to_bytes`, in a small context. -/
theorem to_bytes_tail (X Y acc115_0 acc126_0 : Nat) (v95 v96 v97 v98 v103 v104 v105 v106 v116 v117 v121 v127 v128 v129 : Word)
    (hXY : X < 2 ^ 256 ∧ Y < 2 ^ 256)
    (hXc : X * Fp.rInv % Fp.p < 2 ^ 255)
    (v95_def : BitVec.ofNat 64 (Y >>> 0) = v95)
    (v96_def : BitVec.ofNat 64 (Y >>> 64) = v96)
    (v97_def : BitVec.ofNat 64 (Y >>> 128) = v97)
    (v98_def : BitVec.ofNat 64 (Y >>> 192) = v98)
    (v103_def : BitVec.ofNat 64 (X >>> 0) = v103)
    (v104_def : BitVec.ofNat 64 (X >>> 64) = v104)
    (v105_def : BitVec.ofNat 64 (X >>> 128) = v105)
    (v106_def : BitVec.ofNat 64 (X >>> 192) = v106)
    (acc115_0_def : leLimbsToNat [v95, v96, v97, v98] * Fp.rInv % Fp.p = acc115_0)
    (acc126_0_def : leLimbsToNat [v103, v104, v105, v106] * Fp.rInv % Fp.p = acc126_0)
    (v116_def : BitVec.zeroExtend 64 (extractByte (BitVec.ofNat 64 (acc115_0 >>> 0)) 0) = v116)
    (v117_def : v116 &&& 1#64 = v117)
    (v121_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v117) <<< 7 = v121)
    (v127_def : BitVec.zeroExtend 64 (extractByte (BitVec.ofNat 64 (acc126_0 >>> 192)) 7) = v127)
    (v128_def : v127 ||| v121 = v128)
    (v129_def : replaceByte (BitVec.ofNat 64 (acc126_0 >>> 192)) 7 (BitVec.truncate 8 v128) = v129) :
    [BitVec.ofNat 64 (acc126_0 >>> (64 * 0)), BitVec.ofNat 64 (acc126_0 >>> (64 * 1)), BitVec.ofNat 64 (acc126_0 >>> (64 * 2)), v129] = natToLeLimbs 4 (X * Fp.rInv % Fp.p + 2 ^ 255 * (Y * Fp.rInv % Fp.p % 2)) := by
  have hXc' : acc126_0 = X * Fp.rInv % Fp.p := by
    rw [← acc126_0_def, ← v103_def, ← v104_def, ← v105_def, ← v106_def]
    simp only [Nat.shiftRight_zero]
    rw [leLimbs_ofNat_shifts _ hXY.1]
  have hYc' : acc115_0 = Y * Fp.rInv % Fp.p := by
    rw [← acc115_0_def, ← v95_def, ← v96_def, ← v97_def, ← v98_def]
    simp only [Nat.shiftRight_zero]
    rw [leLimbs_ofNat_shifts _ hXY.2]
  have hlt : acc126_0 < 2 ^ 255 := by rw [hXc']; exact hXc
  rw [← v129_def, ← v128_def, ← v127_def, ← v121_def, ← v117_def, ← v116_def, encode_top _ _ hlt,
    natToLeLimbs_four, ← hXc', ← hYc']
  have e0 := encode_low acc126_0 (acc115_0 % 2) 0 (by decide)
  have e1 := encode_low acc126_0 (acc115_0 % 2) 64 (by decide)
  have e2 := encode_low acc126_0 (acc115_0 % 2) 128 (by decide)
  simp only [Nat.shiftRight_zero, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reducePow] at e0 e1 e2 ⊢
  rw [e0, e1, e2]

/-- The identity branch of `to_bytes`: the eight limbs are zero, so `X = Y = 0`. -/
theorem to_bytes_identity_tail (X Y) (acc99_0 : List Word) (v10 v11 v15 v16 v17 v21 v22 v26 v27 v28 v32 v33 v37 v38 v39 v43 v44 v48 v49 v50 v54 v55 v56 v60 v61 v65 v66 v67 v71 v72 v76 v77 v78 v82 v83 v87 v88 v92 : Word)
    (hXY : X < 2 ^ 256 ∧ Y < 2 ^ 256)
    (hbr93 : ¬(v92 == 0#64) = true)
    (acc99_0_def : List.replicate 4 0#64 = acc99_0)
    (v92_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v88) &&& 255#64 = v92)
    (v88_def : v87 &&& 255#64 = v88)
    (v87_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v83) &&& v49 = v87)
    (v83_def : v82 &&& 255#64 = v83)
    (v82_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v78) &&& v77 = v82)
    (v78_def : (if v76.ult 1#64 = true then 1#64 else 0#64) = v78)
    (v77_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v72) = v77)
    (v76_def : BitVec.ofNat 64 (Y >>> 192) = v76)
    (v72_def : v71 &&& 255#64 = v72)
    (v71_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v67) &&& v66 = v71)
    (v67_def : (if v65.ult 1#64 = true then 1#64 else 0#64) = v67)
    (v66_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v61) = v66)
    (v65_def : BitVec.ofNat 64 (Y >>> 128) = v65)
    (v61_def : v60 &&& 255#64 = v61)
    (v60_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v56) &&& v55 = v60)
    (v56_def : (if v54.ult 1#64 = true then 1#64 else 0#64) = v56)
    (v55_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v50) = v55)
    (v54_def : BitVec.ofNat 64 (Y >>> 64) = v54)
    (v50_def : (if v48.ult 1#64 = true then 1#64 else 0#64) = v50)
    (v49_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v44) = v49)
    (v48_def : BitVec.ofNat 64 (Y >>> 0) = v48)
    (v44_def : v43 &&& 255#64 = v44)
    (v43_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v39) &&& v38 = v43)
    (v39_def : (if v37.ult 1#64 = true then 1#64 else 0#64) = v39)
    (v38_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v33) = v38)
    (v37_def : BitVec.ofNat 64 (X >>> 192) = v37)
    (v33_def : v32 &&& 255#64 = v33)
    (v32_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v28) &&& v27 = v32)
    (v28_def : (if v26.ult 1#64 = true then 1#64 else 0#64) = v28)
    (v27_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v22) = v27)
    (v26_def : BitVec.ofNat 64 (X >>> 128) = v26)
    (v22_def : v21 &&& 255#64 = v22)
    (v21_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v17) &&& v16 = v21)
    (v17_def : (if v15.ult 1#64 = true then 1#64 else 0#64) = v17)
    (v16_def : BitVec.zeroExtend 64 (BitVec.truncate 8 v11) = v16)
    (v15_def : BitVec.ofNat 64 (X >>> 64) = v15)
    (v11_def : (if v10.ult 1#64 = true then 1#64 else 0#64) = v11)
    (v10_def : BitVec.ofNat 64 (X >>> 0) = v10) :
    [acc99_0[0]!, acc99_0[1]!, acc99_0[2]!, acc99_0[3]!] = natToLeLimbs 4 (X * Fp.rInv % Fp.p + 2 ^ 255 * (Y * Fp.rInv % Fp.p % 2)) := by
  rw [← v92_def, ← v88_def, ← v87_def, ← v83_def, ← v82_def, ← v78_def, ← v77_def, ← v76_def, ← v72_def, ← v71_def, ← v67_def, ← v66_def, ← v65_def, ← v61_def, ← v60_def, ← v56_def, ← v55_def, ← v54_def, ← v50_def, ← v49_def, ← v48_def, ← v44_def, ← v43_def, ← v39_def, ← v38_def, ← v37_def, ← v33_def, ← v32_def, ← v28_def, ← v27_def, ← v26_def, ← v22_def, ← v21_def, ← v17_def, ← v16_def, ← v15_def, ← v11_def, ← v10_def] at hbr93
  simp only [seqz_bw, bb_bw, and_bw, and255_bw, Nat.shiftRight_zero] at hbr93
  have hB := (bw_ne_zero _).mp hbr93
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hB
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hB
  have hX0 := (limbs4_zero_iff _ hXY.1).mp ⟨h8, h7, h6, h5⟩
  have hY0 := (limbs4_zero_iff _ hXY.2).mp ⟨h4, h3, h2, h1⟩
  rw [hX0, hY0]
  simp only [Nat.zero_mul, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  rw [← acc99_0_def]
  rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem ep_to_bytes_spec {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Word)
    (O : List Word) (hOl : O.length = 4)
    (hpc : s.pc = 0x78025654#64) (hcode : CodeAt F_78025654.base F_78025654.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x2f0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hd0 : Disjoint (sp - 0x2f0#64) 94 a0 4) (hd1 : Disjoint (sp - 0x2f0#64) 94 a1 12)
    (he1 : Disjoint a0 4 a1 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x2f0#64, 94), (a0, 4)] s t →
      Region a0 (natToLeLimbs 4
        ((Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).1 * Fp.rInv % Fp.p +
          2 ^ 255 * ((Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).2 * Fp.rInv % Fp.p % 2))) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2f0#64) 94 := hstk.frame 94 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xc0#64) 24 := hokW.sub' 70 24 (by decide) (by bv_omega)
  -- the frame: [0, 0x40) the affine point, [0x40, 0x60) `x`, [0x60, 0x80) `y`,
  -- [0x80, 0xa0) `y.to_repr()`, saved registers
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0xc0#64) 8 s
  obtain ⟨FX, hFX, hFXl⟩ := Region.exists_junk (sp - 0x80#64) 4 s
  obtain ⟨FY, hFY, hFYl⟩ := Region.exists_junk (sp - 0x60#64) 4 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x40#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xc0#64) 8 := hokF.sub' 0 8 (by decide) (by bv_omega)
  have hokX : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 4 := hokF.sub' 8 4 (by decide) (by bv_omega)
  have hokY : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 4 := hokF.sub' 12 4 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 4 := hokF.sub' 16 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokF.sub' 20 4 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x2f0#64, 94), (a0, 4)] s
  have hlo := hstk.lo
  -- the affine coordinates are below `2^256`
  have hXY := toAffine_lt (X := leLimbsToNat [p0, p1, p2, p3]) (Y := leLimbsToNat [p4, p5, p6, p7]) (Z := leLimbsToNat [p8, p9, p10, p11])
    (by have := leLimbsToNat_lt [p0, p1, p2, p3]; simpa using this)
    (by have := leLimbsToNat_lt [p4, p5, p6, p7]; simpa using this)
  have hp255 : Fp.p < 2 ^ 255 := by decide +kernel
  have hXc : (Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).1 * Fp.rInv % Fp.p < 2 ^ 255 :=
    (Nat.mod_lt _ Fp.p_pos).trans hp255
  sym_exec [to_affine_spec, black_box_spec, memset32_spec, fp_to_repr_spec]
  · -- not the identity: `x.to_repr()` with the parity of `y.to_repr()` in the top bit.
    -- The affine coordinates appear through `[p0, …, p11][k]!`; normalise, then name them, then
    -- hand the small context to `to_bytes_tail`.
    sym_close hk
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at v95_def v96_def v97_def v98_def v103_def v104_def v105_def v106_def
    generalize (Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).1 = X at v103_def v104_def v105_def v106_def hXY hXc ⊢
    generalize (Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).2 = Y at v95_def v96_def v97_def v98_def hXY ⊢
    exact to_bytes_tail X Y acc115_0 acc126_0 v95 v96 v97 v98 v103 v104 v105 v106 v116 v117 v121 v127 v128 v129 hXY hXc v95_def v96_def v97_def v98_def v103_def v104_def v105_def v106_def acc115_0_def acc126_0_def v116_def v117_def v121_def v127_def v128_def v129_def
  · -- the identity: 32 zero bytes
    sym_close hk
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at v10_def v15_def v26_def v37_def v48_def v54_def v65_def v76_def
    generalize (Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).1 = X at v10_def v15_def v26_def v37_def v48_def v54_def v65_def v76_def hXY ⊢
    generalize (Fp.toAffine (leLimbsToNat [p0, p1, p2, p3]) (leLimbsToNat [p4, p5, p6, p7]) (leLimbsToNat [p8, p9, p10, p11])).2 = Y at v10_def v15_def v26_def v37_def v48_def v54_def v65_def v76_def hXY ⊢
    exact to_bytes_identity_tail X Y acc99_0 v10 v11 v15 v16 v17 v21 v22 v26 v27 v28 v32 v33 v37 v38 v39 v43 v44 v48 v49 v50 v54 v55 v56 v60 v61 v65 v66 v67 v71 v72 v76 v77 v78 v82 v83 v87 v88 v92 hXY hbr93 acc99_0_def v92_def v88_def v87_def v83_def v82_def v78_def v77_def v76_def v72_def v71_def v67_def v66_def v65_def v61_def v60_def v56_def v55_def v54_def v50_def v49_def v48_def v44_def v43_def v39_def v38_def v37_def v33_def v32_def v28_def v27_def v26_def v22_def v21_def v17_def v16_def v15_def v11_def v10_def

end Cases.Zip2005
