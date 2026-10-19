import Cases.Zip2005.Orchard.NonIdentityFromBytes
import Cases.Zip2005.Curve.ToAffine
import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Image.F_7802340c
import Cases.Zip2005.Image.Ro

/-!
# `sinsemilla::extract_p_bottom` (0x7802340c)

`extract_p_bottom(Option<Ep>)`: a zero point by `memset`, `conditional_select(zero, pt, flag)`,
`to_affine`, `coordinates`, and the affine `x` masked by the coordinates' `is_some` byte; the
input flag byte is copied to the output's byte 0x20.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-- The point selected by the flag: the input, or the identity's `(0, 0, 0)`. -/
def selJ (f : BitVec 8) (p : List Word) : Nat × Nat × Nat :=
  if f = 1#8 then (ptX p, ptY p, ptZ p) else (0, 0, 0)

/-- `extract_p_bottom`'s four words: the affine `x` of the selected point, zero when
`coordinates` reports the identity. -/
def extractPBottomW (f : BitVec 8) (p : List Word) : List Word :=
  if (Fp.toAffine (selJ f p).1 (selJ f p).2.1 (selJ f p).2.2).1 = 0 ∧
      (Fp.toAffine (selJ f p).1 (selJ f p).2.1 (selJ f p).2.2).2 = 0
  then [0#64, 0#64, 0#64, 0#64]
  else natToLeLimbs 4 (Fp.toAffine (selJ f p).1 (selJ f p).2.1 (selJ f p).2.2).1

@[simp] theorem extractPBottomW_length (f : BitVec 8) (p : List Word) :
    (extractPBottomW f p).length = 4 := by
  unfold extractPBottomW; split <;> simp

/-- The selected point's coordinates as the executor computes them. -/
theorem selJ_eq (f : BitVec 8) (hf : f = 1#8 ∨ f = 0#8) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Word) :
    selJ f [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] =
      (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)], leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)], leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)]) := by
  rcases hf with rfl | rfl
  · simp [selJ, ptX, ptY, ptZ]
  · simp [selJ]

/-- The affine `x` cells masked by `-(is_some)`, where `is_some` is the coordinates' all-zero
test: zero for the identity, the cells otherwise. -/
theorem epb_mask (X Y : Nat) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    [BitVec.ofNat 64 (X >>> (64 * 0)) &&& -(BitVec.zeroExtend 64 (if BitVec.ofNat 64 (X >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 3)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 3)) = 0#64 then 0#8 else 1#8)), BitVec.ofNat 64 (X >>> (64 * 1)) &&& -(BitVec.zeroExtend 64 (if BitVec.ofNat 64 (X >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 3)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 3)) = 0#64 then 0#8 else 1#8)), BitVec.ofNat 64 (X >>> (64 * 2)) &&& -(BitVec.zeroExtend 64 (if BitVec.ofNat 64 (X >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 3)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 3)) = 0#64 then 0#8 else 1#8)), BitVec.ofNat 64 (X >>> (64 * 3)) &&& -(BitVec.zeroExtend 64 (if BitVec.ofNat 64 (X >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (X >>> (64 * 3)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 0)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 1)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 2)) = 0#64 ∧ BitVec.ofNat 64 (Y >>> (64 * 3)) = 0#64 then 0#8 else 1#8))] = if X = 0 ∧ Y = 0 then [0#64, 0#64, 0#64, 0#64] else natToLeLimbs 4 X := by
  simp only [Nat.reduceMul, Nat.shiftRight_zero]
  have hx := cells4_eq_zero_iff X hX
  have hy := cells4_eq_zero_iff Y hY
  by_cases h : X = 0 ∧ Y = 0
  · have hc : (BitVec.ofNat 64 X = 0#64 ∧ BitVec.ofNat 64 (X >>> 64) = 0#64 ∧ BitVec.ofNat 64 (X >>> 128) = 0#64 ∧ BitVec.ofNat 64 (X >>> 192) = 0#64) ∧
        (BitVec.ofNat 64 Y = 0#64 ∧ BitVec.ofNat 64 (Y >>> 64) = 0#64 ∧ BitVec.ofNat 64 (Y >>> 128) = 0#64 ∧ BitVec.ofNat 64 (Y >>> 192) = 0#64) :=
      ⟨hx.mpr h.1, hy.mpr h.2⟩
    obtain ⟨⟨h0, h1, h2, h3⟩, ⟨h4, h5, h6, h7⟩⟩ := hc
    rw [if_pos ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, if_pos h]
    simp
  · have hc : ¬ (BitVec.ofNat 64 X = 0#64 ∧ BitVec.ofNat 64 (X >>> 64) = 0#64 ∧ BitVec.ofNat 64 (X >>> 128) = 0#64 ∧ BitVec.ofNat 64 (X >>> 192) = 0#64 ∧
        BitVec.ofNat 64 Y = 0#64 ∧ BitVec.ofNat 64 (Y >>> 64) = 0#64 ∧ BitVec.ofNat 64 (Y >>> 128) = 0#64 ∧ BitVec.ofNat 64 (Y >>> 192) = 0#64) := by
      intro hc; exact h ⟨hx.mp ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩, hy.mp ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2⟩⟩
    rw [if_neg hc, if_neg h, natToLeLimbs_cells4,
      show (-BitVec.zeroExtend 64 1#8 : Word) = BitVec.allOnes 64 by decide,
      BitVec.and_allOnes, BitVec.and_allOnes, BitVec.and_allOnes, BitVec.and_allOnes]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem extract_p_bottom_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out a1 : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 c : Word) (f : BitVec 8) (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7802340c#64) (hcode : CodeAt F_7802340c.base F_7802340c.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3a0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hA : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, replaceByte c 0 f] s)
    (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi a1 13) (hf : f = 1#8 ∨ f = 0#8)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 5)
    (hd0 : Disjoint (sp - 0x3a0#64) 116 out 5) (hdA : Disjoint (sp - 0x3a0#64) 116 a1 13)
    (heA : Disjoint out 5 a1 13)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3a0#64, 116), (out, 5)] s t →
      Region out (extractPBottomW f [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] ++
        [replaceByte O[4]! 0 f]) t →
      SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x3a0#64) 116 := hstk.frame 116 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x170#64) 46 := hokW.sub' 70 46 (by decide) (by bv_omega)
  -- the frame: [8, 0x68) the selection, [0x68, 0xc8) the zero point, [0xc8, 0x110) the affine
  -- coordinates with their flag byte, [0x110, 0x150) the affine point, saved registers at
  -- 0x150..0x170
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x168#64) 12 s
  obtain ⟨FZ, hFZ, hFZl⟩ := Region.exists_junk (sp - 0x108#64) 12 s
  obtain ⟨FC, hFC, hFCl⟩ := Region.exists_junk (sp - 0xa8#64) 9 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hokFS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x168#64) 12 := hokF.sub' 1 12 (by decide) (by bv_omega)
  have hokFZ : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x108#64) 12 := hokF.sub' 13 12 (by decide) (by bv_omega)
  have hokFC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa8#64) 9 := hokF.sub' 25 9 (by decide) (by bv_omega)
  have hokFP : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 8 := hokF.sub' 34 8 (by decide) (by bv_omega)
  have hokFR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokF.sub' 42 4 (by decide) (by bv_omega)
  have hokA12 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12 := hokA.sub' 0 12 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x3a0#64, 116), (out, 5)] s
  have hlo := hstk.lo
  sym_exec [memset96_spec'] stop [0x78023440]
  rw [extractByte_replaceByte _ _ (by decide)] at v13_def
  sym_reframe
  sym_exec [conditional_select_spec_byte, to_affine_spec, coordinates_spec']
  -- the coordinates' cells over the selected point's affine coordinates
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at post16_12 post16_13 post16_14 post16_15
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at post16_16 post16_17 post16_18 post16_19
  have c0 : post16_0 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).1 >>> (64 * 0)) := by rw [← post16_12]
  have c1 : post16_1 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).1 >>> (64 * 1)) := by rw [← post16_13]
  have c2 : post16_2 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).1 >>> (64 * 2)) := by rw [← post16_14]
  have c3 : post16_3 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).1 >>> (64 * 3)) := by rw [← post16_15]
  have c4 : post16_4 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).2 >>> (64 * 0)) := by rw [← post16_16]
  have c5 : post16_5 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).2 >>> (64 * 1)) := by rw [← post16_17]
  have c6 : post16_6 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).2 >>> (64 * 2)) := by rw [← post16_18]
  have c7 : post16_7 = BitVec.ofNat 64 ((Fp.toAffine (leLimbsToNat [(if f = 1#8 then p0 else 0#64), (if f = 1#8 then p1 else 0#64), (if f = 1#8 then p2 else 0#64), (if f = 1#8 then p3 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p4 else 0#64), (if f = 1#8 then p5 else 0#64), (if f = 1#8 then p6 else 0#64), (if f = 1#8 then p7 else 0#64)]) (leLimbsToNat [(if f = 1#8 then p8 else 0#64), (if f = 1#8 then p9 else 0#64), (if f = 1#8 then p10 else 0#64), (if f = 1#8 then p11 else 0#64)])).2 >>> (64 * 3)) := by rw [← post16_19]
  rw [extractByte_replaceByte _ _ (by decide)] at v17_def
  have e4 : [v23, v24, v25, v26] = extractPBottomW f [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] := by
    rw [← v23_def, ← v24_def, ← v25_def, ← v26_def, ← v18_def, ← v17_def, c0, c1, c2, c3, c4, c5, c6, c7]
    unfold extractPBottomW; rw [selJ_eq f hf]
    exact epb_mask _ _ (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).1
      (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).2
  have e1 : v31 = replaceByte O[4]! 0 f := by rw [← v31_def, ← v13_def]; simp
  have hRo : Region out (extractPBottomW f [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] ++ [replaceByte O[4]! 0 f]) s_38 := by
    rw [← e4, ← e1]; exact hR1
  sym_close hk

end Cases.Zip2005
