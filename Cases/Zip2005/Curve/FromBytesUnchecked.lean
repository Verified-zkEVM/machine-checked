import Cases.Zip2005.Curve.FromBytes
import Cases.Zip2005.Image.F_78026928
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Ep::from_bytes_unchecked`

`EpAffine::from_bytes` into a stack slot, then `CtOption::map(to_curve)`: the affine
coordinates masked by the flag, and `z = R` unless the point is the affine identity `(0, 0)`
(then `z = 0`), decided through sixteen `black_box` folds.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

theorem shl2_shr2 (x : Word) : (x <<< 2) >>> 2 = x &&& 0x3fffffffffffffff#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and]
  interval_cases i <;> simp

theorem bw_add_ones (a : Bool) :
    bw a + 18446744073709551615#64 = if a then 0#64 else 18446744073709551615#64 := by
  cases a <;> decide

/-- `(flag - 1) &&& c`: `c` under a clear flag, `0` under a set one. -/
theorem and_notmask (c : Word) (a : Bool) :
    (bw a + 18446744073709551615#64) &&& c = if a then 0#64 else c := by
  rw [bw_add_ones]
  cases a
  · simp only [Bool.false_eq_true, if_false]; rw [BitVec.and_comm]; exact and_allOnes' c
  · simp only [if_true]; exact BitVec.zero_and

theorem zext_byte01 {f : BitVec 8} (h : f = 1#8 ∨ f = 0#8) :
    BitVec.zeroExtend 64 f = bw (decide (f = 1#8)) := by
  rcases h with h | h <;> subst h <;> decide

theorem FromBytesPost.flag01 {b0 b1 b2 b3 : Word} {x y : Nat} {f : BitVec 8}
    (h : FromBytesPost b0 b1 b2 b3 x y f) : f = 1#8 ∨ f = 0#8 := by
  rcases h.2.2 with ⟨h1, _⟩ | ⟨h0, _⟩
  · exact Or.inl h1
  · exact Or.inr h0

/-- `CtOption::map` zeroes the coordinates under a clear flag; the postcondition survives. -/
theorem fbu_post {b0 b1 b2 b3 x0 x1 x2 x3 y0 y1 y2 y3 : Word} {f : BitVec 8} {c : Bool}
    (hpost : FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f)
    (hc : decide (f = 1#8) = c) :
    FromBytesPost b0 b1 b2 b3
      (leLimbsToNat [if c then x0 else 0#64, if c then x1 else 0#64, if c then x2 else 0#64,
        if c then x3 else 0#64])
      (leLimbsToNat [if c then y0 else 0#64, if c then y1 else 0#64, if c then y2 else 0#64,
        if c then y3 else 0#64]) f := by
  cases c
  · simp only [Bool.false_eq_true, if_false]
    have hf : f = 0#8 := by
      rcases hpost.flag01 with h | h
      · exact absurd (decide_eq_true h) (by rw [hc]; decide)
      · exact h
    unfold FromBytesPost at hpost ⊢
    dsimp only at hpost ⊢
    refine ⟨Fp.p_pos, Fp.p_pos, ?_⟩
    rcases hpost.2.2 with ⟨h1, _⟩ | ⟨h0, hr⟩
    · exact absurd h1 (by rw [hf]; decide)
    · exact Or.inr ⟨h0, hr⟩
  · simp only [if_true]; exact hpost

/-- `to_curve`: `z = R`, or `0` at the affine identity `(0, 0)`. -/
theorem fbu_z {x0 x1 x2 x3 y0 y1 y2 y3 : Word} {xz yz : Bool}
    (hxz : (x3 == 0#64 && (x2 == 0#64 && (x1 == 0#64 && x0 == 0#64))) = xz)
    (hyz : (y3 == 0#64 && (y2 == 0#64 && (y1 == 0#64 && y0 == 0#64))) = yz) :
    leLimbsToNat [if (yz && xz) then 0#64 else 3780891978758094845#64,
      if (yz && xz) then 0#64 else 11037255111966004397#64,
      if (yz && xz) then 0#64 else 18446744073709551615#64,
      if (yz && xz) then 0#64 else 4611686018427387903#64] =
      if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R := by
  have ex : leLimbsToNat [x0, x1, x2, x3] = 0 ↔ xz = true := by
    rw [limbs_zero4, ← hxz]; simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩, fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩⟩
  have ey : leLimbsToNat [y0, y1, y2, y3] = 0 ↔ yz = true := by
    rw [limbs_zero4, ← hyz]; simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩, fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩⟩
  cases xz <;> cases yz
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    rw [if_neg (fun hh => Bool.false_ne_true (ex.mp hh.1))]; exact Fp.limbs_R
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    rw [if_neg (fun hh => Bool.false_ne_true (ex.mp hh.1))]; exact Fp.limbs_R
  · simp only [Bool.false_and, Bool.false_eq_true, if_false]
    rw [if_neg (fun hh => Bool.false_ne_true (ey.mp hh.2))]; exact Fp.limbs_R
  · simp only [Bool.and_self, if_true]
    rw [if_pos ⟨ex.mpr rfl, ey.mpr rfl⟩]; rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `Ep::from_bytes_unchecked` (`0x78026928`): `from_bytes`, then `to_curve`. The output is
    the projective point `(x, y, z)` with the flag; `x, y` satisfy `FromBytesPost` (they are
    zeroed under a clear flag, which the postcondition allows) and `z` is `R` (Montgomery one)
    unless `(x, y) = (0, 0)`, the affine identity, where `z = 0`. -/
theorem ep_from_bytes_unchecked_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 13) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hpc : s.pc = 0x78026928#64) (hcode : CodeAt F_78026928.base F_78026928.prog s)
    (hcodeF : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x7a0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.textLo Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 13)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x7a0#64) 244 a0 13) (hd_a1 : Disjoint (sp - 0x7a0#64) 244 a1 4)
    (hd_tb : Disjoint (sp - 0x7a0#64) 244 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x7a0#64) 244 iptr 138)
    (hd_g0 : Disjoint (sp - 0x7a0#64) 244 g0 1024) (hd_g1 : Disjoint (sp - 0x7a0#64) 244 g1 1024)
    (hd_g2 : Disjoint (sp - 0x7a0#64) 244 g2 1024) (hd_g3 : Disjoint (sp - 0x7a0#64) 244 g3 516)
    (he_a1 : Disjoint a0 13 a1 4) (he_tb : Disjoint a0 13 0x780488a8#64 10)
    (he_iptr : Disjoint a0 13 iptr 138)
    (he_g0 : Disjoint a0 13 g0 1024) (he_g1 : Disjoint a0 13 g1 1024)
    (he_g2 : Disjoint a0 13 g2 1024) (he_g3 : Disjoint a0 13 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (f : BitVec 8),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x7a0#64, 244), (a0, 13)] s t →
      Region a0 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, replaceByte O[12]! 0 f] t →
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f →
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) →
      SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x7a0#64) 244 := hstk.frame 244 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 22 := hokW.sub' 222 22 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 9 := hokF.sub' 0 9 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 9 13 (by decide) (by bv_omega)
  obtain ⟨Sl, hSl, hSll⟩ := Region.exists_junk (sp - 0xb0#64) 9 s
  obtain ⟨Sv, hSv, hSvl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x7a0#64, 244), (a0, 13)] s
  have hlo := hstk.lo
  -- the output region survives the callee (its frame, its output slot), and the callee's frame
  -- facts against the fixed table address: stated in the shapes the executor needs
  have hsurv : Disjoint a0 13 (sp + 18446744073709551440#64 - 1776#64) 222 := by
    rw [MachineChecked.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd0 ⊢
    omega
  have hsurv2 : Disjoint a0 13 (sp + 18446744073709551440#64) 9 := by
    rw [MachineChecked.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd0 ⊢
    omega
  have hd_tb' : Disjoint (sp + 18446744073709551440#64 - 1776#64) 222 0x780488a8#64 10 := by
    rw [MachineChecked.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  have he_tb' : Disjoint (sp + 18446744073709551440#64) 9 0x780488a8#64 10 := by
    rw [MachineChecked.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  sym_exec [ep_affine_from_bytes_spec, black_box_spec, hpb, hpp, hprz]
  -- the flag and the `CtOption::map` masks
  have h01 := post18_14.flag01
  obtain ⟨c, hc⟩ : ∃ c, decide (post18_8 = 1#8) = c := ⟨_, rfl⟩
  have hv19e : BitVec.zeroExtend 64 post18_8 = v19 := by
    rw [← v19_def, extractByte_replaceByte _ 0 (by decide)]
  have hv19 : bw c = v19 := by rw [← hv19e, zext_byte01 h01, hc]
  have hv20 : -(bw c) = v20 := by rw [← v20_def, ← hv19]
  have h25 : (if c then post18_0 else 0#64) = v25 := by rw [← v25_def, ← hv20, and_negbw]
  have h26 : (if c then post18_1 else 0#64) = v26 := by rw [← v26_def, ← hv20, and_negbw]
  have h27 : (if c then post18_2 else 0#64) = v27 := by rw [← v27_def, ← hv20, and_negbw]
  have h28 : (if c then post18_3 else 0#64) = v28 := by rw [← v28_def, ← hv20, and_negbw]
  have h33 : (if c then post18_4 else 0#64) = v33 := by rw [← v33_def, ← hv20, and_negbw]
  have h34 : (if c then post18_5 else 0#64) = v34 := by rw [← v34_def, ← hv20, and_negbw]
  have h35 : (if c then post18_6 else 0#64) = v35 := by rw [← v35_def, ← hv20, and_negbw]
  have h36 : (if c then post18_7 else 0#64) = v36 := by rw [← v36_def, ← hv20, and_negbw]
  -- `to_curve`: the identity test through `black_box`
  obtain ⟨xz, hxz⟩ : ∃ z, (v28 == 0#64 && (v27 == 0#64 && (v26 == 0#64 && v25 == 0#64))) = z := ⟨_, rfl⟩
  obtain ⟨yz, hyz⟩ : ∃ z, (v36 == 0#64 && (v35 == 0#64 && (v34 == 0#64 && v33 == 0#64))) = z := ⟨_, rfl⟩
  have h71 : bw xz = v71 := by
    rw [← v71_def, ← v67_def, ← v66_def, ← v62_def, ← v61_def, ← v57_def, ← v56_def, ← v52_def,
      ← v51_def, ← v47_def, ← v46_def, ← v42_def, ← v41_def, ← v37_def, ← hxz]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw]
  have h102 : bw yz = v102 := by
    rw [← v102_def, ← v101_def, ← v97_def, ← v96_def, ← v92_def, ← v91_def, ← v87_def, ← v86_def,
      ← v82_def, ← v81_def, ← v77_def, ← v76_def, ← v72_def, ← hyz]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw]
  have h111 : bw (yz && xz) = v111 := by
    rw [← v111_def, ← v107_def, ← v106_def, ← h102, ← h71, bb_bw, and_bw, and255_bw, bb_bw, and255_bw]
  -- `z`: `R`, or `0` at the identity
  have h119 : (if (yz && xz) then 0#64 else 3780891978758094845#64) = v119 := by
    rw [← v119_def, ← h111, and_notmask]
  have h120 : (if (yz && xz) then 0#64 else 11037255111966004397#64) = v120 := by
    rw [← v120_def, ← h111, and_notmask]
  have h122 : (if (yz && xz) then 0#64 else 4611686018427387903#64) = v122 := by
    rw [← v122_def, ← v121_def, shl2_shr2, ← h111, and_notmask]
  have hz2 : (if (yz && xz) then 0#64 else 18446744073709551615#64) =
      v111 + 18446744073709551615#64 := by
    rw [← h111, bw_add_ones]
  rw [← hv19e, trunc8_zext] at v135_def
  subst v135_def
  sym_close hk _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · rw [← h25, ← h26, ← h27, ← h28, ← h33, ← h34, ← h35, ← h36]
    exact fbu_post post18_14 hc
  · rw [← h119, ← h120, ← h122, ← hz2]
    exact fbu_z hxz hyz

end Cases.Zip2005
