/-
  `SpendValidatingKey::from_bytes` (0x78022514): a 32-byte slice; `None` unless the length is
  32, the bytes are not all zero (`memcmp` against a zero constant in `.rodata`) and the top
  bit of the last byte is clear; then `Ep::from_bytes_unchecked` on the words assembled from
  the bytes, and the `Option<(Ep, [u8; 32])>` at `a0` as in `parse_rk`: the tag, and on `Some`
  the point and the bytes, moved through the 7-byte offset and back.
-/
import Cases.Zip2005.Curve.FromBytesUnchecked
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemcpyOff
import Cases.Zip2005.Runtime.Memcmp
import Cases.Zip2005.Image.F_78022514
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem slt_sign_byte (w : Word) : (BitVec.signExtend 64 (extractByte w 7)).slt 0#64 = w.msb := by
  rw [BitVec.slt_zero_eq_msb, BitVec.msb_signExtend]
  simp [extractByte, BitVec.msb_eq_getLsbD_last]

/-- `memcmp`'s result, sign-extended from 32 bits and added to zero, as the guest does. -/
theorem sext32_add_zero (x : Word) (h : BitVec.signExtend 64 (BitVec.truncate 32 x) = x) :
    BitVec.signExtend 64 (BitVec.truncate 32 x + BitVec.truncate 32 0#64) = x := by
  rw [show BitVec.truncate 32 0#64 = 0#32 from rfl, BitVec.add_zero, h]

/-- The `Option<SpendValidatingKey>` written at the output: the tag `tag` and sixteen further
words `L`. `None` (tag 0) when the bytes are all zero or the last byte's top bit is set;
otherwise the outcome of `Ep::from_bytes_unchecked` on the bytes, `L` holding the point and
the bytes when it succeeds. -/
def SvkPost (b0 b1 b2 b3 : Word) (tag : Word) (L : List Word) : Prop :=
  L.length = 16 ∧
    ((tag = 0#64 ∧ ([b0, b1, b2, b3] = [0#64, 0#64, 0#64, 0#64] ∨ b3.msb = true)) ∨
      ([b0, b1, b2, b3] ≠ [0#64, 0#64, 0#64, 0#64] ∧ b3.msb = false ∧
        ∃ (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (f : BitVec 8),
          FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f ∧
          leLimbsToNat [z0, z1, z2, z3] =
            (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0
              else Fp.R) ∧
          tag = BitVec.zeroExtend 64 f ∧
          (f = 1#8 → L = [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, b0, b1, b2, b3])))

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem spend_validating_key_from_bytes_spec {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 17) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → Safe P u)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → Safe P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x78022514#64) (hcode : CodeAt F_78022514.base F_78022514.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeU : CodeAt F_78026928.base F_78026928.prog s)
    (hcodeF : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x960 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (ha2 : s.getReg .x12 = 32#64)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 17)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x960#64) 300 a0 13) (hd_a1 : Disjoint (sp - 0x960#64) 300 a1 4)
    (hd_tb : Disjoint (sp - 0x960#64) 300 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x960#64) 300 iptr 138)
    (hd_g0 : Disjoint (sp - 0x960#64) 300 g0 1024) (hd_g1 : Disjoint (sp - 0x960#64) 300 g1 1024)
    (hd_g2 : Disjoint (sp - 0x960#64) 300 g2 1024) (hd_g3 : Disjoint (sp - 0x960#64) 300 g3 516)
    (he_a1 : Disjoint a0 17 a1 4) (he_tb : Disjoint a0 17 0x780488a8#64 10)
    (he_iptr : Disjoint a0 17 iptr 138)
    (he_g0 : Disjoint a0 17 g0 1024) (he_g1 : Disjoint a0 17 g1 1024)
    (he_g2 : Disjoint a0 17 g2 1024) (he_g3 : Disjoint a0 17 g3 516)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x960#64, 300), (a0, 17)] s t →
      SvkPost b0 b1 b2 b3 tag L → Region a0 (tag :: L) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x960#64) 300 := hstk.frame 300 (by decide)
  have hok_a1' := hok_a1.toText
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1c0#64) 56 := hokW.sub' 244 56 (by decide) (by bv_omega)
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0x1c0#64) 18 s
  obtain ⟨FB, hFB, hFBl⟩ := Region.exists_junk (sp - 0x130#64) 16 s
  obtain ⟨FW, hFW, hFWl⟩ := Region.exists_junk (sp - 0xb0#64) 4 s
  obtain ⟨FP, hFP, hFPl⟩ := Region.exists_junk (sp - 0x90#64) 13 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x28#64) 5 s
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1c0#64) 18 := hokF.sub' 0 18 (by decide) (by bv_omega)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 16 := hokF.sub' 18 16 (by decide) (by bv_omega)
  have hokWd : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 4 := hokF.sub' 34 4 (by decide) (by bv_omega)
  have hokP : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x90#64) 13 := hokF.sub' 38 13 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x28#64) 5 := hokF.sub' 51 5 (by decide) (by bv_omega)
  -- the 32 zero bytes the key is compared against, in `.rodata`
  have hZ : Region 0x78001790#64 [0#64, 0#64, 0#64, 0#64] s :=
    (hro.get 11 (by decide)).sub 50 4 (by decide) rfl
  have hokZ : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001790#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 50 4 (by decide) (by decide)
  have he_z : Disjoint a0 17 0x78001790#64 4 := by
    have h1 := hok0.offCode; have h2 := hok0.inMem
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_ofNat, Ro.layout_roBase, Ro.layout_textHi, SP1_MAX_MEMORY, Nat.reducePow,
      Nat.reduceMod] at h1 h2 ⊢
    omega
  have hf_z : Disjoint a1 4 0x78001790#64 4 := by
    have h1 := hok_a1.offCode; have h2 := hok_a1.inMem
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_ofNat, Ro.layout_roBase, Ro.layout_textHi, SP1_MAX_MEMORY, Nat.reducePow,
      Nat.reduceMod] at h1 h2 ⊢
    omega
  have hu := Unchanged.refl [(sp - 0x960#64, 300), (a0, 17)] s
  have hlo := hstk.lo
  sym_exec [ep_from_bytes_unchecked_spec, memcmp4_spec, memcpy96_spec, memcpy32_spec,
    memcpy128_spec, memcpy128_to7_spec, memcpy128_from7_spec, hpb, hpp, hprz, hpaf]
  all_goals rw [sext32_add_zero _ post17_5] at v18_def
  -- the bytes are all zero: `None`
  · have hz : [b0, b1, b2, b3] = [0#64, 0#64, 0#64, 0#64] :=
      post17_4.mp (v18_def.trans (beq_iff_eq.mp hbr20))
    sym_close (hk _ _ _)
    exact ⟨rfl, Or.inl ⟨rfl, Or.inl hz⟩⟩
  -- the last byte's top bit is set: `None`
  · have hm : b3.msb = true := by rw [← slt_sign_byte, v10_def]; exact hbr21
    sym_close (hk _ _ _)
    exact ⟨rfl, Or.inl ⟨rfl, Or.inr hm⟩⟩
  all_goals
    have hnz : [b0, b1, b2, b3] ≠ [0#64, 0#64, 0#64, 0#64] := fun h =>
      hbr20 (beq_iff_eq.mpr (v18_def.symm.trans (post17_4.mpr h)))
  all_goals
    have hm : b3.msb = false := by
      rw [← slt_sign_byte, v10_def]; exact Bool.eq_false_iff.mpr hbr21
  all_goals rw [extractByte_replaceByte _ _ (by decide)] at v119_def
  -- the key's words, reassembled from its bytes
  all_goals
    have hb3 : v43 = b3 := by
      rw [← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def,
        ← v36_def, ← v35_def, ← v34_def, ← v33_def, ← v32_def, ← v31_def, ← v30_def, ← v29_def,
        ← v28_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def, ← v23_def, ← v22_def]
      exact bytes_word b3
  all_goals
    have hb2 : v65 = b2 := by
      rw [← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def,
        ← v58_def, ← v57_def, ← v56_def, ← v55_def, ← v54_def, ← v53_def, ← v52_def, ← v51_def,
        ← v50_def, ← v49_def, ← v48_def, ← v47_def, ← v46_def, ← v45_def, ← v44_def]
      exact bytes_word b2
  all_goals
    have hb1 : v87 = b1 := by
      rw [← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def,
        ← v80_def, ← v79_def, ← v78_def, ← v77_def, ← v76_def, ← v75_def, ← v74_def, ← v73_def,
        ← v72_def, ← v71_def, ← v70_def, ← v69_def, ← v68_def, ← v67_def, ← v66_def]
      exact bytes_word b1
  all_goals
    have hb0 : v109 = b0 := by
      rw [← v109_def, ← v108_def, ← v107_def, ← v106_def, ← v105_def, ← v104_def, ← v103_def,
        ← v102_def, ← v101_def, ← v100_def, ← v99_def, ← v98_def, ← v97_def, ← v96_def,
        ← v95_def, ← v94_def, ← v93_def, ← v92_def, ← v91_def, ← v90_def, ← v89_def, ← v88_def]
      exact bytes_word b0
  all_goals rw [hb0, hb1, hb2, hb3] at post118_18
  all_goals rcases FromBytesPost.flag01 post118_18 with hf | hf <;> subst v119_def <;>
    rw [hf] at hbr120
  all_goals try rw [hf] at hbr123
  all_goals first
    | exact absurd hbr120 (by decide)
    | exact absurd hbr123 (by decide)
    | skip
  -- `Some`: the point and the key bytes, through the 7-byte offset and back
  all_goals try simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, rt_first, rt_mid,
    rt_last] at hR1
  all_goals sym_close (hk _ _ _)
  all_goals refine ⟨rfl, Or.inr ⟨hnz, hm, post118_0, post118_1, post118_2, post118_3, post118_4,
    post118_5, post118_6, post118_7, post118_8, post118_9, post118_10, post118_11, post118_12,
    post118_18, post118_19, by rw [hf]; rfl, ?_⟩⟩
  all_goals first
    | exact fun _ => rfl
    | exact fun h => by rw [hf] at h; exact absurd h (by decide)

end Cases.Zip2005
