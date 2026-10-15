/-
  `Zip2005Instance::parse_rk` (0x7801cb44): `Ep::from_bytes_unchecked` on the 32 bytes at
  `a1 + 0x20`, then `Option<(Ep, [u8; 32])>` at `a0`: the tag, and on `Some` the twelve
  words of the point followed by the four words of the input bytes. The value travels
  `memcpy` 0x60 / 0x20 into a buffer, 0x80 to a second buffer, 0x80 to `sp + 7` (the
  `Option` payload at offset 8 of a 7-shifted temporary) and 0x80 back to `a0 + 8`.
-/
import Cases.Zip2005.Curve.FromBytesUnchecked
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemcpyOff
import Cases.Zip2005.Image.F_7801cb44
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem parse_rk_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 17) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hpc : s.pc = 0x7801cb44#64) (hcode : CodeAt F_7801cb44.base F_7801cb44.prog s)
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
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x960 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region (a1 + 32#64) [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi (a1 + 32#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 17)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x960#64) 300 a0 13) (hd_a1 : Disjoint (sp - 0x960#64) 300 (a1 + 32#64) 4)
    (hd_tb : Disjoint (sp - 0x960#64) 300 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x960#64) 300 iptr 138)
    (hd_g0 : Disjoint (sp - 0x960#64) 300 g0 1024) (hd_g1 : Disjoint (sp - 0x960#64) 300 g1 1024)
    (hd_g2 : Disjoint (sp - 0x960#64) 300 g2 1024) (hd_g3 : Disjoint (sp - 0x960#64) 300 g3 516)
    (he_a1 : Disjoint a0 17 (a1 + 32#64) 4) (he_tb : Disjoint a0 17 0x780488a8#64 10)
    (he_iptr : Disjoint a0 17 iptr 138)
    (he_g0 : Disjoint a0 17 g0 1024) (he_g1 : Disjoint a0 17 g1 1024)
    (he_g2 : Disjoint a0 17 g2 1024) (he_g3 : Disjoint a0 17 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 tag : Word) (f : BitVec 8)
      (L : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x960#64, 300), (a0, 17)] s t →
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f →
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) →
      tag = BitVec.zeroExtend 64 f → L.length = 16 →
      (f = 1#8 → L = [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, b0, b1, b2, b3]) →
      Region a0 (tag :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x960#64) 300 := hstk.frame 300 (by decide)
  have hok_a1' := hok_a1.toText
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1c0#64) 56 := hokW.sub' 244 56 (by decide) (by bv_omega)
  -- the frame: [0, 0x60) the point copy and [0x60, 0x80) the key bytes (buffer A, 18 words with
  -- the spill slot), [0x90, 0x110) buffer B, [0x110, 0x130) the four words of the key,
  -- [0x130, 0x198) the decoded point, saved registers at 0x198..0x1b8
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
  have hu := Unchanged.refl [(sp - 0x960#64, 300), (a0, 17)] s
  have hlo := hstk.lo
  sym_exec [ep_from_bytes_unchecked_spec, memcpy96_spec, memcpy32_spec, memcpy128_spec,
    memcpy128_to7_spec, memcpy128_from7_spec, hpb, hpp, hprz, hpaf]
  all_goals rw [extractByte_replaceByte _ _ (by decide)] at v105_def
  all_goals rcases FromBytesPost.flag01 post104_18 with hf | hf <;> subst v105_def <;>
    rw [hf] at hbr106
  all_goals try rw [hf] at hbr109
  all_goals first
    | exact absurd hbr106 (by decide)
    | exact absurd hbr109 (by decide)
    | skip
  -- the key's words, reassembled from its bytes
  all_goals
    have hb3 : v29 = b3 := by
      rw [← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def, ← v23_def,
        ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def,
        ← v14_def, ← v13_def, ← v12_def, ← v11_def, ← v10_def, ← v9_def, ← v8_def]
      exact bytes_word b3
  all_goals
    have hb2 : v51 = b2 := by
      rw [← v51_def, ← v50_def, ← v49_def, ← v48_def, ← v47_def, ← v46_def, ← v45_def,
        ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def,
        ← v36_def, ← v35_def, ← v34_def, ← v33_def, ← v32_def, ← v31_def, ← v30_def]
      exact bytes_word b2
  all_goals
    have hb1 : v73 = b1 := by
      rw [← v73_def, ← v72_def, ← v71_def, ← v70_def, ← v69_def, ← v68_def, ← v67_def,
        ← v66_def, ← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def,
        ← v58_def, ← v57_def, ← v56_def, ← v55_def, ← v54_def, ← v53_def, ← v52_def]
      exact bytes_word b1
  all_goals
    have hb0 : v95 = b0 := by
      rw [← v95_def, ← v94_def, ← v93_def, ← v92_def, ← v91_def, ← v90_def, ← v89_def,
        ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def,
        ← v80_def, ← v79_def, ← v78_def, ← v77_def, ← v76_def, ← v75_def, ← v74_def]
      exact bytes_word b0
  all_goals rw [hb0, hb1, hb2, hb3] at post104_18
  -- the point decoded (`Some`): the three copies through the 7-byte offset round-trip
  all_goals try simp only [List.getElem!_cons_zero, List.getElem!_cons_succ, rt_first, rt_mid,
    rt_last] at hR1
  -- `None`: only the tag is written
  · sym_close (hk _ post104_0 post104_1 post104_2 post104_3 post104_4 post104_5 post104_6
      post104_7 post104_8 post104_9 post104_10 post104_11 _ post104_12 _)
    all_goals first
      | rfl
      | (intro h; rw [hf] at h; exact absurd h (by decide))
  -- `Some`: the point and the key bytes, through the 7-byte offset and back
  · sym_close (hk _ post104_0 post104_1 post104_2 post104_3 post104_4 post104_5 post104_6
      post104_7 post104_8 post104_9 post104_10 post104_11 _ post104_12 _)
    all_goals rfl

end Cases.Zip2005
