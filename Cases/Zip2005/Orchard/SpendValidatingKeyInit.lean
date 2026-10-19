import Cases.Zip2005.Curve.FromBytesInit
import Cases.Zip2005.Orchard.SpendValidatingKey

/-!
# `SpendValidatingKey::from_bytes`, the run's first decompression, building `FP_TABLES`
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `SpendValidatingKey::from_bytes` (`0x78022514`) from the `Once` uninitialised: `None` early
    (the tables untouched), or through `ep_from_bytes_unchecked_init_spec` (the tables built). -/
theorem spend_validating_key_from_bytes_init_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 w0 w1 w2 w3 w4 w5 w6 w7 w8 : Word) (O : List Word)
    (hOl : O.length = 17)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    {c : Word → Option Instr} (hcc : s.code = c)
    (halloc : SqAlloc G n P c) (hrealloc_g : SqReallocG G n P c) (halloci : SqAllocInv G n P c)
    (hrealloc : SqRealloc G n P c)
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
    (hcodeO : CodeAt F_78032b38.base F_78032b38.prog s)
    (hcodeN : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeFI : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMs : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeD : CodeAt F_78032560.base F_78032560.prog s) (hcodeG : CodeAt F_78032614.base F_78032614.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x960 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (ha2 : s.getReg .x12 = 32#64)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 17)
    (hbelow0 : a0.toNat + 8 * 17 ≤ 0x78040620) (hbelow1 : a1.toNat + 8 * 4 ≤ 0x78040620)
    -- `FP_TABLES`, uninitialised (`Once` state byte 0 at 0x780488f0, padding zero)
    (hT0 : Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] s)
    (hd0 : Disjoint (sp - 0x960#64) 300 a0 13) (hd_a1 : Disjoint (sp - 0x960#64) 300 a1 4)
    (hd_tb : Disjoint (sp - 0x960#64) 300 0x780488a8#64 10)
    (he_a1 : Disjoint a0 17 a1 4) (he_tb : Disjoint a0 17 0x780488a8#64 10)
    (hk : ∀ (t : MachineState) (tag : Word) (Lo : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x960#64, 300), (a0, 17), (0x780488a8#64, 10),
        (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      SvkPost b0 b1 b2 b3 tag Lo → Region a0 (tag :: Lo) t →
      ∀ (iptr tg0 tg1 tg2 tg3 hx : Word) (IV G0 G1 G2 G3 : List Word),
      ((tag = 0#64 ∧ Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] t ∧
          Run.HeapAt L t) ∨
        (Region 0x780488a8#64 [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64, hx, 2#64] t ∧
          Region iptr IV t ∧ Region tg0 G0 t ∧ Region tg1 G1 t ∧ Region tg2 G2 t ∧ Region tg3 G3 t ∧
          IV.length = 138 ∧ G0.length = 1024 ∧ G1.length = 1024 ∧ G2.length = 1024 ∧ G3.length = 516 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 ∧ RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 ∧ RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 ∧
          0x78048980 ≤ iptr.toNat ∧ iptr.toNat + 1104 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg0.toNat ∧ tg0.toNat + 0x2000 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg1.toNat ∧ tg1.toNat + 0x2000 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg2.toNat ∧ tg2.toNat + 0x2000 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg3.toNat ∧ tg3.toNat + 0x1020 ≤ 0x1c00000000 ∧
          Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L) t)) →
      SafeN G n P t) :
    SafeN G n P s := by
  subst hcc
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
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_ofNat, Ro.layout_roBase, Ro.layout_textHi, SP1_MAX_MEMORY, Nat.reducePow,
      Nat.reduceMod] at h1 h2 ⊢
    omega
  have hf_z : Disjoint a1 4 0x78001790#64 4 := by
    have h1 := hok_a1.offCode; have h2 := hok_a1.inMem
    simp only [MachineChecked.RiscV.Sym.Disjoint, BitVec.toNat_ofNat, Ro.layout_roBase, Ro.layout_textHi, SP1_MAX_MEMORY, Nat.reducePow,
      Nat.reduceMod] at h1 h2 ⊢
    omega
  have hu := Unchanged.refl [(sp - 0x960#64, 300), (a0, 17), (0x780488a8#64, 10), (0x78040620#64, 4162),
    (0x78048980#64, 14780690128)] s
  have hokTb : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 10 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokAr : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hbo : (sp + 18446744073709551472#64).toNat + 8 * 13 ≤ 0x78040620 := by
    have h1 := hstk.lo; have h2 := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    rw [MachineChecked.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide), BitVec.toNat_sub]; simp; omega
  have hlo := hstk.lo
  sym_exec [ep_from_bytes_unchecked_init_spec, memcmp4_spec, memcpy96_spec, memcpy32_spec,
    memcpy128_spec, memcpy128_to7_spec, memcpy128_from7_spec, hpb, hpp, hprz, hpaf]
  all_goals rw [sext32_add_zero _ post17_5] at v18_def
  -- the bytes are all zero: `None`
  · have hz : [b0, b1, b2, b3] = [0#64, 0#64, 0#64, 0#64] :=
      post17_4.mp (v18_def.trans (beq_iff_eq.mp hbr20))
    sym_close (hk _ _ _ (iptr := 0#64) (tg0 := 0#64) (tg1 := 0#64) (tg2 := 0#64) (tg3 := 0#64) (hx := 0#64)
      (IV := []) (G0 := []) (G1 := []) (G2 := []) (G3 := []))
    all_goals first
      | exact ⟨rfl, Or.inl ⟨rfl, Or.inl hz⟩⟩
      | exact .inl ⟨rfl, by assumption, by assumption⟩
  -- the last byte's top bit is set: `None`
  · have hm : b3.msb = true := by rw [← slt_sign_byte, v10_def]; exact hbr21
    sym_close (hk _ _ _ (iptr := 0#64) (tg0 := 0#64) (tg1 := 0#64) (tg2 := 0#64) (tg3 := 0#64) (hx := 0#64)
      (IV := []) (G0 := []) (G1 := []) (G2 := []) (G3 := []))
    all_goals first
      | exact ⟨rfl, Or.inl ⟨rfl, Or.inr hm⟩⟩
      | exact .inl ⟨rfl, by assumption, by assumption⟩
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
  all_goals sym_close (hk _ _ _ (iptr := post118_20) (tg0 := post118_21) (tg1 := post118_22)
    (tg2 := post118_23) (tg3 := post118_24) (hx := post118_25) (IV := post118_26) (G0 := post118_27)
    (G1 := post118_28) (G2 := post118_29) (G3 := post118_30))
  all_goals first
    | (refine .inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_⟩ <;> assumption)
    | (refine ⟨rfl, Or.inr ⟨hnz, hm, post118_0, post118_1, post118_2, post118_3, post118_4,
        post118_5, post118_6, post118_7, post118_8, post118_9, post118_10, post118_11, post118_12,
        post118_18, post118_19, by rw [hf]; rfl, ?_⟩⟩
       first
        | exact fun _ => rfl
        | exact fun h => by rw [hf] at h; exact absurd h (by decide))

/-- `spend_validating_key_from_bytes_init_spec` with the output's length (inside `SvkPost`) stated
    where the executor reads post regions. -/
theorem spend_validating_key_from_bytes_init_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 w0 w1 w2 w3 w4 w5 w6 w7 w8 : Word) (O : List Word)
    (hOl : O.length = 17)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    {c : Word → Option Instr} (hcc : s.code = c)
    (halloc : SqAlloc G n P c) (hrealloc_g : SqReallocG G n P c) (halloci : SqAllocInv G n P c)
    (hrealloc : SqRealloc G n P c)
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
    (hcodeO : CodeAt F_78032b38.base F_78032b38.prog s)
    (hcodeN : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeFI : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMs : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeD : CodeAt F_78032560.base F_78032560.prog s) (hcodeG : CodeAt F_78032614.base F_78032614.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x960 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (ha2 : s.getReg .x12 = 32#64)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 17)
    (hbelow0 : a0.toNat + 8 * 17 ≤ 0x78040620) (hbelow1 : a1.toNat + 8 * 4 ≤ 0x78040620)
    -- `FP_TABLES`, uninitialised (`Once` state byte 0 at 0x780488f0, padding zero)
    (hT0 : Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] s)
    (hd0 : Disjoint (sp - 0x960#64) 300 a0 13) (hd_a1 : Disjoint (sp - 0x960#64) 300 a1 4)
    (hd_tb : Disjoint (sp - 0x960#64) 300 0x780488a8#64 10)
    (he_a1 : Disjoint a0 17 a1 4) (he_tb : Disjoint a0 17 0x780488a8#64 10)
    (hk : ∀ (t : MachineState) (tag : Word) (Lo : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x960#64, 300), (a0, 17), (0x780488a8#64, 10),
        (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Lo.length = 16 → SvkPost b0 b1 b2 b3 tag Lo → Region a0 (tag :: Lo) t →
      ∀ (iptr tg0 tg1 tg2 tg3 hx : Word) (IV G0 G1 G2 G3 : List Word),
      ((tag = 0#64 ∧ Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] t ∧
          Run.HeapAt L t) ∨
        (Region 0x780488a8#64 [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64, hx, 2#64] t ∧
          Region iptr IV t ∧ Region tg0 G0 t ∧ Region tg1 G1 t ∧ Region tg2 G2 t ∧ Region tg3 G3 t ∧
          IV.length = 138 ∧ G0.length = 1024 ∧ G1.length = 1024 ∧ G2.length = 1024 ∧ G3.length = 516 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 ∧ RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 ∧ RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 ∧
          0x78048980 ≤ iptr.toNat ∧ iptr.toNat + 1104 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg0.toNat ∧ tg0.toNat + 0x2000 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg1.toNat ∧ tg1.toNat + 0x2000 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg2.toNat ∧ tg2.toNat + 0x2000 ≤ 0x1c00000000 ∧
          0x78048980 ≤ tg3.toNat ∧ tg3.toNat + 0x1020 ≤ 0x1c00000000 ∧
          Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L) t)) →
      SafeN G n P t) :
    SafeN G n P s :=
  spend_validating_key_from_bytes_init_spec s ra sp a0 a1 b0 b1 b2 b3 w0 w1 w2 w3 w4 w5 w6 w7 w8 O hOl hpb hpaf hpp hprz hhandle_rv hunwrap_opt hcc halloc hrealloc_g halloci hrealloc hpc hcode hcodeCmp hcodeU hcodeF hcodeMC hcodeM hcodeP hcodeC hcodeL hcodeB hcodeA hcodeR hcodeT hcodeO hcodeN hcodeFI hcodeSh hcodeMs hcodeD hcodeG hcw hro hheap hra hra1 hsp hstk ha0 ha1 ha2 hB hok_a1 hO hok0 hbelow0 hbelow1 hT0 hd0 hd_a1 hd_tb he_a1 he_tb
    (fun t tag Lo h1 h2 h3 h4 hp hR => hk t tag Lo h1 h2 h3 h4 hp.1 hp hR)

end Cases.Zip2005
