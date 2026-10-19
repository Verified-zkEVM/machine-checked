import Cases.Zip2005.Witness.OptWrap
import Cases.Zip2005.Witness.NextU64
import Cases.Zip2005.Witness.NextU32
import Cases.Zip2005.Witness.NextArrBytes32
import Cases.Zip2005.Witness.BoolReader
import Cases.Zip2005.Witness.InvalidLength
import Cases.Zip2005.Runtime.Memcpy_d0s0_1010
import Cases.Zip2005.Witness.WitnessTail
import Cases.Zip2005.Witness.WitnessModel
import Cases.Zip2005.Witness.WitnessMidCells_NN
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Zip2005Witness`'s visitor from `value` on (`0x78018a6c`)

The second part of the visitor (cut at `0x78018a6c`, after `sk` and the eight `Bytes32`, which
are in the frame and in callee-saved registers by then): `value`, `merkle_position`,
`auth_path`, `qk`, `sigma_qsk` and `negate` through the sequence access at `sp + 0x88`
(`[de, 6]`), then the tail (`Cases.Zip2005.witness_tail_spec`). This case: `qk` None, `sigma_qsk` None. The stream is at `qb + 1` over the
aligned words `W`; whatever the tag of `sk`, every later field sits at the same residue mod 8.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option machineChecked.sym.foldBytes true in
theorem witness_mid_NN_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word)
    (vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra : Word)
    (Fr1 Fr2 O W : List Word) (hF1l : Fr1.length = 17) (hF2l : Fr2.length = 302)
    (hOl : O.length = 174) (hWl : W.length = 138)
    (hpc : s.pc = 0x78018a6c#64) (hcode : CodeAt F_7801823c.base F_7801823c.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcode64 : CodeAt F_78019cb8.base F_78019cb8.prog s)
    (hcode32 : CodeAt F_78019bf0.base F_78019bf0.prog s)
    (hcodeNA : CodeAt F_780197cc.base F_780197cc.prog s)
    (hcodeV : CodeAt F_78016938.base F_78016938.prog s)
    (hcodeE : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeNO : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeB : CodeAt F_78019dd8.base F_78019dd8.prog s)
    (hcodeIL : CodeAt F_78019f50.base F_78019f50.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1120 sp)
    (hs0 : s.getReg .x8 = out) (hs5 : s.getReg .x21 = sp + 0x9c4#64)
    (hr9 : s.getReg .x9 = r9) (hr18 : s.getReg .x18 = r18) (hr19 : s.getReg .x19 = r19) (hr20 : s.getReg .x20 = r20)
    (hr22 : s.getReg .x22 = r22) (hr23 : s.getReg .x23 = r23) (hr24 : s.getReg .x24 = r24) (hr25 : s.getReg .x25 = r25)
    (hr26 : s.getReg .x26 = r26) (hr27 : s.getReg .x27 = r27)
    (hF1 : Region sp Fr1 s) (hA : Region (sp + 0x88#64) [de, c] s) (hF2 : Region (sp + 0x98#64) Fr2 s)
    (hS : Region (sp + 0xa08#64) [vs11, vs10, vs9, vs8, vs7, vs6, vs5, vs4, vs3, vs2, vs1, vs0, vra] s)
    (hokF : RegionOk Ro.layout.textLo Ro.layout.textHi sp 334) (hc : c = 6#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 174)
    (hD : Region de [qb + 1#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region qb W s) (hq : 0x1c00000000 ≤ qb.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi qb 138)
    (hdO : Disjoint (sp - 0x1120#64) 882 out 174) (hdD : Disjoint (sp - 0x1120#64) 882 de 2)
    (heD : Disjoint out 174 de 2) (hOlo : out.toNat + 1392 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000) (hFlo : sp.toNat + 2672 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r' → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hqk : (optTag5 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!]).toNat < 1) (hsg : (optTag6 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!]).toNat < 1)
    (hkOk : ∀ (t : MachineState) (V : List Word), t.pc = vra &&& ~~~1#64 →
      t.code = s.code → t.getReg .x1 = vra → t.getReg .x2 = sp + 0xa70#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 →
      t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = vs6 → t.getReg .x23 = vs7 →
      t.getReg .x24 = vs8 → t.getReg .x25 = vs9 → t.getReg .x26 = vs10 → t.getReg .x27 = vs11 →
      Unchanged [(sp - 0x1120#64, 548), (sp, 334), (out, 174), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out V t → V.length = 174 → V = midW (Fr1 ++ [de, c] ++ Fr2) r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V →
      midOkCond W l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkErr : ∀ (t : MachineState) (V : List Word), t.pc = vra &&& ~~~1#64 →
      t.code = s.code → t.getReg .x1 = vra → t.getReg .x2 = sp + 0xa70#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 →
      t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = vs6 → t.getReg .x23 = vs7 →
      t.getReg .x24 = vs8 → t.getReg .x25 = vs9 → t.getReg .x26 = vs10 → t.getReg .x27 = vs11 →
      Unchanged [(sp - 0x1120#64, 548), (sp, 334), (out, 174), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out V t → V.length = 174 → extractByte V[173]! 7 = 2#8 → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1120#64) 548 := hstk.frame 548 (by decide)
  have hu := Unchanged.refl [(sp - 0x1120#64, 548), (sp, 334), (out, 174), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  have hokOr : RegionOk Ro.layout.roBase Ro.layout.textHi out 174 :=
    ⟨hokO.aligned, hokO.inMem, Or.inl (by simp only [Ro.layout_roBase]; omega)⟩
  have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi sp 17 := hokF.sub' 0 17 (by decide) (by simp)
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x88#64) 2 := hokF.sub' 17 2 (by decide) rfl
  have hokF2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x98#64) 302 := hokF.sub' 19 302 (by decide) rfl
  have hokSv : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa08#64) 13 := hokF.sub' 321 13 (by decide) rfl
  have halloc0 := fun u sp' L' h1 h2 h3 => halloc u sp' 0x78018130#64 L' h1 h2 h3 (by decide)
  have halloc1 := fun u sp' L' h1 h2 h3 => halloc u sp' 0x78019e80#64 L' h1 h2 h3 (by decide)
  have halloc2 := fun u sp' L' h1 h2 h3 => halloc u sp' 0x78019fbc#64 L' h1 h2 h3 (by decide)
  subst hc
  rw [MachineChecked.RiscV.Sym.List.eq_map_range Fr1 hF1l] at hF1
  rw [MachineChecked.RiscV.Sym.List.eq_map_range Fr2 hF2l] at hF2
  rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [MachineChecked.RiscV.Sym.List.eq_map_range W hWl] at hW
  sym_exec [next_u64_ok_spec, next_u64_err_spec, next_u32_ok_spec, next_u32_err_spec,
    next_arr_bytes32_ok_spec, next_arr_bytes32_err_spec,
    nopt5_none_spec, nopt5_errnone_spec, nopt6_none_spec, nopt6_errnone_spec,
    bool_reader_ok_spec, bool_reader_eof_spec, bool_reader_badbyte_spec, invalid_length_spec,
    memcpy_d0s0_1010_spec, witness_tail_spec, hhandle, halloc0, halloc1, halloc2, hio] 3000
  all_goals first
    | (sym_close hkErr
       all_goals (try simp only [List.length_cons, List.length_nil])
       all_goals (simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
                  sym_unfold
                  simp (disch := decide) only [byte_simp]
                  try decide)
       done)
    | (sym_close hkOk
       · simp only [List.length_cons, List.length_nil]
       · set FrL : List Word := [Fr1[0]!, Fr1[1]!, 0#64, v100, v68, v37, r27, v17, Fr1[8]!, Fr1[9]!, Fr1[10]!, Fr1[11]!, Fr1[12]!, Fr1[13]!, Fr1[14]!, Fr1[15]!, Fr1[16]!, de, 6#64 - 1#64 - 1#64 - 1#64 - 1#64 - 1#64, Fr2[0]!, Fr2[1]!, Fr2[2]!, Fr2[3]!, Fr2[4]!, Fr2[5]!, Fr2[6]!, Fr2[7]!, Fr2[8]!, Fr2[9]!, Fr2[10]!, Fr2[11]!, Fr2[12]!, Fr2[13]!, Fr2[14]!, Fr2[15]!, Fr2[16]!, Fr2[17]!, Fr2[18]!, Fr2[19]!, Fr2[20]!, Fr2[21]!, Fr2[22]!, Fr2[23]!, Fr2[24]!, Fr2[25]!, Fr2[26]!, Fr2[27]!, Fr2[28]!, Fr2[29]!, Fr2[30]!, Fr2[31]!, Fr2[32]!, Fr2[33]!, Fr2[34]!, Fr2[35]!, Fr2[36]!, v102, v103, v118, post90_0[3]!, post90_0[4]!, acc46_0[5]!, acc46_0[6]!, acc46_0[7]!, acc46_0[8]!, acc46_0[9]!, acc46_0[10]!, acc46_0[11]!, acc46_0[12]!, acc46_0[13]!, acc46_0[14]!, acc46_0[15]!, acc46_0[16]!, acc46_0[17]!, acc46_0[18]!, acc46_0[19]!, acc46_0[20]!, acc46_0[21]!, acc46_0[22]!, acc46_0[23]!, acc46_0[24]!, acc46_0[25]!, acc46_0[26]!, acc46_0[27]!, acc46_0[28]!, acc46_0[29]!, acc46_0[30]!, acc46_0[31]!, acc46_0[32]!, acc46_0[33]!, acc46_0[34]!, acc46_0[35]!, acc46_0[36]!, acc46_0[37]!, acc46_0[38]!, acc46_0[39]!, acc46_0[40]!, acc46_0[41]!, acc46_0[42]!, acc46_0[43]!, acc46_0[44]!, acc46_0[45]!, acc46_0[46]!, acc46_0[47]!, acc46_0[48]!, acc46_0[49]!, acc46_0[50]!, acc46_0[51]!, acc46_0[52]!, acc46_0[53]!, acc46_0[54]!, acc46_0[55]!, acc46_0[56]!, acc46_0[57]!, acc46_0[58]!, acc46_0[59]!, acc46_0[60]!, acc46_0[61]!, acc46_0[62]!, acc46_0[63]!, acc46_0[64]!, acc46_0[65]!, acc46_0[66]!, acc46_0[67]!, acc46_0[68]!, acc46_0[69]!, acc46_0[70]!, acc46_0[71]!, acc46_0[72]!, acc46_0[73]!, acc46_0[74]!, acc46_0[75]!, acc46_0[76]!, acc46_0[77]!, acc46_0[78]!, acc46_0[79]!, acc46_0[80]!, acc46_0[81]!, acc46_0[82]!, acc46_0[83]!, acc46_0[84]!, acc46_0[85]!, acc46_0[86]!, acc46_0[87]!, acc46_0[88]!, acc46_0[89]!, acc46_0[90]!, acc46_0[91]!, acc46_0[92]!, acc46_0[93]!, acc46_0[94]!, acc46_0[95]!, acc46_0[96]!, acc46_0[97]!, acc46_0[98]!, acc46_0[99]!, acc46_0[100]!, acc46_0[101]!, acc46_0[102]!, acc46_0[103]!, acc46_0[104]!, acc46_0[105]!, acc46_0[106]!, acc46_0[107]!, acc46_0[108]!, acc46_0[109]!, acc46_0[110]!, acc46_0[111]!, acc46_0[112]!, acc46_0[113]!, acc46_0[114]!, acc46_0[115]!, acc46_0[116]!, acc46_0[117]!, acc46_0[118]!, acc46_0[119]!, acc46_0[120]!, acc46_0[121]!, acc46_0[122]!, acc46_0[123]!, acc46_0[124]!, acc46_0[125]!, acc46_0[126]!, acc54_0[0]!, acc54_0[1]!, acc54_0[2]!, acc54_0[3]!, acc54_0[4]!, acc54_0[5]!, acc54_0[6]!, acc54_0[7]!, acc54_0[8]!, acc54_0[9]!, acc54_0[10]!, acc54_0[11]!, acc54_0[12]!, acc54_0[13]!, acc54_0[14]!, acc54_0[15]!, acc54_0[16]!, acc54_0[17]!, acc54_0[18]!, acc54_0[19]!, acc54_0[20]!, acc54_0[21]!, acc54_0[22]!, acc54_0[23]!, acc54_0[24]!, acc54_0[25]!, acc54_0[26]!, acc54_0[27]!, acc54_0[28]!, acc54_0[29]!, acc54_0[30]!, acc54_0[31]!, acc54_0[32]!, acc54_0[33]!, acc54_0[34]!, acc54_0[35]!, acc54_0[36]!, acc54_0[37]!, acc54_0[38]!, acc54_0[39]!, acc54_0[40]!, acc54_0[41]!, acc54_0[42]!, acc54_0[43]!, acc54_0[44]!, acc54_0[45]!, acc54_0[46]!, acc54_0[47]!, acc54_0[48]!, acc54_0[49]!, acc54_0[50]!, acc54_0[51]!, acc54_0[52]!, acc54_0[53]!, acc54_0[54]!, acc54_0[55]!, acc54_0[56]!, acc54_0[57]!, acc54_0[58]!, acc54_0[59]!, acc54_0[60]!, acc54_0[61]!, acc54_0[62]!, acc54_0[63]!, acc54_0[64]!, acc54_0[65]!, acc54_0[66]!, acc54_0[67]!, acc54_0[68]!, acc54_0[69]!, acc54_0[70]!, acc54_0[71]!, acc54_0[72]!, acc54_0[73]!, acc54_0[74]!, acc54_0[75]!, acc54_0[76]!, acc54_0[77]!, acc54_0[78]!, acc54_0[79]!, acc54_0[80]!, acc54_0[81]!, acc54_0[82]!, acc54_0[83]!, acc54_0[84]!, acc54_0[85]!, acc54_0[86]!, acc54_0[87]!, acc54_0[88]!, acc54_0[89]!, acc54_0[90]!, acc54_0[91]!, acc54_0[92]!, acc54_0[93]!, acc54_0[94]!, acc54_0[95]!, acc54_0[96]!, acc54_0[97]!, acc54_0[98]!, acc54_0[99]!, acc54_0[100]!, acc54_0[101]!, acc54_0[102]!, acc54_0[103]!, acc54_0[104]!, acc54_0[105]!, acc54_0[106]!, acc54_0[107]!, acc54_0[108]!, acc54_0[109]!, acc54_0[110]!, acc54_0[111]!, acc54_0[112]!, acc54_0[113]!, acc54_0[114]!, acc54_0[115]!, acc54_0[116]!, acc54_0[117]!, acc54_0[118]!, acc54_0[119]!, acc54_0[120]!, acc54_0[121]!, acc54_0[122]!, acc54_0[123]!, acc54_0[124]!, acc54_0[125]!, acc54_0[126]!, acc27_0[127]!, acc27_0[128]!, v40, v74, v70, v71, v85, replaceByte (replaceByte [v102, v103][0]! 1 (boolByte [W[129]!])) 0 0#8, [v102, v103][1]!, v108, v109] with hFL
         have hF2 : FrL[2]! = 0#64 := by rw [hFL]; rfl
         have hF3 : FrL[3]! = v100 := by rw [hFL]; rfl
         have hF4 : FrL[4]! = v68 := by rw [hFL]; rfl
         have hF5 : FrL[5]! = v37 := by rw [hFL]; rfl
         have hF6 : FrL[6]! = r27 := by rw [hFL]; rfl
         have hF7 : FrL[7]! = v17 := by rw [hFL]; rfl
         have hF8 : FrL[8]! = Fr1[8]! := by rw [hFL]; rfl
         have hF9 : FrL[9]! = Fr1[9]! := by rw [hFL]; rfl
         have hF10 : FrL[10]! = Fr1[10]! := by rw [hFL]; rfl
         have hF11 : FrL[11]! = Fr1[11]! := by rw [hFL]; rfl
         have hF12 : FrL[12]! = Fr1[12]! := by rw [hFL]; rfl
         have hF13 : FrL[13]! = Fr1[13]! := by rw [hFL]; rfl
         have hF14 : FrL[14]! = Fr1[14]! := by rw [hFL]; rfl
         have hF15 : FrL[15]! = Fr1[15]! := by rw [hFL]; rfl
         have hF16 : FrL[16]! = Fr1[16]! := by rw [hFL]; rfl
         have hF20 : FrL[20]! = Fr2[1]! := by rw [hFL]; rfl
         have hF21 : FrL[21]! = Fr2[2]! := by rw [hFL]; rfl
         have hF22 : FrL[22]! = Fr2[3]! := by rw [hFL]; rfl
         have hF23 : FrL[23]! = Fr2[4]! := by rw [hFL]; rfl
         have hF24 : FrL[24]! = Fr2[5]! := by rw [hFL]; rfl
         have hF25 : FrL[25]! = Fr2[6]! := by rw [hFL]; rfl
         have hF26 : FrL[26]! = Fr2[7]! := by rw [hFL]; rfl
         have hF27 : FrL[27]! = Fr2[8]! := by rw [hFL]; rfl
         have hF28 : FrL[28]! = Fr2[9]! := by rw [hFL]; rfl
         have hF29 : FrL[29]! = Fr2[10]! := by rw [hFL]; rfl
         have hF30 : FrL[30]! = Fr2[11]! := by rw [hFL]; rfl
         have hF31 : FrL[31]! = Fr2[12]! := by rw [hFL]; rfl
         have hF32 : FrL[32]! = Fr2[13]! := by rw [hFL]; rfl
         have hF33 : FrL[33]! = Fr2[14]! := by rw [hFL]; rfl
         have hF34 : FrL[34]! = Fr2[15]! := by rw [hFL]; rfl
         have hF35 : FrL[35]! = Fr2[16]! := by rw [hFL]; rfl
         have hF36 : FrL[36]! = Fr2[17]! := by rw [hFL]; rfl
         have hF37 : FrL[37]! = Fr2[18]! := by rw [hFL]; rfl
         have hF38 : FrL[38]! = Fr2[19]! := by rw [hFL]; rfl
         have hF39 : FrL[39]! = Fr2[20]! := by rw [hFL]; rfl
         have hF40 : FrL[40]! = Fr2[21]! := by rw [hFL]; rfl
         have hF41 : FrL[41]! = Fr2[22]! := by rw [hFL]; rfl
         have hF42 : FrL[42]! = Fr2[23]! := by rw [hFL]; rfl
         have hF43 : FrL[43]! = Fr2[24]! := by rw [hFL]; rfl
         have hF44 : FrL[44]! = Fr2[25]! := by rw [hFL]; rfl
         have hF45 : FrL[45]! = Fr2[26]! := by rw [hFL]; rfl
         have hF46 : FrL[46]! = Fr2[27]! := by rw [hFL]; rfl
         have hF47 : FrL[47]! = Fr2[28]! := by rw [hFL]; rfl
         have hF48 : FrL[48]! = Fr2[29]! := by rw [hFL]; rfl
         have hF49 : FrL[49]! = Fr2[30]! := by rw [hFL]; rfl
         have hF50 : FrL[50]! = Fr2[31]! := by rw [hFL]; rfl
         have hF51 : FrL[51]! = Fr2[32]! := by rw [hFL]; rfl
         have hF52 : FrL[52]! = Fr2[33]! := by rw [hFL]; rfl
         have hF53 : FrL[53]! = Fr2[34]! := by rw [hFL]; rfl
         have hF54 : FrL[54]! = Fr2[35]! := by rw [hFL]; rfl
         have hF55 : FrL[55]! = Fr2[36]! := by rw [hFL]; rfl
         have hF56 : FrL[56]! = v102 := by rw [hFL]; rfl
         have hF57 : FrL[57]! = v103 := by rw [hFL]; rfl
         have hF58 : FrL[58]! = v118 := by rw [hFL]; rfl
         have hF183 : FrL[183]! = acc54_0[0]! := by rw [hFL]; rfl
         have hF184 : FrL[184]! = acc54_0[1]! := by rw [hFL]; rfl
         have hF185 : FrL[185]! = acc54_0[2]! := by rw [hFL]; rfl
         have hF186 : FrL[186]! = acc54_0[3]! := by rw [hFL]; rfl
         have hF187 : FrL[187]! = acc54_0[4]! := by rw [hFL]; rfl
         have hF188 : FrL[188]! = acc54_0[5]! := by rw [hFL]; rfl
         have hF189 : FrL[189]! = acc54_0[6]! := by rw [hFL]; rfl
         have hF190 : FrL[190]! = acc54_0[7]! := by rw [hFL]; rfl
         have hF191 : FrL[191]! = acc54_0[8]! := by rw [hFL]; rfl
         have hF192 : FrL[192]! = acc54_0[9]! := by rw [hFL]; rfl
         have hF193 : FrL[193]! = acc54_0[10]! := by rw [hFL]; rfl
         have hF194 : FrL[194]! = acc54_0[11]! := by rw [hFL]; rfl
         have hF195 : FrL[195]! = acc54_0[12]! := by rw [hFL]; rfl
         have hF196 : FrL[196]! = acc54_0[13]! := by rw [hFL]; rfl
         have hF197 : FrL[197]! = acc54_0[14]! := by rw [hFL]; rfl
         have hF198 : FrL[198]! = acc54_0[15]! := by rw [hFL]; rfl
         have hF199 : FrL[199]! = acc54_0[16]! := by rw [hFL]; rfl
         have hF200 : FrL[200]! = acc54_0[17]! := by rw [hFL]; rfl
         have hF201 : FrL[201]! = acc54_0[18]! := by rw [hFL]; rfl
         have hF202 : FrL[202]! = acc54_0[19]! := by rw [hFL]; rfl
         have hF203 : FrL[203]! = acc54_0[20]! := by rw [hFL]; rfl
         have hF204 : FrL[204]! = acc54_0[21]! := by rw [hFL]; rfl
         have hF205 : FrL[205]! = acc54_0[22]! := by rw [hFL]; rfl
         have hF206 : FrL[206]! = acc54_0[23]! := by rw [hFL]; rfl
         have hF207 : FrL[207]! = acc54_0[24]! := by rw [hFL]; rfl
         have hF208 : FrL[208]! = acc54_0[25]! := by rw [hFL]; rfl
         have hF209 : FrL[209]! = acc54_0[26]! := by rw [hFL]; rfl
         have hF210 : FrL[210]! = acc54_0[27]! := by rw [hFL]; rfl
         have hF211 : FrL[211]! = acc54_0[28]! := by rw [hFL]; rfl
         have hF212 : FrL[212]! = acc54_0[29]! := by rw [hFL]; rfl
         have hF213 : FrL[213]! = acc54_0[30]! := by rw [hFL]; rfl
         have hF214 : FrL[214]! = acc54_0[31]! := by rw [hFL]; rfl
         have hF215 : FrL[215]! = acc54_0[32]! := by rw [hFL]; rfl
         have hF216 : FrL[216]! = acc54_0[33]! := by rw [hFL]; rfl
         have hF217 : FrL[217]! = acc54_0[34]! := by rw [hFL]; rfl
         have hF218 : FrL[218]! = acc54_0[35]! := by rw [hFL]; rfl
         have hF219 : FrL[219]! = acc54_0[36]! := by rw [hFL]; rfl
         have hF220 : FrL[220]! = acc54_0[37]! := by rw [hFL]; rfl
         have hF221 : FrL[221]! = acc54_0[38]! := by rw [hFL]; rfl
         have hF222 : FrL[222]! = acc54_0[39]! := by rw [hFL]; rfl
         have hF223 : FrL[223]! = acc54_0[40]! := by rw [hFL]; rfl
         have hF224 : FrL[224]! = acc54_0[41]! := by rw [hFL]; rfl
         have hF225 : FrL[225]! = acc54_0[42]! := by rw [hFL]; rfl
         have hF226 : FrL[226]! = acc54_0[43]! := by rw [hFL]; rfl
         have hF227 : FrL[227]! = acc54_0[44]! := by rw [hFL]; rfl
         have hF228 : FrL[228]! = acc54_0[45]! := by rw [hFL]; rfl
         have hF229 : FrL[229]! = acc54_0[46]! := by rw [hFL]; rfl
         have hF230 : FrL[230]! = acc54_0[47]! := by rw [hFL]; rfl
         have hF231 : FrL[231]! = acc54_0[48]! := by rw [hFL]; rfl
         have hF232 : FrL[232]! = acc54_0[49]! := by rw [hFL]; rfl
         have hF233 : FrL[233]! = acc54_0[50]! := by rw [hFL]; rfl
         have hF234 : FrL[234]! = acc54_0[51]! := by rw [hFL]; rfl
         have hF235 : FrL[235]! = acc54_0[52]! := by rw [hFL]; rfl
         have hF236 : FrL[236]! = acc54_0[53]! := by rw [hFL]; rfl
         have hF237 : FrL[237]! = acc54_0[54]! := by rw [hFL]; rfl
         have hF238 : FrL[238]! = acc54_0[55]! := by rw [hFL]; rfl
         have hF239 : FrL[239]! = acc54_0[56]! := by rw [hFL]; rfl
         have hF240 : FrL[240]! = acc54_0[57]! := by rw [hFL]; rfl
         have hF241 : FrL[241]! = acc54_0[58]! := by rw [hFL]; rfl
         have hF242 : FrL[242]! = acc54_0[59]! := by rw [hFL]; rfl
         have hF243 : FrL[243]! = acc54_0[60]! := by rw [hFL]; rfl
         have hF244 : FrL[244]! = acc54_0[61]! := by rw [hFL]; rfl
         have hF245 : FrL[245]! = acc54_0[62]! := by rw [hFL]; rfl
         have hF246 : FrL[246]! = acc54_0[63]! := by rw [hFL]; rfl
         have hF247 : FrL[247]! = acc54_0[64]! := by rw [hFL]; rfl
         have hF248 : FrL[248]! = acc54_0[65]! := by rw [hFL]; rfl
         have hF249 : FrL[249]! = acc54_0[66]! := by rw [hFL]; rfl
         have hF250 : FrL[250]! = acc54_0[67]! := by rw [hFL]; rfl
         have hF251 : FrL[251]! = acc54_0[68]! := by rw [hFL]; rfl
         have hF252 : FrL[252]! = acc54_0[69]! := by rw [hFL]; rfl
         have hF253 : FrL[253]! = acc54_0[70]! := by rw [hFL]; rfl
         have hF254 : FrL[254]! = acc54_0[71]! := by rw [hFL]; rfl
         have hF255 : FrL[255]! = acc54_0[72]! := by rw [hFL]; rfl
         have hF256 : FrL[256]! = acc54_0[73]! := by rw [hFL]; rfl
         have hF257 : FrL[257]! = acc54_0[74]! := by rw [hFL]; rfl
         have hF258 : FrL[258]! = acc54_0[75]! := by rw [hFL]; rfl
         have hF259 : FrL[259]! = acc54_0[76]! := by rw [hFL]; rfl
         have hF260 : FrL[260]! = acc54_0[77]! := by rw [hFL]; rfl
         have hF261 : FrL[261]! = acc54_0[78]! := by rw [hFL]; rfl
         have hF262 : FrL[262]! = acc54_0[79]! := by rw [hFL]; rfl
         have hF263 : FrL[263]! = acc54_0[80]! := by rw [hFL]; rfl
         have hF264 : FrL[264]! = acc54_0[81]! := by rw [hFL]; rfl
         have hF265 : FrL[265]! = acc54_0[82]! := by rw [hFL]; rfl
         have hF266 : FrL[266]! = acc54_0[83]! := by rw [hFL]; rfl
         have hF267 : FrL[267]! = acc54_0[84]! := by rw [hFL]; rfl
         have hF268 : FrL[268]! = acc54_0[85]! := by rw [hFL]; rfl
         have hF269 : FrL[269]! = acc54_0[86]! := by rw [hFL]; rfl
         have hF270 : FrL[270]! = acc54_0[87]! := by rw [hFL]; rfl
         have hF271 : FrL[271]! = acc54_0[88]! := by rw [hFL]; rfl
         have hF272 : FrL[272]! = acc54_0[89]! := by rw [hFL]; rfl
         have hF273 : FrL[273]! = acc54_0[90]! := by rw [hFL]; rfl
         have hF274 : FrL[274]! = acc54_0[91]! := by rw [hFL]; rfl
         have hF275 : FrL[275]! = acc54_0[92]! := by rw [hFL]; rfl
         have hF276 : FrL[276]! = acc54_0[93]! := by rw [hFL]; rfl
         have hF277 : FrL[277]! = acc54_0[94]! := by rw [hFL]; rfl
         have hF278 : FrL[278]! = acc54_0[95]! := by rw [hFL]; rfl
         have hF279 : FrL[279]! = acc54_0[96]! := by rw [hFL]; rfl
         have hF280 : FrL[280]! = acc54_0[97]! := by rw [hFL]; rfl
         have hF281 : FrL[281]! = acc54_0[98]! := by rw [hFL]; rfl
         have hF282 : FrL[282]! = acc54_0[99]! := by rw [hFL]; rfl
         have hF283 : FrL[283]! = acc54_0[100]! := by rw [hFL]; rfl
         have hF284 : FrL[284]! = acc54_0[101]! := by rw [hFL]; rfl
         have hF285 : FrL[285]! = acc54_0[102]! := by rw [hFL]; rfl
         have hF286 : FrL[286]! = acc54_0[103]! := by rw [hFL]; rfl
         have hF287 : FrL[287]! = acc54_0[104]! := by rw [hFL]; rfl
         have hF288 : FrL[288]! = acc54_0[105]! := by rw [hFL]; rfl
         have hF289 : FrL[289]! = acc54_0[106]! := by rw [hFL]; rfl
         have hF290 : FrL[290]! = acc54_0[107]! := by rw [hFL]; rfl
         have hF291 : FrL[291]! = acc54_0[108]! := by rw [hFL]; rfl
         have hF292 : FrL[292]! = acc54_0[109]! := by rw [hFL]; rfl
         have hF293 : FrL[293]! = acc54_0[110]! := by rw [hFL]; rfl
         have hF294 : FrL[294]! = acc54_0[111]! := by rw [hFL]; rfl
         have hF295 : FrL[295]! = acc54_0[112]! := by rw [hFL]; rfl
         have hF296 : FrL[296]! = acc54_0[113]! := by rw [hFL]; rfl
         have hF297 : FrL[297]! = acc54_0[114]! := by rw [hFL]; rfl
         have hF298 : FrL[298]! = acc54_0[115]! := by rw [hFL]; rfl
         have hF299 : FrL[299]! = acc54_0[116]! := by rw [hFL]; rfl
         have hF300 : FrL[300]! = acc54_0[117]! := by rw [hFL]; rfl
         have hF301 : FrL[301]! = acc54_0[118]! := by rw [hFL]; rfl
         have hF302 : FrL[302]! = acc54_0[119]! := by rw [hFL]; rfl
         have hF303 : FrL[303]! = acc54_0[120]! := by rw [hFL]; rfl
         have hF304 : FrL[304]! = acc54_0[121]! := by rw [hFL]; rfl
         have hF305 : FrL[305]! = acc54_0[122]! := by rw [hFL]; rfl
         have hF306 : FrL[306]! = acc54_0[123]! := by rw [hFL]; rfl
         have hF307 : FrL[307]! = acc54_0[124]! := by rw [hFL]; rfl
         have hF308 : FrL[308]! = acc54_0[125]! := by rw [hFL]; rfl
         have hF309 : FrL[309]! = acc54_0[126]! := by rw [hFL]; rfl
         have hF312 : FrL[312]! = v40 := by rw [hFL]; rfl
         have hF313 : FrL[313]! = v74 := by rw [hFL]; rfl
         have hF314 : FrL[314]! = v70 := by rw [hFL]; rfl
         have hF315 : FrL[315]! = v71 := by rw [hFL]; rfl
         have hF316 : FrL[316]! = v85 := by rw [hFL]; rfl
         have hF317 : FrL[317]! = replaceByte (replaceByte [v102, v103][0]! 1 (boolByte [W[129]!])) 0 0#8 := by rw [hFL]; rfl
         have hF320 : FrL[320]! = v109 := by rw [hFL]; rfl
         have htq : extractByte W[129]! 5 = 0#8 := by
           have e : extractByte W[129]! 5 = optTag5 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!] := rfl
           rw [e]
           apply BitVec.eq_of_toNat_eq
           rw [BitVec.toNat_ofNat]
           omega
         have hts : extractByte W[129]! 6 = 0#8 := by
           have e : extractByte W[129]! 6 = optTag6 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!] := rfl
           rw [e]
           apply BitVec.eq_of_toNat_eq
           rw [BitVec.toNat_ofNat]
           omega
         rw [← acc128_0_def]
         apply List.ext_getElem (by simp)
         intro i h1 h2
         have hi : i < 174 := by simpa using h2
         interval_cases i
         · exact (wmNN_cell0 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 v31 v32 v34 v35 v36 v37 v39 v40 hF5 hF312 v6_def acc27_0_def v31_def v32_def v34_def v35_def v36_def v37_def v39_def v40_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell1 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 v37 acc46_0 acc54_0 hF5 hF183 v6_def acc27_0_def v37_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell2 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF183 hF184 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell3 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF184 hF185 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell4 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF185 hF186 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell5 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF186 hF187 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell6 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF187 hF188 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell7 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF188 hF189 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell8 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF189 hF190 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell9 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF190 hF191 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell10 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF191 hF192 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell11 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF192 hF193 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell12 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF193 hF194 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell13 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF194 hF195 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell14 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF195 hF196 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell15 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF196 hF197 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell16 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF197 hF198 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell17 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF198 hF199 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell18 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF199 hF200 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell19 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF200 hF201 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell20 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF201 hF202 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell21 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF202 hF203 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell22 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF203 hF204 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell23 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF204 hF205 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell24 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF205 hF206 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell25 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF206 hF207 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell26 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF207 hF208 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell27 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF208 hF209 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell28 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF209 hF210 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell29 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF210 hF211 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell30 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF211 hF212 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell31 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF212 hF213 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell32 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF213 hF214 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell33 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF214 hF215 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell34 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF215 hF216 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell35 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF216 hF217 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell36 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF217 hF218 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell37 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF218 hF219 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell38 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF219 hF220 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell39 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF220 hF221 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell40 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF221 hF222 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell41 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF222 hF223 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell42 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF223 hF224 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell43 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF224 hF225 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell44 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF225 hF226 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell45 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF226 hF227 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell46 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF227 hF228 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell47 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF228 hF229 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell48 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF229 hF230 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell49 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF230 hF231 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell50 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF231 hF232 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell51 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF232 hF233 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell52 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF233 hF234 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell53 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF234 hF235 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell54 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF235 hF236 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell55 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF236 hF237 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell56 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF237 hF238 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell57 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF238 hF239 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell58 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF239 hF240 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell59 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF240 hF241 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell60 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF241 hF242 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell61 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF242 hF243 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell62 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF243 hF244 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell63 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF244 hF245 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell64 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF245 hF246 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell65 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF246 hF247 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell66 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF247 hF248 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell67 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF248 hF249 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell68 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF249 hF250 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell69 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF250 hF251 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell70 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF251 hF252 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell71 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF252 hF253 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell72 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF253 hF254 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell73 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF254 hF255 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell74 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF255 hF256 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell75 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF256 hF257 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell76 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF257 hF258 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell77 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF258 hF259 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell78 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF259 hF260 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell79 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF260 hF261 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell80 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF261 hF262 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell81 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF262 hF263 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell82 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF263 hF264 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell83 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF264 hF265 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell84 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF265 hF266 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell85 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF266 hF267 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell86 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF267 hF268 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell87 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF268 hF269 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell88 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF269 hF270 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell89 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF270 hF271 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell90 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF271 hF272 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell91 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF272 hF273 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell92 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF273 hF274 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell93 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF274 hF275 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell94 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF275 hF276 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell95 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF276 hF277 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell96 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF277 hF278 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell97 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF278 hF279 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell98 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF279 hF280 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell99 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF280 hF281 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell100 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF281 hF282 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell101 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF282 hF283 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell102 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF283 hF284 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell103 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF284 hF285 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell104 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF285 hF286 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell105 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF286 hF287 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell106 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF287 hF288 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell107 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF288 hF289 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell108 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF289 hF290 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell109 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF290 hF291 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell110 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF291 hF292 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell111 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF292 hF293 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell112 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF293 hF294 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell113 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF294 hF295 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell114 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF295 hF296 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell115 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF296 hF297 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell116 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF297 hF298 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell117 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF298 hF299 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell118 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF299 hF300 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell119 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF300 hF301 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell120 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF301 hF302 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell121 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF302 hF303 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell122 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF303 hF304 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell123 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF304 hF305 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell124 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF305 hF306 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell125 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF306 hF307 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell126 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF307 hF308 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell127 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 acc27_0 acc46_0 acc54_0 hF308 hF309 v6_def acc27_0_def acc46_0_def acc54_0_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell128 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF27 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell129 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF24 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell130 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF24 hF25 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell131 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF25 hF26 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell132 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF31 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell133 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF28 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell134 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF28 hF29 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell135 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF29 hF30 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell136 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF14 hF35 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell137 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF14 hF32 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell138 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF32 hF33 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell139 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF33 hF34 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell140 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF15 hF39 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell141 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF15 hF16 hF36 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell142 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF36 hF37 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell143 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF37 hF38 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell144 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF12 hF43 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell145 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF12 hF13 hF40 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell146 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF40 hF41 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell147 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF41 hF42 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell148 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF6 hF44 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell149 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF6 hF11 hF45 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell150 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF45 hF46 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell151 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF46 hF47 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell152 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF10 hF48 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell153 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF9 hF10 hF49 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell154 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF49 hF50 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell155 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF50 hF51 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell156 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF8 hF52 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell157 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF8 hF53 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell158 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF53 hF54 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell159 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF54 hF55 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell160 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell161 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 v17 hF1l hF7 hF23 v6_def v17_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell162 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF23 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell163 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF20 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell164 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 v6 hF1l hF20 hF21 v6_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell165 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post59_0 v6 v62 v63 v65 v66 v67 v73 v74 hF1l htq hF21 hF22 hF313 v6_def v62_def v63_def v65_def v66_def v67_def v73_def v74_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell166 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post59_0 v6 v62 v63 v65 v66 v67 v68 v73 v74 htq hF4 hF313 v6_def v62_def v63_def v65_def v66_def v67_def v68_def v73_def v74_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell167 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post59_0 v6 v68 v70 htq hF4 hF314 v6_def v68_def v70_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell168 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post59_0 v6 v70 v71 htq hF314 hF315 v6_def v70_def v71_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell169 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post59_0 post90_0 v6 v71 v72 v82 v85 v93 v94 v95 v97 v98 v99 v109 htq hts hF2 hF315 hF316 hF320 v6_def v71_def v72_def v82_def v85_def v93_def v94_def v95_def v97_def v98_def v99_def v109_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell170 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post90_0 v6 v93 v94 v95 v97 v98 v99 v100 v109 htq hts hF3 hF320 v6_def v93_def v94_def v95_def v97_def v98_def v99_def v100_def v109_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell171 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post90_0 v6 v100 v102 htq hts hF3 hF56 v6_def v100_def v102_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell172 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post90_0 v6 v102 v103 htq hts hF56 hF57 v6_def v102_def v103_def (by rfl)).trans (getElem!_pos _ _ _)
         · exact (wmNN_cell173 Fr1 Fr2 W _ FrL de r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 post90_0 v6 v102 v103 v104 v114 v118 htq hts hF57 hF58 hF317 v6_def v102_def v103_def v104_def v114_def v118_def (by rfl)).trans (getElem!_pos _ _ _)
       · have htq : extractByte W[129]! 5 = 0#8 := by
           have e : extractByte W[129]! 5 = optTag5 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!] := rfl
           rw [e]
           apply BitVec.eq_of_toNat_eq
           rw [BitVec.toNat_ofNat]
           omega
         have hts : extractByte W[129]! 6 = 0#8 := by
           have e : extractByte W[129]! 6 = optTag6 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!] := rfl
           rw [e]
           apply BitVec.eq_of_toNat_eq
           rw [BitVec.toNat_ofNat]
           omega
         have htq' : inByte W 1037 0 = 0#8 := htq
         have hts' : inByte W 1038 0 = 0#8 := hts
         have e4 : inByte W 1039 0 = boolByte [W[129]!] := rfl
         have hb : (boolByte [W[129]!]).toNat < 2 := by assumption
         have hl0 : 8 ≤ l.toNat := by assumption
         have hl1 : 4 ≤ (l - 8#64).toNat := by assumption
         have hl2 : 1024 ≤ (l - 8#64 - 4#64).toNat := by assumption
         have hl3 : 1 ≤ (l - 8#64 - 4#64 - 1024#64).toNat := by assumption
         have hl4 : 1 ≤ (l - 8#64 - 4#64 - 1024#64 - 1#64).toNat := by assumption
         have hl5 : 1 ≤ (l - 8#64 - 4#64 - 1024#64 - 1#64 - 1#64).toNat := by assumption
         simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hl1 hl2 hl3 hl4 hl5
         have o3 : midO3 W = 1038 := by rw [midO3, htq']; decide
         have o4 : midO4 W = 1039 := by rw [midO4, o3, hts']; decide
         exact ⟨by rw [htq']; decide, by rw [o3, hts']; decide, by rw [o4, e4]; exact hb, by rw [o4]; omega⟩)

end Cases.Zip2005
