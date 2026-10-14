import Cases.Zip2005.Witness.ArrayBytes32
import Cases.Zip2005.Witness.NextArrCells
import Cases.Zip2005.Runtime.Memcpy_d0s0_1009
import Cases.Zip2005.Runtime.Memcpy_d1s0_1009
import Cases.Zip2005.Image.F_780197cc
import Cases.Zip2005.Image.Ro

/-!
# `SeqAccess::next_element::<[Bytes32; 32]>` (0x780197cc)

The witness's auth path as a struct field: with `c ≠ 0` fields left the count is decremented and
`ArrayVisitor<Bytes32, 32>` reads into the frame; its `Ok` payload is moved one byte up into
`Ok(Some(path))` (tags 0 and 1, the 1024 input bytes from offset 5 at `out + 2`, `optArrW`) through
two 1009-byte `memcpy`s, or its `Err` passed up. With `c = 0` the result is `Ok(None)`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option asmverif.sym.foldBytes true in
theorem next_arr_bytes32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out acs de q l c : Word)
    (O WW : List Word) (hOl : O.length = 129) (hWl : WW.length = 129)
    (hpc : s.pc = 0x780197cc#64) (hcode : CodeAt F_780197cc.base F_780197cc.prog s)
    (hcodeV : CodeAt F_78016938.base F_78016938.prog s)
    (hcodeE : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1120 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 129)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q WW s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 129)
    (hdO : Disjoint (sp - 0x1120#64) 548 out 129) (hdA : Disjoint (sp - 0x1120#64) 548 acs 2)
    (hdD : Disjoint (sp - 0x1120#64) 548 de 2)
    (heA : Disjoint out 129 acs 2) (heD : Disjoint out 129 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 1032 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1120#64, 548), (out, 129), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) t → Region acs [de, c] t →
      Region de [q + 5#64, l] t → c = 0#64 → SafeN G n P t)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1120#64, 548), (out, 129), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (optArrW O WW 5) t → Region acs [de, c - 1#64] t →
      Region de [q + 1029#64, l - 1024#64] t → c ≠ 0#64 → 1024 ≤ l.toNat → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1120#64, 548), (out, 129), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → c ≠ 0#64 → l.toNat < 1024 → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1120#64) 548 := hstk.frame 548 (by decide)
  have hu := Unchanged.refl [(sp - 0x1120#64, 548), (out, 129), (acs, 2), (de, 2),
    (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  -- below the read-only segment too (the misaligned `memcpy` reads its jump table)
  have hokOr : RegionOk Ro.layout.roBase Ro.layout.textHi out 129 :=
    ⟨hokO.aligned, hokO.inMem, Or.inl (by simp only [Ro.layout_roBase]; omega)⟩
  have hmS : sp &&& 7#64 = 0#64 := by
    have ha := hstk.aligned
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    simp only [BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  -- the frame (`sp' = sp - 0x820`): [0, 8), the copy buffer [8, 0x400), the array result
  -- [0x400, 0x808), saves [0x808, 0x820)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x820#64) 1 := hokS.sub' 288 1 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x818#64) 127 := hokS.sub' 289 127 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x420#64) 129 := hokS.sub' 416 129 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokS.sub' 545 3 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x820#64) 1 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x818#64) 127 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x420#64) 129 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  sym_exec [array_bytes32_ok_spec, array_bytes32_err_spec, memcpy_d0s0_1009_spec,
    memcpy_d1s0_1009_spec, hio]
  · have hc : c = 0#64 := by simpa using hbr7
    rw [show BitVec.truncate 16 (0#64) = 0#16 from rfl] at v8_def
    have hd : O.drop 1 = [O[1]!, O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) s_15 := by
      rw [hd, v8_def]; exact hR0
    clear hR0
    sym_close hkN
  · have hc : c ≠ 0#64 := by simpa using hbr7
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    rw [hc1] at hR1
    have c0 := na32_cell0 O WW F2 acc16_0 v19 v20 v23 v24 v26 v27 v28 v29 v30 v31 v32 v33 v59 acc16_0_def v19_def v20_def v23_def v24_def v26_def v27_def v28_def v29_def v30_def v31_def v32_def v33_def v59_def
    have c1 := na32_cell1 O WW F2 acc16_0 v21 v22 v25 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v60 v61 v62 acc16_0_def v21_def v22_def v25_def v48_def v49_def v50_def v51_def v52_def v53_def v54_def v55_def v56_def v57_def v60_def v61_def v62_def
    have c2 := na32_cell2 O WW F1 F2 acc16_0 v22 acc39_0 acc45_0 v46 v47 acc16_0_def v22_def acc39_0_def acc45_0_def v46_def v47_def
    have c3 := na32_cell3 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c4 := na32_cell4 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c5 := na32_cell5 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c6 := na32_cell6 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c7 := na32_cell7 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c8 := na32_cell8 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c9 := na32_cell9 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c10 := na32_cell10 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c11 := na32_cell11 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c12 := na32_cell12 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c13 := na32_cell13 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c14 := na32_cell14 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c15 := na32_cell15 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c16 := na32_cell16 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c17 := na32_cell17 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c18 := na32_cell18 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c19 := na32_cell19 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c20 := na32_cell20 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c21 := na32_cell21 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c22 := na32_cell22 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c23 := na32_cell23 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c24 := na32_cell24 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c25 := na32_cell25 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c26 := na32_cell26 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c27 := na32_cell27 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c28 := na32_cell28 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c29 := na32_cell29 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c30 := na32_cell30 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c31 := na32_cell31 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c32 := na32_cell32 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c33 := na32_cell33 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c34 := na32_cell34 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c35 := na32_cell35 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c36 := na32_cell36 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c37 := na32_cell37 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c38 := na32_cell38 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c39 := na32_cell39 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c40 := na32_cell40 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c41 := na32_cell41 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c42 := na32_cell42 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c43 := na32_cell43 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c44 := na32_cell44 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c45 := na32_cell45 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c46 := na32_cell46 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c47 := na32_cell47 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c48 := na32_cell48 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c49 := na32_cell49 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c50 := na32_cell50 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c51 := na32_cell51 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c52 := na32_cell52 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c53 := na32_cell53 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c54 := na32_cell54 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c55 := na32_cell55 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c56 := na32_cell56 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c57 := na32_cell57 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c58 := na32_cell58 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c59 := na32_cell59 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c60 := na32_cell60 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c61 := na32_cell61 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c62 := na32_cell62 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c63 := na32_cell63 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c64 := na32_cell64 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c65 := na32_cell65 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c66 := na32_cell66 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c67 := na32_cell67 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c68 := na32_cell68 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c69 := na32_cell69 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c70 := na32_cell70 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c71 := na32_cell71 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c72 := na32_cell72 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c73 := na32_cell73 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c74 := na32_cell74 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c75 := na32_cell75 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c76 := na32_cell76 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c77 := na32_cell77 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c78 := na32_cell78 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c79 := na32_cell79 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c80 := na32_cell80 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c81 := na32_cell81 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c82 := na32_cell82 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c83 := na32_cell83 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c84 := na32_cell84 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c85 := na32_cell85 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c86 := na32_cell86 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c87 := na32_cell87 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c88 := na32_cell88 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c89 := na32_cell89 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c90 := na32_cell90 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c91 := na32_cell91 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c92 := na32_cell92 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c93 := na32_cell93 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c94 := na32_cell94 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c95 := na32_cell95 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c96 := na32_cell96 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c97 := na32_cell97 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c98 := na32_cell98 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c99 := na32_cell99 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c100 := na32_cell100 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c101 := na32_cell101 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c102 := na32_cell102 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c103 := na32_cell103 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c104 := na32_cell104 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c105 := na32_cell105 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c106 := na32_cell106 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c107 := na32_cell107 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c108 := na32_cell108 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c109 := na32_cell109 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c110 := na32_cell110 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c111 := na32_cell111 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c112 := na32_cell112 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c113 := na32_cell113 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c114 := na32_cell114 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c115 := na32_cell115 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c116 := na32_cell116 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c117 := na32_cell117 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c118 := na32_cell118 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c119 := na32_cell119 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c120 := na32_cell120 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c121 := na32_cell121 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c122 := na32_cell122 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c123 := na32_cell123 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c124 := na32_cell124 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c125 := na32_cell125 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c126 := na32_cell126 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c127 := na32_cell127 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have c128 := na32_cell128 O WW F1 F2 acc16_0 acc39_0 acc45_0 acc16_0_def acc39_0_def acc45_0_def
    have e : [v59, v62, v47, acc45_0[1]!, acc45_0[2]!, acc45_0[3]!, acc45_0[4]!, acc45_0[5]!, acc45_0[6]!, acc45_0[7]!, acc45_0[8]!, acc45_0[9]!, acc45_0[10]!, acc45_0[11]!, acc45_0[12]!, acc45_0[13]!, acc45_0[14]!, acc45_0[15]!, acc45_0[16]!, acc45_0[17]!, acc45_0[18]!, acc45_0[19]!, acc45_0[20]!, acc45_0[21]!, acc45_0[22]!, acc45_0[23]!, acc45_0[24]!, acc45_0[25]!, acc45_0[26]!, acc45_0[27]!, acc45_0[28]!, acc45_0[29]!, acc45_0[30]!, acc45_0[31]!, acc45_0[32]!, acc45_0[33]!, acc45_0[34]!, acc45_0[35]!, acc45_0[36]!, acc45_0[37]!, acc45_0[38]!, acc45_0[39]!, acc45_0[40]!, acc45_0[41]!, acc45_0[42]!, acc45_0[43]!, acc45_0[44]!, acc45_0[45]!, acc45_0[46]!, acc45_0[47]!, acc45_0[48]!, acc45_0[49]!, acc45_0[50]!, acc45_0[51]!, acc45_0[52]!, acc45_0[53]!, acc45_0[54]!, acc45_0[55]!, acc45_0[56]!, acc45_0[57]!, acc45_0[58]!, acc45_0[59]!, acc45_0[60]!, acc45_0[61]!, acc45_0[62]!, acc45_0[63]!, acc45_0[64]!, acc45_0[65]!, acc45_0[66]!, acc45_0[67]!, acc45_0[68]!, acc45_0[69]!, acc45_0[70]!, acc45_0[71]!, acc45_0[72]!, acc45_0[73]!, acc45_0[74]!, acc45_0[75]!, acc45_0[76]!, acc45_0[77]!, acc45_0[78]!, acc45_0[79]!, acc45_0[80]!, acc45_0[81]!, acc45_0[82]!, acc45_0[83]!, acc45_0[84]!, acc45_0[85]!, acc45_0[86]!, acc45_0[87]!, acc45_0[88]!, acc45_0[89]!, acc45_0[90]!, acc45_0[91]!, acc45_0[92]!, acc45_0[93]!, acc45_0[94]!, acc45_0[95]!, acc45_0[96]!, acc45_0[97]!, acc45_0[98]!, acc45_0[99]!, acc45_0[100]!, acc45_0[101]!, acc45_0[102]!, acc45_0[103]!, acc45_0[104]!, acc45_0[105]!, acc45_0[106]!, acc45_0[107]!, acc45_0[108]!, acc45_0[109]!, acc45_0[110]!, acc45_0[111]!, acc45_0[112]!, acc45_0[113]!, acc45_0[114]!, acc45_0[115]!, acc45_0[116]!, acc45_0[117]!, acc45_0[118]!, acc45_0[119]!, acc45_0[120]!, acc45_0[121]!, acc45_0[122]!, acc45_0[123]!, acc45_0[124]!, acc45_0[125]!, acc45_0[126]!] = optArrW O WW 5 := by
      rw [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127, c128]
      conv_rhs => rw [AsmVerif.RiscV.Sym.List.eq_map_range (optArrW O WW 5) (optArrW_length O WW 5)]
      rfl
    rw [e] at hR0
    sym_close hk
  · exfalso
    have ht : v17 = 0#64 := by
      rw [← v17_def, ← acc16_0_def]
      simp (disch := decide) only [byte_pre]
      rfl
    exact hbr18 (by simp [ht])
  · have hc : c ≠ 0#64 := by simpa using hbr7
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    rw [hc1] at hR1
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v21_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post16_0 :: O.drop 2) s_29 := by
      rw [hd, v21_def]; exact hR0
    clear hR0
    have hlt : l.toNat < 1024 := by omega
    sym_close (hkE _ post16_0 post16_1 post16_2)

theorem optArrW_tag0 (O W : List Word) (r : Nat) : extractByte (optArrW O W r)[0]! 0 = 0#8 := by
  simp (disch := decide) only [byte_simp]

theorem optArrW_tag1 (O W : List Word) (r : Nat) : extractByte (optArrW O W r)[0]! 1 = 1#8 := by
  simp (disch := decide) only [byte_simp]

/-- `Ok(None)`: no fields left. -/
theorem next_arr_bytes32_none_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out acs de q l c : Word)
    (O WW : List Word) (hOl : O.length = 129) (hWl : WW.length = 129)
    (hpc : s.pc = 0x780197cc#64) (hcode : CodeAt F_780197cc.base F_780197cc.prog s)
    (hcodeV : CodeAt F_78016938.base F_78016938.prog s)
    (hcodeE : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1120 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 129)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q WW s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 129)
    (hdO : Disjoint (sp - 0x1120#64) 548 out 129) (hdA : Disjoint (sp - 0x1120#64) 548 acs 2)
    (hdD : Disjoint (sp - 0x1120#64) 548 de 2)
    (heA : Disjoint out 129 acs 2) (heD : Disjoint out 129 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 1032 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hc : c = 0#64)
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1120#64, 548), (out, 129), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) t → Region acs [de, c] t →
      Region de [q + 5#64, l] t → SafeN G n P t) :
    SafeN G n P s :=
  next_arr_bytes32_spec s ra sp out acs de q l c O WW hOl hWl hpc hcode hcodeV hcodeE hcodeA hcodeN hcodeM hcw hro hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun t h1 h2 h3 h4 h5 h6 h7 _ => hkN t h1 h2 h3 h4 h5 h6 h7)
    (fun _ _ _ _ _ _ _ _ hc' _ => absurd hc hc')
    (fun _ _ _ _ _ _ _ _ _ _ _ hc' _ => absurd hc hc')

/-- `Ok(Some(path))`: 1024 bytes left. -/
theorem next_arr_bytes32_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out acs de q l c : Word)
    (O WW : List Word) (hOl : O.length = 129) (hWl : WW.length = 129)
    (hpc : s.pc = 0x780197cc#64) (hcode : CodeAt F_780197cc.base F_780197cc.prog s)
    (hcodeV : CodeAt F_78016938.base F_78016938.prog s)
    (hcodeE : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1120 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 129)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q WW s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 129)
    (hdO : Disjoint (sp - 0x1120#64) 548 out 129) (hdA : Disjoint (sp - 0x1120#64) 548 acs 2)
    (hdD : Disjoint (sp - 0x1120#64) 548 de 2)
    (heA : Disjoint out 129 acs 2) (heD : Disjoint out 129 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 1032 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (hl : 1024 ≤ l.toNat)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1120#64, 548), (out, 129), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (optArrW O WW 5) t → extractByte (optArrW O WW 5)[0]! 0 = 0#8 →
      extractByte (optArrW O WW 5)[0]! 1 = 1#8 → Region acs [de, c - 1#64] t →
      Region de [q + 1029#64, l - 1024#64] t → SafeN G n P t) :
    SafeN G n P s :=
  next_arr_bytes32_spec s ra sp out acs de q l c O WW hOl hWl hpc hcode hcodeV hcodeE hcodeA hcodeN hcodeM hcw hro hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun _ _ _ _ _ _ _ _ hc' => absurd hc' hc)
    (fun t h1 h2 h3 h4 h5 h6 h7 _ _ => hk t h1 h2 h3 h4 h5 (optArrW_tag0 O WW 5) (optArrW_tag1 O WW 5) h6 h7)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hlt => absurd hl (by omega))

/-- `Err`: fewer than 1024 bytes left. -/
theorem next_arr_bytes32_err_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out acs de q l c : Word)
    (O WW : List Word) (hOl : O.length = 129) (hWl : WW.length = 129)
    (hpc : s.pc = 0x780197cc#64) (hcode : CodeAt F_780197cc.base F_780197cc.prog s)
    (hcodeV : CodeAt F_78016938.base F_78016938.prog s)
    (hcodeE : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1120 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 129)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q WW s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 129)
    (hdO : Disjoint (sp - 0x1120#64) 548 out 129) (hdA : Disjoint (sp - 0x1120#64) 548 acs 2)
    (hdD : Disjoint (sp - 0x1120#64) 548 de 2)
    (heA : Disjoint out 129 acs 2) (heD : Disjoint out 129 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 1032 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (hl : l.toNat < 1024)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1120#64, 548), (out, 129), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → SafeN G n P t) :
    SafeN G n P s :=
  next_arr_bytes32_spec s ra sp out acs de q l c O WW hOl hWl hpc hcode hcodeV hcodeE hcodeA hcodeN hcodeM hcw hro hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun _ _ _ _ _ _ _ _ hc' => absurd hc' hc)
    (fun _ _ _ _ _ _ _ _ _ h1024 => absurd hl (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ _ => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7)

end Cases.Zip2005
