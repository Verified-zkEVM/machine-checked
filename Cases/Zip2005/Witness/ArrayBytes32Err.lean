import Cases.Zip2005.Witness.ArrayBytes32Ok
import Cases.Zip2005.Image.F_78016938
import Cases.Zip2005.Image.Ro

/-!
# `ArrayVisitor<Bytes32, 32>` (`deserialize_tuple`, 0x78016938)

The witness's auth path: 32 `Bytes32` from a `SliceReader` at `q + 5` over the aligned input words
`WW` (129 of them), the first six by `ArrayVisitor<u8, 32>` directly, the rest through
`next_element<Bytes32>`; each element moved into the frame, and the whole written as
`Ok([Bytes32; 32])`. Here the `Err` case: with fewer than 1024 bytes left, the first element that
finds fewer than 32 passes its `Err` up (tag 1, the boxed error at `out + 8`). The executor splits
on each element's length precondition; the 32 error exits are closed one by one.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- One element of the reader's length: 32 bytes taken, `n` left after. -/
theorem sub32_step (x : Word) (n : Nat) (h1 : 32 ≤ x.toNat) (h2 : n ≤ (x - 32#64).toNat) :
    n + 32 ≤ x.toNat := by
  bv_omega

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option asmverif.sym.foldBytes true in
theorem array_bytes32_err_spec {P : Prop} (s : MachineState) (ra sp out de q l : Word)
    (O WW : List Word) (hOl : O.length = 129) (hWl : WW.length = 129)
    (hpc : s.pc = 0x78016938#64) (hcode : CodeAt F_78016938.base F_78016938.prog s)
    (hcodeE : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x900 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha2 : s.getReg .x12 = 0x20#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 129)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q WW s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 129)
    (hdO : Disjoint (sp - 0x900#64) 288 out 129) (hdD : Disjoint (sp - 0x900#64) 288 de 2)
    (heD : Disjoint out 129 de 2) (hOlo : out.toNat + 1032 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000) (hl : l.toNat < 1024)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Safe P t) → Safe P u)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x900#64, 288), (out, 129), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t → Safe P t) :
    Safe P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x900#64) 288 := hstk.frame 288 (by decide)
  have hu := Unchanged.refl [(sp - 0x900#64, 288), (out, 129), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  have hmS : sp &&& 7#64 = 0#64 := by
    have ha := hstk.aligned
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    simp only [BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  -- the frame (`sp' = sp - 0x560`): [0, 0x10), the `Access` [0x10, 0x20), locals [0x20, 0x4c8),
  -- the element result [0x4c8, 0x4f0), [0x4f0, 0x4f8), saves [0x4f8, 0x560)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x560#64) 2 := hokS.sub' 116 2 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x550#64) 2 := hokS.sub' 118 2 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x540#64) 149 := hokS.sub' 120 149 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x98#64) 5 := hokS.sub' 269 5 (by decide) (by bv_omega)
  have hok4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x70#64) 1 := hokS.sub' 274 1 (by decide) (by bv_omega)
  have hok5 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokS.sub' 275 13 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x560#64) 2 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x550#64) 2 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x540#64) 149 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0x98#64) 5 s
  obtain ⟨F4, hF4, hF4l⟩ := Region.exists_junk (sp - 0x70#64) 1 s
  obtain ⟨F5, hF5, hF5l⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [AsmVerif.RiscV.Sym.List.eq_map_range WW hWl] at hW
  sym_exec [array32_r5_ok_spec, array32_r5_err_spec, next_bytes32_ok_spec, next_bytes32_err_spec, memcpy32_d1s2_spec, memcpy17_spec, hio]
  · -- the all-`Ok` path: 32 elements of 32 bytes, against `l < 1024`
    have g31 := hsp479
    have g30 := sub32_step _ _ hsp469 g31
    have g29 := sub32_step _ _ hsp459 g30
    have g28 := sub32_step _ _ hsp449 g29
    have g27 := sub32_step _ _ hsp439 g28
    have g26 := sub32_step _ _ hsp429 g27
    have g25 := sub32_step _ _ hsp419 g26
    have g24 := sub32_step _ _ hsp409 g25
    have g23 := sub32_step _ _ hsp399 g24
    have g22 := sub32_step _ _ hsp389 g23
    have g21 := sub32_step _ _ hsp379 g22
    have g20 := sub32_step _ _ hsp369 g21
    have g19 := sub32_step _ _ hsp359 g20
    have g18 := sub32_step _ _ hsp349 g19
    have g17 := sub32_step _ _ hsp339 g18
    have g16 := sub32_step _ _ hsp329 g17
    have g15 := sub32_step _ _ hsp319 g16
    have g14 := sub32_step _ _ hsp309 g15
    have g13 := sub32_step _ _ hsp299 g14
    have g12 := sub32_step _ _ hsp289 g13
    have g11 := sub32_step _ _ hsp279 g12
    have g10 := sub32_step _ _ hsp269 g11
    have g9 := sub32_step _ _ hsp259 g10
    have g8 := sub32_step _ _ hsp249 g9
    have g7 := sub32_step _ _ hsp239 g8
    have g6 := sub32_step _ _ hsp229 g7
    have g5 := sub32_step _ _ hsp198 g6
    have g4 := sub32_step _ _ hsp161 g5
    have g3 := sub32_step _ _ hsp128 g4
    have g2 := sub32_step _ _ hsp92 g3
    have g1 := sub32_step _ _ hsp59 g2
    have g0 := sub32_step _ _ hsp23 g1
    exact absurd (Nat.lt_of_lt_of_le hl g0) (Nat.lt_irrefl _)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v484_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post479_0 :: O.drop 2) s_501 := by
      rw [hd, v484_def]; exact hR0
    clear hR0
    sym_close (hkE _ post479_0 post479_1 post479_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v475_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post469_0 :: O.drop 2) s_492 := by
      rw [hd, v475_def]; exact hR0
    clear hR0
    sym_close (hkE _ post469_0 post469_1 post469_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v465_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post459_0 :: O.drop 2) s_482 := by
      rw [hd, v465_def]; exact hR0
    clear hR0
    sym_close (hkE _ post459_0 post459_1 post459_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v455_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post449_0 :: O.drop 2) s_472 := by
      rw [hd, v455_def]; exact hR0
    clear hR0
    sym_close (hkE _ post449_0 post449_1 post449_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v445_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post439_0 :: O.drop 2) s_462 := by
      rw [hd, v445_def]; exact hR0
    clear hR0
    sym_close (hkE _ post439_0 post439_1 post439_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v435_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post429_0 :: O.drop 2) s_452 := by
      rw [hd, v435_def]; exact hR0
    clear hR0
    sym_close (hkE _ post429_0 post429_1 post429_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v425_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post419_0 :: O.drop 2) s_442 := by
      rw [hd, v425_def]; exact hR0
    clear hR0
    sym_close (hkE _ post419_0 post419_1 post419_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v415_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post409_0 :: O.drop 2) s_432 := by
      rw [hd, v415_def]; exact hR0
    clear hR0
    sym_close (hkE _ post409_0 post409_1 post409_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v405_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post399_0 :: O.drop 2) s_422 := by
      rw [hd, v405_def]; exact hR0
    clear hR0
    sym_close (hkE _ post399_0 post399_1 post399_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v395_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post389_0 :: O.drop 2) s_412 := by
      rw [hd, v395_def]; exact hR0
    clear hR0
    sym_close (hkE _ post389_0 post389_1 post389_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v385_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post379_0 :: O.drop 2) s_402 := by
      rw [hd, v385_def]; exact hR0
    clear hR0
    sym_close (hkE _ post379_0 post379_1 post379_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v375_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post369_0 :: O.drop 2) s_392 := by
      rw [hd, v375_def]; exact hR0
    clear hR0
    sym_close (hkE _ post369_0 post369_1 post369_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v365_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post359_0 :: O.drop 2) s_382 := by
      rw [hd, v365_def]; exact hR0
    clear hR0
    sym_close (hkE _ post359_0 post359_1 post359_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v355_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post349_0 :: O.drop 2) s_372 := by
      rw [hd, v355_def]; exact hR0
    clear hR0
    sym_close (hkE _ post349_0 post349_1 post349_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v345_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post339_0 :: O.drop 2) s_362 := by
      rw [hd, v345_def]; exact hR0
    clear hR0
    sym_close (hkE _ post339_0 post339_1 post339_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v335_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post329_0 :: O.drop 2) s_352 := by
      rw [hd, v335_def]; exact hR0
    clear hR0
    sym_close (hkE _ post329_0 post329_1 post329_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v325_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post319_0 :: O.drop 2) s_342 := by
      rw [hd, v325_def]; exact hR0
    clear hR0
    sym_close (hkE _ post319_0 post319_1 post319_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v315_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post309_0 :: O.drop 2) s_332 := by
      rw [hd, v315_def]; exact hR0
    clear hR0
    sym_close (hkE _ post309_0 post309_1 post309_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v305_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post299_0 :: O.drop 2) s_322 := by
      rw [hd, v305_def]; exact hR0
    clear hR0
    sym_close (hkE _ post299_0 post299_1 post299_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v295_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post289_0 :: O.drop 2) s_312 := by
      rw [hd, v295_def]; exact hR0
    clear hR0
    sym_close (hkE _ post289_0 post289_1 post289_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v285_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post279_0 :: O.drop 2) s_302 := by
      rw [hd, v285_def]; exact hR0
    clear hR0
    sym_close (hkE _ post279_0 post279_1 post279_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v275_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post269_0 :: O.drop 2) s_292 := by
      rw [hd, v275_def]; exact hR0
    clear hR0
    sym_close (hkE _ post269_0 post269_1 post269_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v265_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post259_0 :: O.drop 2) s_282 := by
      rw [hd, v265_def]; exact hR0
    clear hR0
    sym_close (hkE _ post259_0 post259_1 post259_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v255_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post249_0 :: O.drop 2) s_272 := by
      rw [hd, v255_def]; exact hR0
    clear hR0
    sym_close (hkE _ post249_0 post249_1 post249_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v245_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post239_0 :: O.drop 2) s_262 := by
      rw [hd, v245_def]; exact hR0
    clear hR0
    sym_close (hkE _ post239_0 post239_1 post239_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v235_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post229_0 :: O.drop 2) s_252 := by
      rw [hd, v235_def]; exact hR0
    clear hR0
    sym_close (hkE _ post229_0 post229_1 post229_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v203_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post198_0 :: O.drop 2) s_220 := by
      rw [hd, v203_def]; exact hR0
    clear hR0
    sym_close (hkE _ post198_0 post198_1 post198_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v166_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post161_0 :: O.drop 2) s_183 := by
      rw [hd, v166_def]; exact hR0
    clear hR0
    sym_close (hkE _ post161_0 post161_1 post161_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v133_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post128_0 :: O.drop 2) s_150 := by
      rw [hd, v133_def]; exact hR0
    clear hR0
    sym_close (hkE _ post128_0 post128_1 post128_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v97_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post92_0 :: O.drop 2) s_114 := by
      rw [hd, v97_def]; exact hR0
    clear hR0
    sym_close (hkE _ post92_0 post92_1 post92_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v64_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post59_0 :: O.drop 2) s_81 := by
      rw [hd, v64_def]; exact hR0
    clear hR0
    sym_close (hkE _ post59_0 post59_1 post59_2)
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v28_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!, O[13]!, O[14]!, O[15]!, O[16]!, O[17]!, O[18]!, O[19]!, O[20]!, O[21]!, O[22]!, O[23]!, O[24]!, O[25]!, O[26]!, O[27]!, O[28]!, O[29]!, O[30]!, O[31]!, O[32]!, O[33]!, O[34]!, O[35]!, O[36]!, O[37]!, O[38]!, O[39]!, O[40]!, O[41]!, O[42]!, O[43]!, O[44]!, O[45]!, O[46]!, O[47]!, O[48]!, O[49]!, O[50]!, O[51]!, O[52]!, O[53]!, O[54]!, O[55]!, O[56]!, O[57]!, O[58]!, O[59]!, O[60]!, O[61]!, O[62]!, O[63]!, O[64]!, O[65]!, O[66]!, O[67]!, O[68]!, O[69]!, O[70]!, O[71]!, O[72]!, O[73]!, O[74]!, O[75]!, O[76]!, O[77]!, O[78]!, O[79]!, O[80]!, O[81]!, O[82]!, O[83]!, O[84]!, O[85]!, O[86]!, O[87]!, O[88]!, O[89]!, O[90]!, O[91]!, O[92]!, O[93]!, O[94]!, O[95]!, O[96]!, O[97]!, O[98]!, O[99]!, O[100]!, O[101]!, O[102]!, O[103]!, O[104]!, O[105]!, O[106]!, O[107]!, O[108]!, O[109]!, O[110]!, O[111]!, O[112]!, O[113]!, O[114]!, O[115]!, O[116]!, O[117]!, O[118]!, O[119]!, O[120]!, O[121]!, O[122]!, O[123]!, O[124]!, O[125]!, O[126]!, O[127]!, O[128]!] := by rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post23_0 :: O.drop 2) s_45 := by
      rw [hd, v28_def]; exact hR0
    clear hR0
    sym_close (hkE _ post23_0 post23_1 post23_2)

end Cases.Zip2005
