import Cases.Zip2005.Witness.OptionBytes32R6
import Cases.Zip2005.Kit.ByteHalf
import Cases.Zip2005.Image.F_78019918
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `SeqAccess::next_element::<Option<Bytes32>>` (0x78019918), the tag at residue 6

The witness's `sigma_qsk`: with `c ≠ 0` fields left the count is decremented and
`deserialize_option<Bytes32>` reads into the frame; its `Ok` is moved to `out` with the `Ok` tag
cleared (`Ok(Some(None))`: tags 0, 0; `Ok(Some(Some(bytes)))`: `someW O W 7`), its `Err` passed
up. With `c = 0` the result is `Ok(None)` (the niche tag 2 in byte 1).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option machineChecked.sym.foldBytes true in
theorem next_opt_r6_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk0 : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceHalfword O[0]! 0 0x200#16 :: O.drop 1) t → Region acs [de, c] t →
      Region de [q + 6#64, l] t → c = 0#64 → Run.HeapAt L t → SafeN G n P t)
    (hkN : ∀ (t : MachineState) (J : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      J.length = 5 → Region out J t → extractByte J[0]! 0 = 0#8 → extractByte J[0]! 1 = 0#8 →
      Region acs [de, c - 1#64] t → Region de [q + 7#64, l - 1#64] t → c ≠ 0#64 →
      optTag6 W = 0#8 → 1 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkS : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 7) t → Region acs [de, c - 1#64] t → Region de [q + 39#64, l - 33#64] t →
      c ≠ 0#64 → optTag6 W = 1#8 → 33 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → c ≠ 0#64 → ¬ (optTag6 W = 0#8 ∧ 1 ≤ l.toNat) →
      ¬ (optTag6 W = 1#8 ∧ 33 ≤ l.toNat) → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x3d0#64) 122 := hstk.frame 122 (by decide)
  have hu := Unchanged.refl [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2),
    (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
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
  -- the frame (`sp' = sp - 0x50`): locals [0, 0x18), the option's result [0x18, 0x40), saves
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 3 := hokS.sub' 112 3 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x38#64) 5 := hokS.sub' 115 5 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokS.sub' 120 2 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x50#64) 3 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x38#64) 5 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl] at hO
  have e : optTag6 [W[0]!, W[1]!, W[2]!, W[3]!, W[4]!] = optTag6 W := rfl
  rcases Classical.em (optTag6 W = 0#8 ∧ 1 ≤ l.toNat) with ⟨htag, hl⟩ | hn0
  · rw [← e] at htag
    sym_exec [option_bytes32_r6_none_spec, hhandle, halloc, hio]
    · have hc : c = 0#64 := by simpa using hbr5
      rw [show BitVec.truncate 16 (512#64) = 0x200#16 from rfl] at v7_def
      have hd : O.drop 1 = [O[1]!, O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
      have hRo : Region out (replaceHalfword O[0]! 0 0x200#16 :: O.drop 1) s_12 := by
        rw [hd, v7_def]; exact hR0
      clear hR0
      sym_close hk0
    · have hc : c ≠ 0#64 := by simpa using hbr5
      have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
      rw [hc1] at hR1
      have hJ : [v34, v23, v28, v29, v44].length = 5 := rfl
      have hb0 : extractByte [v34, v23, v28, v29, v44][0]! 0 = 0#8 := by
        rw [← v34_def, ← v33_def, ← v32_def, ← v31_def]
        simp (disch := decide) only [byte_simp]
      have hb1 : extractByte [v34, v23, v28, v29, v44][0]! 1 = 0#8 := by
        rw [← v34_def, ← v33_def, ← v32_def, ← v16_def]
        simp (disch := decide) only [byte_simp]
      rw [e] at htag
      sym_close (hkN _ [v34, v23, v28, v29, v44])
    · exfalso
      have h0 : v14 = 0#64 := by rw [← v14_def]; rfl
      exact hbr15 (by simp [h0])
  rcases Classical.em (optTag6 W = 1#8 ∧ 33 ≤ l.toNat) with ⟨htag, hl⟩ | hn1
  · rw [← e] at htag
    sym_exec [option_bytes32_r6_some_spec, hhandle, halloc, hio]
    · have hc : c = 0#64 := by simpa using hbr5
      rw [show BitVec.truncate 16 (512#64) = 0x200#16 from rfl] at v7_def
      have hd : O.drop 1 = [O[1]!, O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
      have hRo : Region out (replaceHalfword O[0]! 0 0x200#16 :: O.drop 1) s_12 := by
        rw [hd, v7_def]; exact hR0
      clear hR0
      sym_close hk0
    · have hc : c ≠ 0#64 := by simpa using hbr5
      have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
      rw [hc1] at hR1
      have c0 : v34 = (someW O W 7)[0]! := by
        rw [← v34_def, ← v33_def, ← v32_def, ← v31_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def,
          ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← acc13_0_def]
        apply word_ext
        intro k hk
        interval_cases k <;> simp (disch := decide) only [byte_simp]
      have c1 : v23 = (someW O W 7)[1]! := by
        rw [← v23_def, ← acc13_0_def]
        apply word_ext
        intro k hk
        interval_cases k <;> simp (disch := decide) only [byte_simp]
      have c2 : v28 = (someW O W 7)[2]! := by
        rw [← v28_def, ← acc13_0_def]
        apply word_ext
        intro k hk
        interval_cases k <;> simp (disch := decide) only [byte_simp]
      have c3 : v29 = (someW O W 7)[3]! := by
        rw [← v29_def, ← acc13_0_def]
        apply word_ext
        intro k hk
        interval_cases k <;> simp (disch := decide) only [byte_simp]
      have c4 : v44 = (someW O W 7)[4]! := by
        rw [← v44_def, ← v40_def, ← v30_def, ← acc13_0_def]
        apply word_ext
        intro k hk
        interval_cases k <;> simp (disch := decide) only [byte_simp]
      have ew : [v34, v23, v28, v29, v44] = someW O W 7 := by
        rw [c0, c1, c2, c3, c4]; rfl
      rw [ew] at hR0
      rw [e] at htag
      sym_close hkS
    · exfalso
      have h0 : v14 = 0#64 := by
        rw [← v14_def, ← acc13_0_def, someW_tag0]; rfl
      exact hbr15 (by simp [h0])
  rw [← e] at hn0 hn1
  sym_exec [option_bytes32_r6_err_spec, hhandle, halloc, hio]
  · have hc : c = 0#64 := by simpa using hbr5
    rw [show BitVec.truncate 16 (512#64) = 0x200#16 from rfl] at v7_def
    have hd : O.drop 1 = [O[1]!, O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceHalfword O[0]! 0 0x200#16 :: O.drop 1) s_12 := by
      rw [hd, v7_def]; exact hR0
    clear hR0
    sym_close hk0
  · have hc : c ≠ 0#64 := by simpa using hbr5
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    rw [hc1] at hR1
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v18_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post13_0 :: O.drop 2) s_24 := by
      rw [hd, v18_def]; exact hR0
    clear hR0
    rw [e] at hn0 hn1
    sym_close (hkE _ post13_0 post13_1 post13_2)

end Cases.Zip2005
