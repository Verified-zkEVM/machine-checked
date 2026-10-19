import Cases.Zip2005.Witness.Array32R5
import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Image.F_78019a10
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `SeqAccess::next_element::<Bytes32>` (0x78019a10), elements at residue 5

One element of the witness's `[Bytes32; 32]` auth path: with `c ≠ 0` elements left the count is
decremented and `ArrayVisitor<u8, 32>` reads the 32 bytes at `q + 5`; the result is
`Ok(Some(bytes))` (tags 0 and 1, the bytes at `out + 2`, `someW O W 5`), or the array's `Err`
passed up.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option machineChecked.sym.foldBytes true in
theorem next_bytes32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019a10#64) (hcode : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2) (hc : c ≠ 0#64)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdA : Disjoint (sp - 0x380#64) 112 acs 2)
    (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 5) t → Region acs [de, c - 1#64] t →
      Region de [q + 37#64, l - 32#64] t → 32 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → l.toNat < 32 → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x380#64) 112 := hstk.frame 112 (by decide)
  have hu := Unchanged.refl [(sp - 0x380#64, 112), (out, 5), (acs, 2), (de, 2),
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
  -- the frame (`sp' = sp - 0x60`): locals [0, 0x20), the array result [0x20, 0x48), saves [0x48, 0x60)
  have hokL : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 4 := hokS.sub' 100 4 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 5 := hokS.sub' 104 5 (by decide) (by bv_omega)
  have hokV : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokS.sub' 109 3 (by decide) (by bv_omega)
  obtain ⟨FL, hFL, hFLl⟩ := Region.exists_junk (sp - 0x60#64) 4 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x40#64) 5 s
  obtain ⟨FV, hFV, hFVl⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [MachineChecked.RiscV.Sym.List.eq_map_range W hWl] at hW
  rcases (by omega : l.toNat < 32 ∨ 32 ≤ l.toNat) with hl | hl
  all_goals sym_exec [array32_r5_ok_spec, array32_r5_err_spec, hio]
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v20_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post15_0 :: O.drop 2) s_27 := by
      rw [hd, v20_def]; exact hR0
    clear hR0
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    rw [hc1] at hR1
    sym_close (hkE _ post15_0 post15_1 post15_2)
  · have c0 : v115 = (someW O W 5)[0]! := by
      subst v115_def v35_def v34_def v33_def v32_def v28_def v27_def v26_def v25_def v23_def v22_def v19_def v18_def acc15_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c1 : v118 = (someW O W 5)[1]! := by
      subst v118_def v117_def v116_def v113_def v112_def v111_def v110_def v109_def v108_def v107_def v106_def v105_def v104_def v24_def v21_def v20_def acc15_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c2 : v103 = (someW O W 5)[2]! := by
      subst v103_def v102_def v73_def v72_def v71_def v66_def v65_def v64_def v63_def v61_def v60_def v59_def v58_def v57_def v56_def v55_def v29_def v21_def acc15_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c3 : v87 = (someW O W 5)[3]! := by
      subst v87_def v86_def v85_def v83_def v82_def v81_def v80_def v77_def v76_def v75_def v74_def v70_def v69_def v68_def v67_def v62_def v30_def v29_def acc15_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c4 : v100 = (someW O W 5)[4]! := by
      subst v100_def v99_def v88_def v78_def v31_def v30_def acc15_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have e : [v115, v118, v103, v87, v100] = someW O W 5 := by
      rw [c0, c1, c2, c3, c4]; rfl
    rw [e] at hR0
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    rw [hc1] at hR1
    sym_close hk

/-- `Ok(Some(bytes))`: the reader has the 32 bytes. -/
theorem next_bytes32_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019a10#64) (hcode : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2) (hc : c ≠ 0#64)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hl : 32 ≤ l.toNat)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdA : Disjoint (sp - 0x380#64) 112 acs 2)
    (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 5) t → extractByte (someW O W 5)[0]! 0 = 0#8 →
      extractByte (someW O W 5)[0]! 1 = 1#8 → Region acs [de, c - 1#64] t →
      Region de [q + 37#64, l - 32#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_bytes32_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hc hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun t h1 h2 h3 h4 h5 h6 h7 _ hH => hk t h1 h2 h3 h4 h5 (someW_tag0 O W 5) (someW_tag1 O W 5) h6 h7 hH)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hlt _ => absurd hl (by omega))

/-- `Err`: fewer than 32 bytes left. -/
theorem next_bytes32_err_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019a10#64) (hcode : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2) (hc : c ≠ 0#64)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hl : l.toNat < 32)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdA : Disjoint (sp - 0x380#64) 112 acs 2)
    (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_bytes32_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hc hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun _ _ _ _ _ _ _ _ h32 _ => absurd h32 (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7 hH)

end Cases.Zip2005
