import Cases.Zip2005.Witness.Array32R7
import Cases.Zip2005.Witness.OptionBytes32R0
import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Image.F_7801806c
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `deserialize_option::<OptionVisitor<Bytes32>>` (0x7801806c)

bincode's `Option<[u8; 32]>` from a `SliceReader` at `q + 6` over the aligned words `W`: the tag byte, then on `1` the
32 bytes by `ArrayVisitor<u8, 32>` at `q + 1`. `Ok(None)` (bytes 0, 0) on tag 0, `Ok(Some(b))` (bytes
0, 1, then the 32 bytes at `out + 2`) on tag 1 with 33 bytes in the reader, otherwise `Err`: an
empty reader or a short array (the `io::Error` conversion, a contract), or a tag above 1
(`Box<ErrorKind::InvalidTagEncoding>`, `__rust_alloc(0x18, 8)`, T2).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-- The tag byte of the option at `q`. -/
def optTag6 (W : List Word) : BitVec 8 := extractByte W[0]! 6

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option machineChecked.sym.foldBytes true in
theorem option_bytes32_r6_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
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
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) t → Region de [q + 7#64, l - 1#64] t →
      optTag6 W = 0#8 → 1 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkS : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 7) t → Region de [q + 39#64, l - 33#64] t →
      optTag6 W = 1#8 → 33 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t →
      ¬ (optTag6 W = 0#8 ∧ 1 ≤ l.toNat) → ¬ (optTag6 W = 1#8 ∧ 33 ≤ l.toNat) → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x380#64) 112 := hstk.frame 112 (by decide)
  have hu := Unchanged.refl [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
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
  -- the reader's length against the tag
  rcases (by omega : l.toNat = 0 ∨ (1 ≤ l.toNat ∧ l.toNat < 33) ∨ 33 ≤ l.toNat) with hl | ⟨hl, hl'⟩ | hl
  all_goals sym_exec [array32_r7_ok_spec, array32_r7_err_spec, hio, halloc, hhandle]
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v15_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post12_0 :: O.drop 2) s_22 := by
      rw [hd, v15_def]; exact hR0
    clear hR0
    have hx0 : ¬ (optTag6 W = 0#8 ∧ 1 ≤ l.toNat) := fun h => absurd h.2 (by omega)
    have hx1 : ¬ (optTag6 W = 1#8 ∧ 33 ≤ l.toNat) := fun h => absurd h.2 (by omega)
    sym_close (hkE _ post12_0 (q + 6#64) (l))
  · have h0 : optTag6 W = 0#8 ↔ v8 = 0#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    have h1 : optTag6 W = 1#8 ↔ v8 = 1#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    rw [show BitVec.truncate 16 (0#64) = 0#16 from rfl] at v14_def
    have hd : O.drop 1 = [O[1]!, O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) s_20 := by
      rw [hd, v14_def]; exact hR0
    clear hR0
    have hl1 : l + 18446744073709551615#64 = l - 1#64 := by bv_omega
    rw [hl1] at hR1
    have ht : optTag6 W = 0#8 := h0.mpr (by simpa using hbr13)
    have hl0 : 1 ≤ l.toNat := by omega
    sym_close hkN
  · have h0 : optTag6 W = 0#8 ↔ v8 = 0#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    have h1 : optTag6 W = 1#8 ↔ v8 = 1#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v31_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post23_0 :: O.drop 2) s_38 := by
      rw [hd, v31_def]; exact hR0
    clear hR0
    have hn0 : optTag6 W ≠ 0#8 := fun h => hbr13 (by simpa using h0.mp h)
    have hn1 : optTag6 W ≠ 1#8 := fun h => by simp [h1.mp h] at hbr15
    have hx0 : ¬ (optTag6 W = 0#8 ∧ 1 ≤ l.toNat) := fun h => hn0 h.1
    have hx1 : ¬ (optTag6 W = 1#8 ∧ 33 ≤ l.toNat) := fun h => hn1 h.1
    sym_close (hkE _ post23_0 (q + 7#64) (l + 18446744073709551615#64))
  · have h0 : optTag6 W = 0#8 ↔ v8 = 0#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    have h1 : optTag6 W = 1#8 ↔ v8 = 1#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v26_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post20_0 :: O.drop 2) s_32 := by
      rw [hd, v26_def]; exact hR0
    clear hR0
    have ht : optTag6 W = 1#8 := h1.mpr (by simpa using hbr15)
    have hx0 : ¬ (optTag6 W = 0#8 ∧ 1 ≤ l.toNat) := fun h => absurd (ht ▸ h.1) (by decide)
    have hx1 : ¬ (optTag6 W = 1#8 ∧ 33 ≤ l.toNat) := fun h => absurd h.2 (by omega)
    sym_close (hkE _ post20_0 (post20_1) (post20_2))
  · have h0 : optTag6 W = 0#8 ↔ v8 = 0#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    have h1 : optTag6 W = 1#8 ↔ v8 = 1#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    rw [show BitVec.truncate 16 (0#64) = 0#16 from rfl] at v14_def
    have hd : O.drop 1 = [O[1]!, O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) s_20 := by
      rw [hd, v14_def]; exact hR0
    clear hR0
    have hl1 : l + 18446744073709551615#64 = l - 1#64 := by bv_omega
    rw [hl1] at hR1
    have ht : optTag6 W = 0#8 := h0.mpr (by simpa using hbr13)
    have hl0 : 1 ≤ l.toNat := by omega
    sym_close hkN
  · have h0 : optTag6 W = 0#8 ↔ v8 = 0#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    have h1 : optTag6 W = 1#8 ↔ v8 = 1#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v31_def
    have hd : O.drop 2 = [O[2]!, O[3]!, O[4]!] := by rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl]; rfl
    have hRo : Region out (replaceByte O[0]! 0 1#8 :: post23_0 :: O.drop 2) s_38 := by
      rw [hd, v31_def]; exact hR0
    clear hR0
    have hn0 : optTag6 W ≠ 0#8 := fun h => hbr13 (by simpa using h0.mp h)
    have hn1 : optTag6 W ≠ 1#8 := fun h => by simp [h1.mp h] at hbr15
    have hx0 : ¬ (optTag6 W = 0#8 ∧ 1 ≤ l.toNat) := fun h => hn0 h.1
    have hx1 : ¬ (optTag6 W = 1#8 ∧ 33 ≤ l.toNat) := fun h => hn1 h.1
    sym_close (hkE _ post23_0 (q + 7#64) (l + 18446744073709551615#64))
  · have h0 : optTag6 W = 0#8 ↔ v8 = 0#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    have h1 : optTag6 W = 1#8 ↔ v8 = 1#64 := by
      rw [← v8_def, optTag6]
      constructor
      · intro h; rw [h]; rfl
      · intro h; have := congrArg (BitVec.truncate 8) h; rwa [trunc8_zext] at this
    have ht : optTag6 W = 1#8 := h1.mpr (by simpa using hbr15)
    have c0 : v124 = (someW O W 7)[0]! := by
      subst v124_def v123_def v56_def v55_def v35_def v34_def v30_def v29_def v28_def v27_def v26_def v25_def v24_def v23_def acc20_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c1 : v58 = (someW O W 7)[1]! := by
      subst v58_def v57_def v54_def v53_def v52_def v51_def v50_def v49_def v48_def v47_def v45_def v44_def v43_def v42_def v37_def v36_def acc20_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c2 : v93 = (someW O W 7)[2]! := by
      subst v93_def v92_def v91_def v86_def v85_def v84_def v83_def v81_def v80_def v79_def v78_def v77_def v76_def v75_def v46_def v41_def v37_def v31_def acc20_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c3 : v107 = (someW O W 7)[3]! := by
      subst v107_def v106_def v105_def v103_def v102_def v101_def v100_def v97_def v96_def v95_def v94_def v90_def v89_def v88_def v87_def v82_def v32_def v31_def acc20_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have c4 : v120 = (someW O W 7)[4]! := by
      subst v120_def v119_def v108_def v98_def v33_def v32_def acc20_0_def
      apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
    have e : [v124, v58, v93, v107, v120] = someW O W 7 := by
      rw [c0, c1, c2, c3, c4]; rfl
    rw [e] at hR0
    have hq1 : q + 39#64 = q + 39#64 := by bv_omega
    have hl1 : l + 18446744073709551615#64 - 32#64 = l - 33#64 := by bv_omega
    rw [hq1, hl1] at hR1
    have hl0 : 33 ≤ l.toNat := by omega
    sym_close hkS

theorem option_bytes32_r6_none_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (htag : optTag6 W = 0#8) (hl : 1 ≤ l.toNat)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
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
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) t → Region de [q + 7#64, l - 1#64] t →
      Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r6_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun t h1 h2 h3 h4 h5 h6 _ _ hH => hkN t h1 h2 h3 h4 h5 h6 hH)
    (fun _ _ _ _ _ _ _ h1 _ _ => absurd (htag.symm.trans h1) (by decide))
    (fun _ _ _ _ _ _ _ _ _ _ hx _ _ => absurd ⟨htag, hl⟩ hx)

theorem option_bytes32_r6_some_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (htag : optTag6 W = 1#8) (hl : 33 ≤ l.toNat)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
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
    (hkS : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 7) t → Region de [q + 39#64, l - 33#64] t →
      Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r6_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ h0 _ _ => absurd (htag.symm.trans h0) (by decide))
    (fun t h1 h2 h3 h4 h5 h6 _ _ hH => hkS t h1 h2 h3 h4 h5 h6 hH)
    (fun _ _ _ _ _ _ _ _ _ _ _ hx _ => absurd ⟨htag, hl⟩ hx)

theorem option_bytes32_r6_err_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hx0 : ¬ (optTag6 W = 0#8 ∧ 1 ≤ l.toNat)) (hx1 : ¬ (optTag6 W = 1#8 ∧ 33 ≤ l.toNat))
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
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
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t →
      Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r6_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ h0 h1 _ => absurd ⟨h0, h1⟩ hx0)
    (fun _ _ _ _ _ _ _ h0 h1 _ => absurd ⟨h0, h1⟩ hx1)
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hH)

end Cases.Zip2005
