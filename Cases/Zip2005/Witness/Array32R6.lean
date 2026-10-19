import Cases.Zip2005.Witness.Array32R0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `ArrayVisitor<u8, 32>` (`deserialize_tuple`, 0x7801775c), input at `q + 6`

The 32 bytes of a `[u8; 32]` read from a bincode `SliceReader` whose pointer is `q + 6` over the
aligned input words `W` (5 of them): the first eight inline, the rest through
`next_element<u8>` (0x78019b50). `Ok` (tag byte 0, the bytes at 1..32) when the reader has 32
bytes left, otherwise `Err` (tag 1, the boxed `io::Error` of the `io::Error -> Box<ErrorKind>`
conversion at 0x78036184, a contract here).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option machineChecked.sym.foldBytes true in
theorem array32_r6_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801775c#64) (hcode : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x300 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha2 : s.getReg .x12 = 0x20#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x300#64) 96 out 5) (hdD : Disjoint (sp - 0x300#64) 96 de 2)
    (hdW : Disjoint (sp - 0x300#64) 96 q 5) (heD : Disjoint out 5 de 2)
    (heW : Disjoint out 5 q 5) (hfW : Disjoint de 2 q 5)
    (hhO : Disjoint 0x78040620#64 14780694332 out 5) (hhD : Disjoint 0x78040620#64 14780694332 de 2)
    (hhW : Disjoint 0x78040620#64 14780694332 q 5)
    -- `From<io::Error> for Box<ErrorKind>` (0x78036184), proved separately
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN Gd n P t) → SafeN Gd n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x300#64, 96), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (arr32W O W 6) t → Region de [q + 38#64, l - 32#64] t → 32 ≤ l.toNat → Run.HeapAt L t → SafeN Gd n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x300#64, 96), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte O[0]! 0 1#8, e, O[2]!, O[3]!, O[4]!] t → Region de [d0, d1] t →
      l.toNat < 32 → Run.HeapAt L t → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x300#64) 96 := hstk.frame 96 (by decide)
  have hu := Unchanged.refl [(sp - 0x300#64, 96), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  -- the frame (0x2a0) and `next_element`'s on its error path (0x10)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64) 84 := hokS.sub' 12 84 (by decide) (by bv_omega)
  have hokG : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2b0#64) 2 := hokS.sub' 10 2 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x2a0#64) 84 s
  obtain ⟨G, hG, hGl⟩ := Region.exists_junk (sp - 0x2b0#64) 2 s
  rw [MachineChecked.RiscV.Sym.List.eq_map_range W hWl] at hW
  rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl] at hO
  sym_exec [hio]
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v26_def
    subst v26_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr18
      bv_omega
    sym_close (hkE _ post24_0 (q + 6#64) (l))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v35_def
    subst v35_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr27
      bv_omega
    sym_close (hkE _ post33_0 (q + 7#64) (l + 18446744073709551615#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v43_def
    subst v43_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr35
      bv_omega
    sym_close (hkE _ post41_0 (q + 8#64) (l + 18446744073709551614#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v51_def
    subst v51_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr43
      bv_omega
    sym_close (hkE _ post49_0 (q + 9#64) (l + 18446744073709551613#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v59_def
    subst v59_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr51
      bv_omega
    sym_close (hkE _ post57_0 (q + 10#64) (l + 18446744073709551612#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v67_def
    subst v67_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr59
      bv_omega
    sym_close (hkE _ post65_0 (q + 11#64) (l + 18446744073709551611#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v75_def
    subst v75_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr67
      bv_omega
    sym_close (hkE _ post73_0 (q + 12#64) (l + 18446744073709551610#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v85_def
    subst v85_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr77
      bv_omega
    sym_close (hkE _ post83_0 (q + 13#64) (l + 18446744073709551609#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v119_def
    subst v119_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr93
      bv_omega
    sym_close (hkE _ post104_0 (q + 14#64) (l + 18446744073709551608#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v146_def
    subst v146_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr120
      bv_omega
    sym_close (hkE _ post131_0 (q + 15#64) (l + 18446744073709551607#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v173_def
    subst v173_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr147
      bv_omega
    sym_close (hkE _ post158_0 (q + 16#64) (l + 18446744073709551606#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v200_def
    subst v200_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr174
      bv_omega
    sym_close (hkE _ post185_0 (q + 17#64) (l + 18446744073709551605#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v228_def
    subst v228_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr202
      bv_omega
    sym_close (hkE _ post213_0 (q + 18#64) (l + 18446744073709551604#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v256_def
    subst v256_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr230
      bv_omega
    sym_close (hkE _ post241_0 (q + 19#64) (l + 18446744073709551603#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v284_def
    subst v284_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr258
      bv_omega
    sym_close (hkE _ post269_0 (q + 20#64) (l + 18446744073709551602#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v312_def
    subst v312_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr286
      bv_omega
    sym_close (hkE _ post297_0 (q + 21#64) (l + 18446744073709551601#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v340_def
    subst v340_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr314
      bv_omega
    sym_close (hkE _ post325_0 (q + 22#64) (l + 18446744073709551600#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v368_def
    subst v368_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr342
      bv_omega
    sym_close (hkE _ post353_0 (q + 23#64) (l + 18446744073709551599#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v396_def
    subst v396_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr370
      bv_omega
    sym_close (hkE _ post381_0 (q + 24#64) (l + 18446744073709551598#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v424_def
    subst v424_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr398
      bv_omega
    sym_close (hkE _ post409_0 (q + 25#64) (l + 18446744073709551597#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v452_def
    subst v452_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr426
      bv_omega
    sym_close (hkE _ post437_0 (q + 26#64) (l + 18446744073709551596#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v480_def
    subst v480_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr454
      bv_omega
    sym_close (hkE _ post465_0 (q + 27#64) (l + 18446744073709551595#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v508_def
    subst v508_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr482
      bv_omega
    sym_close (hkE _ post493_0 (q + 28#64) (l + 18446744073709551594#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v536_def
    subst v536_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr510
      bv_omega
    sym_close (hkE _ post521_0 (q + 29#64) (l + 18446744073709551593#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v564_def
    subst v564_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr538
      bv_omega
    sym_close (hkE _ post549_0 (q + 30#64) (l + 18446744073709551592#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v592_def
    subst v592_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr566
      bv_omega
    sym_close (hkE _ post577_0 (q + 31#64) (l + 18446744073709551591#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v620_def
    subst v620_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr594
      bv_omega
    sym_close (hkE _ post605_0 (q + 32#64) (l + 18446744073709551590#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v648_def
    subst v648_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr622
      bv_omega
    sym_close (hkE _ post633_0 (q + 33#64) (l + 18446744073709551589#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v676_def
    subst v676_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr650
      bv_omega
    sym_close (hkE _ post661_0 (q + 34#64) (l + 18446744073709551588#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v704_def
    subst v704_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr678
      bv_omega
    sym_close (hkE _ post689_0 (q + 35#64) (l + 18446744073709551587#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v732_def
    subst v732_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr706
      bv_omega
    sym_close (hkE _ post717_0 (q + 36#64) (l + 18446744073709551586#64))
  · rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v760_def
    subst v760_def
    have hlt : l.toNat < 32 := by
      simp only [beq_iff_eq] at hbr734
      bv_omega
    sym_close (hkE _ post745_0 (q + 37#64) (l + 18446744073709551585#64))
  · -- `Ok`
    have h32 : 32 ≤ l.toNat := by
      simp only [beq_iff_eq] at hbr18 hbr27 hbr35 hbr43 hbr51 hbr59 hbr67 hbr77 hbr93 hbr120 hbr147 hbr174 hbr202 hbr230 hbr258 hbr286 hbr314 hbr342 hbr370 hbr398 hbr426 hbr454 hbr482 hbr510 hbr538 hbr566 hbr594 hbr622 hbr650 hbr678 hbr706 hbr734
      bv_omega
    have hl : l + 18446744073709551584#64 = l - 32#64 := by bv_omega
    rw [hl] at hR1
    have e : [v803, v765, v781, v798, v799] = arr32W O W 6 := by
      subst v803_def v802_def v801_def v800_def v799_def v798_def v796_def v794_def v792_def v791_def v789_def v787_def v785_def v783_def v781_def v779_def v777_def v775_def v773_def v771_def v769_def v767_def v765_def v763_def v761_def v759_def v757_def v756_def v755_def v754_def v753_def v752_def v751_def v750_def v744_def v743_def v742_def v738_def v722_def v716_def v715_def v714_def v710_def v694_def v688_def v687_def v686_def v682_def v666_def v660_def v659_def v658_def v654_def v638_def v632_def v631_def v630_def v626_def v610_def v604_def v603_def v602_def v598_def v582_def v576_def v575_def v574_def v570_def v554_def v548_def v547_def v546_def v542_def v526_def v520_def v519_def v518_def v514_def v498_def v492_def v491_def v490_def v486_def v470_def v464_def v463_def v462_def v458_def v442_def v436_def v435_def v434_def v430_def v414_def v408_def v407_def v406_def v402_def v386_def v380_def v379_def v378_def v374_def v358_def v352_def v351_def v350_def v346_def v330_def v324_def v323_def v322_def v318_def v302_def v296_def v295_def v294_def v290_def v274_def v268_def v267_def v266_def v262_def v246_def v240_def v239_def v238_def v234_def v218_def v212_def v211_def v210_def v206_def v190_def v184_def v183_def v182_def v178_def v163_def v157_def v156_def v155_def v151_def v136_def v130_def v129_def v128_def v124_def v109_def v103_def v102_def v101_def v97_def v79_def v70_def v62_def v54_def v46_def v38_def v30_def v22_def
      simp only [arr32W, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      rotate_left 4
      · simp only [inByte, trunc8_zext]
      all_goals
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [word8, inByte, getLsbD_replaceByte _ _ _ _ hi, trunc8_zext]
        interval_cases i <;> simp [extractByte]
    rw [e] at hR0
    sym_close hk

/-- `Ok`: the reader has the 32 bytes. -/
theorem array32_r6_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801775c#64) (hcode : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x300 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha2 : s.getReg .x12 = 0x20#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2) (hl : 32 ≤ l.toNat)
    (hW : Region q W s) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x300#64) 96 out 5) (hdD : Disjoint (sp - 0x300#64) 96 de 2)
    (hdW : Disjoint (sp - 0x300#64) 96 q 5) (heD : Disjoint out 5 de 2)
    (heW : Disjoint out 5 q 5) (hfW : Disjoint de 2 q 5)
    (hhO : Disjoint 0x78040620#64 14780694332 out 5) (hhD : Disjoint 0x78040620#64 14780694332 de 2)
    (hhW : Disjoint 0x78040620#64 14780694332 q 5)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x300#64, 96), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (arr32W O W 6) t → extractByte (arr32W O W 6)[0]! 0 = 0#8 →
      Region de [q + 38#64, l - 32#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  array32_r6_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeN hcw hro hheap hra hra1 hsp hstk ha0 ha1 ha2
    hO hokO hD hokD hW hokW hdO hdD hdW heD heW hfW hhO hhD hhW hio
    (fun t h1 h2 h3 h4 h5 h6 _ hH => hk t h1 h2 h3 h4 h5 (arr32W_tag O W 6) h6 hH)
    (fun _ _ _ _ _ _ _ _ _ _ hlt _ => absurd hl (by omega))

/-- `Err`: fewer than 32 bytes left. -/
theorem array32_r6_err_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801775c#64) (hcode : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x300 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha2 : s.getReg .x12 = 0x20#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2) (hl : l.toNat < 32)
    (hW : Region q W s) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x300#64) 96 out 5) (hdD : Disjoint (sp - 0x300#64) 96 de 2)
    (hdW : Disjoint (sp - 0x300#64) 96 q 5) (heD : Disjoint out 5 de 2)
    (heW : Disjoint out 5 q 5) (hfW : Disjoint de 2 q 5)
    (hhO : Disjoint 0x78040620#64 14780694332 out 5) (hhD : Disjoint 0x78040620#64 14780694332 de 2)
    (hhW : Disjoint 0x78040620#64 14780694332 q 5)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x300#64, 96), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte O[0]! 0 1#8, e, O[2]!, O[3]!, O[4]!] t → Region de [d0, d1] t →
      Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  array32_r6_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeN hcw hro hheap hra hra1 hsp hstk ha0 ha1 ha2
    hO hokO hD hokD hW hokW hdO hdD hdW heD heW hfW hhO hhD hhW hio
    (fun _ _ _ _ _ _ _ h32 _ => absurd h32 (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hH)

end Cases.Zip2005
