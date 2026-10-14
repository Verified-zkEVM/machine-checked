import Cases.Zip2005.Witness.OptWrap
import Cases.Zip2005.Witness.NextU64
import Cases.Zip2005.Witness.NextU32
import Cases.Zip2005.Witness.NextArrBytes32
import Cases.Zip2005.Witness.BoolReader
import Cases.Zip2005.Witness.InvalidLength
import Cases.Zip2005.Runtime.Memcpy_d0s0_1010
import Cases.Zip2005.Witness.WitnessTail
import Cases.Zip2005.Witness.WitnessModel
import Cases.Zip2005.Image.Ro

/-!
# `Zip2005Witness`'s visitor from `value` on (`0x78018a6c`)

The second part of the visitor (cut at `0x78018a6c`, after `sk` and the eight `Bytes32`, which
are in the frame and in callee-saved registers by then): `value`, `merkle_position`,
`auth_path`, `qk`, `sigma_qsk` and `negate` through the sequence access at `sp + 0x88`
(`[de, 6]`), then the tail (`Cases.Zip2005.witness_tail_spec`). This case: `qk` an invalid tag. The stream is at `qb + 1` over the
aligned words `W`; whatever the tag of `sk`, every later field sits at the same residue mod 8.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option asmverif.sym.foldBytes true in
theorem witness_mid_E_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word)
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
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1120 sp)
    (hs0 : s.getReg .x8 = out) (hs5 : s.getReg .x21 = sp + 0x9c4#64)
    (hr9 : s.getReg .x9 = r9) (hr18 : s.getReg .x18 = r18) (hr19 : s.getReg .x19 = r19) (hr20 : s.getReg .x20 = r20)
    (hr22 : s.getReg .x22 = r22) (hr23 : s.getReg .x23 = r23) (hr24 : s.getReg .x24 = r24) (hr25 : s.getReg .x25 = r25)
    (hr26 : s.getReg .x26 = r26) (hr27 : s.getReg .x27 = r27)
    (hF1 : Region sp Fr1 s) (hA : Region (sp + 0x88#64) [de, c] s) (hF2 : Region (sp + 0x98#64) Fr2 s)
    (hS : Region (sp + 0xa08#64) [vs11, vs10, vs9, vs8, vs7, vs6, vs5, vs4, vs3, vs2, vs1, vs0, vra] s)
    (hokF : RegionOk Ro.layout.textLo Ro.layout.textHi sp 334) (hc : c = 6#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 174)
    (hD : Region de [qb + 1#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region qb W s) (hq : 0x1c00000000 ≤ qb.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi qb 138)
    (hdO : Disjoint (sp - 0x1120#64) 882 out 174) (hdD : Disjoint (sp - 0x1120#64) 882 de 2)
    (heD : Disjoint out 174 de 2) (hOlo : out.toNat + 1392 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000) (hFlo : sp.toNat + 2672 ≤ 0x78000000)
    (hhandle : ∀ u : MachineState, u.pc = 0x7803d1a8#64 → u.code = s.code → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r' → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x18 ≤ 0x1c00000000 → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hqk : 2 ≤ (optTag5 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!]).toNat)
    (hkErr : ∀ (t : MachineState) (V : List Word), t.pc = vra &&& ~~~1#64 →
      t.code = s.code → t.getReg .x1 = vra → t.getReg .x2 = sp + 0xa70#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 →
      t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = vs6 → t.getReg .x23 = vs7 →
      t.getReg .x24 = vs8 → t.getReg .x25 = vs9 → t.getReg .x26 = vs10 → t.getReg .x27 = vs11 →
      Unchanged [(sp - 0x1120#64, 548), (sp, 334), (out, 174), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out V t → V.length = 174 → extractByte V[173]! 7 = 2#8 → SafeN G n P t) :
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
  have halloc0 := fun u sp' h1 h2 h3 => halloc u sp' 0x78018130#64 h1 h2 h3 (by decide)
  have halloc1 := fun u sp' h1 h2 h3 => halloc u sp' 0x78019e80#64 h1 h2 h3 (by decide)
  have halloc2 := fun u sp' h1 h2 h3 => halloc u sp' 0x78019fbc#64 h1 h2 h3 (by decide)
  subst hc
  rw [AsmVerif.RiscV.Sym.List.eq_map_range Fr1 hF1l] at hF1
  rw [AsmVerif.RiscV.Sym.List.eq_map_range Fr2 hF2l] at hF2
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [AsmVerif.RiscV.Sym.List.eq_map_range W hWl] at hW
  sym_exec [next_u64_ok_spec, next_u64_err_spec, next_u32_ok_spec, next_u32_err_spec,
    next_arr_bytes32_ok_spec, next_arr_bytes32_err_spec,
    nopt5_errtag_spec,
    bool_reader_ok_spec, bool_reader_eof_spec, bool_reader_badbyte_spec, invalid_length_spec,
    memcpy_d0s0_1010_spec, witness_tail_spec, hhandle, halloc0, halloc1, halloc2, hio] 3000
  all_goals sym_close hkErr
  all_goals (try simp only [List.length_cons, List.length_nil])
  all_goals (simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
             sym_unfold
             simp (disch := decide) only [byte_simp]
             try decide)

end Cases.Zip2005
