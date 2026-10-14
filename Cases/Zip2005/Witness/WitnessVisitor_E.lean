import Cases.Zip2005.Witness.OptWrap
import Cases.Zip2005.Witness.Array32R1
import Cases.Zip2005.Witness.NextU64
import Cases.Zip2005.Witness.NextU32
import Cases.Zip2005.Witness.NextArrBytes32
import Cases.Zip2005.Witness.BoolReader
import Cases.Zip2005.Witness.InvalidLength
import Cases.Zip2005.Runtime.Memcpy_d0s0_1010
import Cases.Zip2005.Witness.WitnessTail
import Cases.Zip2005.Witness.WitnessModel
import Cases.Zip2005.Image.F_7801823c
import Cases.Zip2005.Image.Ro

/-!
# `Zip2005Witness`'s visitor (`visit_seq`, 0x7801823c) — case E

The witness from the input at `q` (`WW`, 174 words, the reader at `q`): `sk: Option<Bytes32>`,
eight `Bytes32` (`alpha`, `ak`, `nk`, `rivk_ext`, `rivk`, `g_d`, `rho`, `rseed`), `value: u64`,
`merkle_position: u32`, `auth_path: [Bytes32; 32]`, `qk` and `sigma_qsk: Option<Bytes32>`, and
`negate: bool`, each through its reader's specification (the field count checked first), moved
through the frame into `Ok(witness)` (1392 bytes); the first `Err` is passed up (the niche 2 in
byte `0x56f`, the error at `out`).

This case: `sk` an invalid tag.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option asmverif.sym.foldBytes true in
theorem witness_visitor_E_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out de q l : Word)
    (O WW : List Word) (hOl : O.length = 174) (hWl : WW.length = 174)
    (hpc : s.pc = 0x7801823c#64) (hcode : CodeAt F_7801823c.base F_7801823c.prog s)
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
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1b90 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha5 : s.getReg .x15 = 15#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 174)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q WW s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 174)
    (hdO : Disjoint (sp - 0x1b90#64) 882 out 174) (hdD : Disjoint (sp - 0x1b90#64) 882 de 2)
    (heD : Disjoint out 174 de 2) (hOlo : out.toNat + 1392 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
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
    (hsk : 2 ≤ (optTag0 [WW[0]!, WW[1]!, WW[2]!, WW[3]!, WW[4]!]).toNat)
    (hkErr : ∀ (t : MachineState) (V : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1b90#64, 882), (out, 174), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out V t → V.length = 174 → extractByte V[173]! 7 = 2#8 → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1b90#64) 882 := hstk.frame 882 (by decide)
  have hu := Unchanged.refl [(sp - 0x1b90#64, 882), (out, 174), (de, 2),
    (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  have hokOr : RegionOk Ro.layout.roBase Ro.layout.textHi out 174 :=
    ⟨hokO.aligned, hokO.inMem, Or.inl (by simp only [Ro.layout_roBase]; omega)⟩
  have hmS : sp &&& 7#64 = 0#64 := by
    have ha := hstk.aligned
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    simp only [BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have halloc0 := fun u sp' h1 h2 h3 => halloc u sp' 0x78018130#64 h1 h2 h3 (by decide)
  have halloc1 := fun u sp' h1 h2 h3 => halloc u sp' 0x78019e80#64 h1 h2 h3 (by decide)
  have halloc2 := fun u sp' h1 h2 h3 => halloc u sp' 0x78019fbc#64 h1 h2 h3 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa70#64) 334 := hokS.sub' 548 334 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0xa70#64) 334 s
  rw [AsmVerif.RiscV.Sym.List.eq_map_range F0 hF0l] at hF0
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [AsmVerif.RiscV.Sym.List.eq_map_range WW hWl] at hW
  sym_exec [opt0_errtag_spec, invalid_length_spec, hhandle, halloc0, halloc1, halloc2, hio] 4000
  all_goals (sym_close hkErr
             all_goals (try simp only [List.length_cons, List.length_nil])
             all_goals (simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
                        sym_unfold
                        simp (disch := decide) only [byte_simp]
                        try decide))

end Cases.Zip2005
