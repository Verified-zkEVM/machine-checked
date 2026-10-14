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
import Cases.Zip2005.Witness.WitnessMid
import Cases.Zip2005.Witness.WitnessVisitor_N
import Cases.Zip2005.Witness.WitnessVisitor_S
import Cases.Zip2005.Witness.WitnessVisitor_E
import Cases.Zip2005.Image.F_7801823c
import Cases.Zip2005.Image.Ro

/-!
# `Zip2005Witness`'s visitor (`visit_seq`, 0x7801823c)

The witness from the input at `q` (`WW`, 174 words, the reader at `q`): `sk: Option<Bytes32>`,
eight `Bytes32` (`alpha`, `ak`, `nk`, `rivk_ext`, `rivk`, `g_d`, `rho`, `rseed`), `value: u64`,
`merkle_position: u32`, `auth_path: [Bytes32; 32]`, `qk` and `sigma_qsk: Option<Bytes32>`, and
`negate: bool`, each through its reader's specification (the field count checked first), moved
through the frame into `Ok(witness)` (1392 bytes); the first `Err` is passed up (the niche 2 in
byte `0x56f`, the error at `out`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem witness_visitor_spec {P : Prop} (s : MachineState) (ra sp out de q l : Word)
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
    (hfmt : ∀ (u : MachineState) (sp' d : Word), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fa4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78019fa4#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        S.length = 3 → Region d S t → Safe P t) → Safe P u)
    (hhandle : ∀ u : MachineState, u.pc = 0x7803d1a8#64 → u.code = s.code → Safe P u)
    (halloc : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r' → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x18 ≤ 0x1c00000000 → Safe P t) → Safe P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Safe P t) → Safe P u)
    (hk : ∀ (t : MachineState) (V : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1b90#64, 882), (out, 174), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out V t → V.length = 174 →
      (extractByte V[173]! 7 = 2#8 ∨ (V = witW WW V ∧ witOkCond WW l.toNat)) → Safe P t) :
    Safe P s := by
  have hkOk := fun t V h1 h2 h3 h4 hR hl hV hc => hk t V h1 h2 h3 h4 hR hl (Or.inr ⟨hV, hc⟩)
  have hkErr := fun t V h1 h2 h3 h4 hR hl hE => hk t V h1 h2 h3 h4 hR hl (Or.inl hE)
  rcases Nat.lt_or_ge (optTag0 [WW[0]!, WW[1]!, WW[2]!, WW[3]!, WW[4]!]).toNat 2 with h2 | h2
  · rcases Nat.lt_or_ge (optTag0 [WW[0]!, WW[1]!, WW[2]!, WW[3]!, WW[4]!]).toNat 1 with h1 | h1
    · exact witness_visitor_N_spec s ra sp out de q l O WW hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hra hra1 hsp hstk ha0 ha1 ha5 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hfmt hhandle halloc hio h1 hkOk hkErr
    · exact witness_visitor_S_spec s ra sp out de q l O WW hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hra hra1 hsp hstk ha0 ha1 ha5 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hfmt hhandle halloc hio h1 h2 hkOk hkErr
  · exact witness_visitor_E_spec s ra sp out de q l O WW hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hra hra1 hsp hstk ha0 ha1 ha5 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio h2 hkErr

end Cases.Zip2005
