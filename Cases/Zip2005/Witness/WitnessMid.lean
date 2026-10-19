import Cases.Zip2005.Witness.OptWrap
import Cases.Zip2005.Witness.NextU64
import Cases.Zip2005.Witness.NextU32
import Cases.Zip2005.Witness.NextArrBytes32
import Cases.Zip2005.Witness.BoolReader
import Cases.Zip2005.Witness.InvalidLength
import Cases.Zip2005.Runtime.Memcpy_d0s0_1010
import Cases.Zip2005.Witness.WitnessTail
import Cases.Zip2005.Witness.WitnessModel
import Cases.Zip2005.Witness.WitnessMid_NN
import Cases.Zip2005.Witness.WitnessMid_NS
import Cases.Zip2005.Witness.WitnessMid_SN
import Cases.Zip2005.Witness.WitnessMid_SS
import Cases.Zip2005.Witness.WitnessMid_E
import Cases.Zip2005.Witness.WitnessMid_NE
import Cases.Zip2005.Witness.WitnessMid_SE
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Zip2005Witness`'s visitor from `value` on (`0x78018a6c`)

The second part of the visitor (cut at `0x78018a6c`, after `sk` and the eight `Bytes32`, which
are in the frame and in callee-saved registers by then): `value`, `merkle_position`,
`auth_path`, `qk`, `sigma_qsk` and `negate` through the sequence access at `sp + 0x88`
(`[de, 6]`), then the tail (`Cases.Zip2005.witness_tail_spec`). The stream is at `qb + 1` over the
aligned words `W`; whatever the tag of `sk`, every later field sits at the same residue mod 8.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option machineChecked.sym.foldBytes true in
theorem witness_mid_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word)
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
    (hfmt : ∀ (u : MachineState) (sp' d : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fa4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78019fa4#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        S.length = 3 → Region d S t → Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
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
    (hk : ∀ (t : MachineState) (V : List Word), t.pc = vra &&& ~~~1#64 →
      t.code = s.code → t.getReg .x1 = vra → t.getReg .x2 = sp + 0xa70#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 →
      t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = vs6 → t.getReg .x23 = vs7 →
      t.getReg .x24 = vs8 → t.getReg .x25 = vs9 → t.getReg .x26 = vs10 → t.getReg .x27 = vs11 →
      Unchanged [(sp - 0x1120#64, 548), (sp, 334), (out, 174), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out V t → V.length = 174 →
      (extractByte V[173]! 7 = 2#8 ∨
        (V = midW (Fr1 ++ [de, c] ++ Fr2) r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V ∧
          midOkCond W l.toNat)) → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  -- the tags of `qk` and `sigma_qsk` (their words are fixed: the stream is at `qb + 1`)
  have hkOk := fun t V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hR hl hV hc =>
    hk t V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hR hl (Or.inr ⟨hV, hc⟩)
  have hkErr := fun t V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hR hl hE =>
    hk t V h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hR hl (Or.inl hE)
  rcases Nat.lt_or_ge (optTag5 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!]).toNat 2 with hq2 | hq2
  · rcases Nat.lt_or_ge (optTag5 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!]).toNat 1 with hq1 | hq1
    · rcases Nat.lt_or_ge (optTag6 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!]).toNat 2 with hs2 | hs2
      · rcases Nat.lt_or_ge (optTag6 [W[129]!, W[130]!, W[131]!, W[132]!, W[133]!]).toNat 1 with hs1 | hs1
        · exact witness_mid_NN_spec s sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra Fr1 Fr2 O W hF1l hF2l hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hheap hsp hstk hs0 hs5 hr9 hr18 hr19 hr20 hr22 hr23 hr24 hr25 hr26 hr27 hF1 hA hF2 hS hokF hc hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hFlo hhandle halloc hio hq1 hs1 hkOk hkErr
        · exact witness_mid_NS_spec s sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra Fr1 Fr2 O W hF1l hF2l hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hheap hsp hstk hs0 hs5 hr9 hr18 hr19 hr20 hr22 hr23 hr24 hr25 hr26 hr27 hF1 hA hF2 hS hokF hc hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hFlo hfmt hhandle halloc hio hq1 hs1 hs2 hkOk hkErr
      · exact witness_mid_NE_spec s sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra Fr1 Fr2 O W hF1l hF2l hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hheap hsp hstk hs0 hs5 hr9 hr18 hr19 hr20 hr22 hr23 hr24 hr25 hr26 hr27 hF1 hA hF2 hS hokF hc hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hFlo hhandle halloc hio hq1 hs2 hkErr
    · rcases Nat.lt_or_ge (optTag6 [W[133]!, W[134]!, W[135]!, W[136]!, W[137]!]).toNat 2 with hs2 | hs2
      · rcases Nat.lt_or_ge (optTag6 [W[133]!, W[134]!, W[135]!, W[136]!, W[137]!]).toNat 1 with hs1 | hs1
        · exact witness_mid_SN_spec s sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra Fr1 Fr2 O W hF1l hF2l hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hheap hsp hstk hs0 hs5 hr9 hr18 hr19 hr20 hr22 hr23 hr24 hr25 hr26 hr27 hF1 hA hF2 hS hokF hc hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hFlo hfmt hhandle halloc hio hq1 hq2 hs1 hkOk hkErr
        · exact witness_mid_SS_spec s sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra Fr1 Fr2 O W hF1l hF2l hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hheap hsp hstk hs0 hs5 hr9 hr18 hr19 hr20 hr22 hr23 hr24 hr25 hr26 hr27 hF1 hA hF2 hS hokF hc hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hFlo hfmt hhandle halloc hio hq1 hq2 hs1 hs2 hkOk hkErr
      · exact witness_mid_SE_spec s sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra Fr1 Fr2 O W hF1l hF2l hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hheap hsp hstk hs0 hs5 hr9 hr18 hr19 hr20 hr22 hr23 hr24 hr25 hr26 hr27 hF1 hA hF2 hS hokF hc hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hFlo hfmt hhandle halloc hio hq1 hq2 hs2 hkErr
  · exact witness_mid_E_spec s sp out de qb l c r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra Fr1 Fr2 O W hF1l hF2l hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcode64 hcode32 hcodeNA hcodeV hcodeE hcodeNO hcodeB hcodeIL hcw hro hheap hsp hstk hs0 hs5 hr9 hr18 hr19 hr20 hr22 hr23 hr24 hr25 hr26 hr27 hF1 hA hF2 hS hokF hc hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hFlo hhandle halloc hio hq2 hkErr

end Cases.Zip2005
