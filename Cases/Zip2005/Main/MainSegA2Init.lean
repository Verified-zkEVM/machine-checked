import Cases.Zip2005.Orchard.CommitIvk
import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Orchard.DeriveUnchecked
import Cases.Zip2005.Curve.EpMulFq
import Cases.Zip2005.Orchard.ExtractP
import Cases.Zip2005.Orchard.ExtractedNoteCommitment
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Curve.FromBytesUnchecked
import Cases.Zip2005.Kit.CellsGlue
import Cases.Zip2005.Main.MainTags
import Cases.Zip2005.Main.MainWrap
import Cases.Zip2005.Runtime.Memcmp
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.Memcpy_d0s0_113
import Cases.Zip2005.Runtime.Memcpy_d0s0_1383
import Cases.Zip2005.Runtime.Memcpy_d7s0_113
import Cases.Zip2005.Orchard.NonZeroScalar
import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Orchard.NullifierDerive
import Cases.Zip2005.Witness.ParseAlpha
import Cases.Zip2005.Witness.ParseGd
import Cases.Zip2005.Witness.ParseKeys
import Cases.Zip2005.Witness.ParseMerklePath
import Cases.Zip2005.Witness.ParseRho
import Cases.Zip2005.Witness.ParseRk
import Cases.Zip2005.Orchard.Psi
import Cases.Zip2005.Orchard.Randomize
import Cases.Zip2005.Orchard.Rcm
import Cases.Zip2005.Orchard.Rivk
import Cases.Zip2005.Orchard.SpendValidatingKey
import Cases.Zip2005.Orchard.SpendingKeyFrom
import Cases.Zip2005.Curve.ToBytes
import Cases.Zip2005.Witness.WitnessVisitor
import Cases.Zip2005.Image.F_78019ff4
import Cases.Zip2005.Main.MainSegKit
import Cases.Zip2005.Main.MainSegA2
import Cases.Zip2005.Image.Ro

/-!
# `main`, segment A2, with the lazy `FP_TABLES` build

`main_seg_a2_spec` takes the tables at entry; the real run reaches `0x7801a258` before
they exist. This applies the build contract `hinit` (`docs/ASSUMPTIONS.md`, `A3`) first.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
/-- Segment A2 from a state where `FP_TABLES` may not be built yet: `hinit` (assumption `A3`)
    supplies them, and nothing else changes (the build writes only the heap). -/
theorem main_seg_a2i_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState) (sp vs0 vs1 vs2 vs3 vs4 vs5 vra r22 r23 r24 r25 r26 r27 : Word)
    (f0 f1 f2 f3 kr0 kr1 kr2 kr3 kb0 kb1 kb2 kb3 nb0 nb1 nb2 nb3 xb0 xb1 xb2 xb3 ib0 ib1 ib2 ib3 gb0 gb1 gb2 gb3 rb0 rb1 rb2 rb3 sd0 sd1 sd2 sd3 vv pw al0 al1 al2 al3 ng t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : Word) (H Y D X A O13 Iv Gp Kp Rc Sc Ps Rm Gb Pb F16 F8 Ri Iv4 Wf Nk Re Rv Ak R16 Q4 : List Word)
    (hHl : H.length = 128) (hYl : Y.length = 117) (hDl : D.length = 12) (hXl : X.length = 4) (hAl : A.length = 4) (hO13l : O13.length = 13) (hIvl : Iv.length = 4) (hGpl : Gp.length = 12) (hKpl : Kp.length = 12) (hRcl : Rc.length = 4) (hScl : Sc.length = 4) (hPsl : Ps.length = 4) (hRml : Rm.length = 4) (hGbl : Gb.length = 4) (hPbl : Pb.length = 4) (hF16l : F16.length = 16) (hF8l : F8.length = 8) (hRil : Ri.length = 4) (hIv4l : Iv4.length = 4) (hWfl : Wf.length = 16) (hNkl : Nk.length = 4) (hRel : Re.length = 4) (hRvl : Rv.length = 4) (hAkl : Ak.length = 4) (hR16l : R16.length = 16) (hQ4l : Q4.length = 4)
    (hpc : s.pc = 0x7801a258#64)
    (hc_78016938 : CodeAt F_78016938.base F_78016938.prog s)
    (hc_7801775c : CodeAt F_7801775c.base F_7801775c.prog s)
    (hc_7801806c : CodeAt F_7801806c.base F_7801806c.prog s)
    (hc_7801823c : CodeAt F_7801823c.base F_7801823c.prog s)
    (hc_780191c4 : CodeAt F_780191c4.base F_780191c4.prog s)
    (hc_780197cc : CodeAt F_780197cc.base F_780197cc.prog s)
    (hc_78019918 : CodeAt F_78019918.base F_78019918.prog s)
    (hc_78019a10 : CodeAt F_78019a10.base F_78019a10.prog s)
    (hc_78019b50 : CodeAt F_78019b50.base F_78019b50.prog s)
    (hc_78019bf0 : CodeAt F_78019bf0.base F_78019bf0.prog s)
    (hc_78019cb8 : CodeAt F_78019cb8.base F_78019cb8.prog s)
    (hc_78019dd8 : CodeAt F_78019dd8.base F_78019dd8.prog s)
    (hc_78019f50 : CodeAt F_78019f50.base F_78019f50.prog s)
    (hc_78019ff4 : CodeAt F_78019ff4.base F_78019ff4.prog s)
    (hc_7801aed0 : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hc_7801b4d8 : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hc_7801beb0 : CodeAt F_7801beb0.base F_7801beb0.prog s)
    (hc_7801bf3c : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hc_7801bf4c : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hc_7801bf5c : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hc_7801cb44 : CodeAt F_7801cb44.base F_7801cb44.prog s)
    (hc_7801ce6c : CodeAt F_7801ce6c.base F_7801ce6c.prog s)
    (hc_7801ce90 : CodeAt F_7801ce90.base F_7801ce90.prog s)
    (hc_7801d074 : CodeAt F_7801d074.base F_7801d074.prog s)
    (hc_7801d098 : CodeAt F_7801d098.base F_7801d098.prog s)
    (hc_7801d2c8 : CodeAt F_7801d2c8.base F_7801d2c8.prog s)
    (hc_7801d2ec : CodeAt F_7801d2ec.base F_7801d2ec.prog s)
    (hc_7801d360 : CodeAt F_7801d360.base F_7801d360.prog s)
    (hc_7801d3d4 : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    (hc_7801d51c : CodeAt F_7801d51c.base F_7801d51c.prog s)
    (hc_7801d92c : CodeAt F_7801d92c.base F_7801d92c.prog s)
    (hc_7801ddd8 : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    (hc_7801e26c : CodeAt F_7801e26c.base F_7801e26c.prog s)
    (hc_7801e704 : CodeAt F_7801e704.base F_7801e704.prog s)
    (hc_7801ed68 : CodeAt F_7801ed68.base F_7801ed68.prog s)
    (hc_7801f120 : CodeAt F_7801f120.base F_7801f120.prog s)
    (hc_7801f5a4 : CodeAt F_7801f5a4.base F_7801f5a4.prog s)
    (hc_7801f780 : CodeAt F_7801f780.base F_7801f780.prog s)
    (hc_7801fb1c : CodeAt F_7801fb1c.base F_7801fb1c.prog s)
    (hc_7801fbcc : CodeAt F_7801fbcc.base F_7801fbcc.prog s)
    (hc_7802018c : CodeAt F_7802018c.base F_7802018c.prog s)
    (hc_780203dc : CodeAt F_780203dc.base F_780203dc.prog s)
    (hc_78020548 : CodeAt F_78020548.base F_78020548.prog s)
    (hc_780207e8 : CodeAt F_780207e8.base F_780207e8.prog s)
    (hc_78020ca0 : CodeAt F_78020ca0.base F_78020ca0.prog s)
    (hc_78020d50 : CodeAt F_78020d50.base F_78020d50.prog s)
    (hc_78021238 : CodeAt F_78021238.base F_78021238.prog s)
    (hc_7802233c : CodeAt F_7802233c.base F_7802233c.prog s)
    (hc_78022514 : CodeAt F_78022514.base F_78022514.prog s)
    (hc_780227b4 : CodeAt F_780227b4.base F_780227b4.prog s)
    (hc_78022848 : CodeAt F_78022848.base F_78022848.prog s)
    (hc_78022a74 : CodeAt F_78022a74.base F_78022a74.prog s)
    (hc_78022ca0 : CodeAt F_78022ca0.base F_78022ca0.prog s)
    (hc_78022f5c : CodeAt F_78022f5c.base F_78022f5c.prog s)
    (hc_780231e8 : CodeAt F_780231e8.base F_780231e8.prog s)
    (hc_78023230 : CodeAt F_78023230.base F_78023230.prog s)
    (hc_78023278 : CodeAt F_78023278.base F_78023278.prog s)
    (hc_780232f4 : CodeAt F_780232f4.base F_780232f4.prog s)
    (hc_78023308 : CodeAt F_78023308.base F_78023308.prog s)
    (hc_7802340c : CodeAt F_7802340c.base F_7802340c.prog s)
    (hc_780234cc : CodeAt F_780234cc.base F_780234cc.prog s)
    (hc_78023544 : CodeAt F_78023544.base F_78023544.prog s)
    (hc_78023594 : CodeAt F_78023594.base F_78023594.prog s)
    (hc_780235e8 : CodeAt F_780235e8.base F_780235e8.prog s)
    (hc_780237dc : CodeAt F_780237dc.base F_780237dc.prog s)
    (hc_78023864 : CodeAt F_78023864.base F_78023864.prog s)
    (hc_780239bc : CodeAt F_780239bc.base F_780239bc.prog s)
    (hc_78023a18 : CodeAt F_78023a18.base F_78023a18.prog s)
    (hc_78023d7c : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hc_78023ec4 : CodeAt F_78023ec4.base F_78023ec4.prog s)
    (hc_78023f64 : CodeAt F_78023f64.base F_78023f64.prog s)
    (hc_7802413c : CodeAt F_7802413c.base F_7802413c.prog s)
    (hc_78025164 : CodeAt F_78025164.base F_78025164.prog s)
    (hc_78025654 : CodeAt F_78025654.base F_78025654.prog s)
    (hc_78025854 : CodeAt F_78025854.base F_78025854.prog s)
    (hc_78025a1c : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hc_78026258 : CodeAt F_78026258.base F_78026258.prog s)
    (hc_78026878 : CodeAt F_78026878.base F_78026878.prog s)
    (hc_78026928 : CodeAt F_78026928.base F_78026928.prog s)
    (hc_78026b44 : CodeAt F_78026b44.base F_78026b44.prog s)
    (hc_7802827c : CodeAt F_7802827c.base F_7802827c.prog s)
    (hc_78028298 : CodeAt F_78028298.base F_78028298.prog s)
    (hc_78028718 : CodeAt F_78028718.base F_78028718.prog s)
    (hc_78028b34 : CodeAt F_78028b34.base F_78028b34.prog s)
    (hc_78028ce8 : CodeAt F_78028ce8.base F_78028ce8.prog s)
    (hc_78028d04 : CodeAt F_78028d04.base F_78028d04.prog s)
    (hc_78029468 : CodeAt F_78029468.base F_78029468.prog s)
    (hc_780297c0 : CodeAt F_780297c0.base F_780297c0.prog s)
    (hc_78029ae8 : CodeAt F_78029ae8.base F_78029ae8.prog s)
    (hc_78029b18 : CodeAt F_78029b18.base F_78029b18.prog s)
    (hc_78029b64 : CodeAt F_78029b64.base F_78029b64.prog s)
    (hc_78029d94 : CodeAt F_78029d94.base F_78029d94.prog s)
    (hc_7802e2b4 : CodeAt F_7802e2b4.base F_7802e2b4.prog s)
    (hc_7802e5b4 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hc_7802e8ec : CodeAt F_7802e8ec.base F_7802e8ec.prog s)
    (hc_7802e9b8 : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hc_7802ed10 : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hc_7802f038 : CodeAt F_7802f038.base F_7802f038.prog s)
    (hc_7802f358 : CodeAt F_7802f358.base F_7802f358.prog s)
    (hc_780315c0 : CodeAt F_780315c0.base F_780315c0.prog s)
    (hc_78031be8 : CodeAt F_78031be8.base F_78031be8.prog s)
    (hc_78032c1c : CodeAt F_78032c1c.base F_78032c1c.prog s)
    (hc_78032db4 : CodeAt F_78032db4.base F_78032db4.prog s)
    (hc_78032fa4 : CodeAt F_78032fa4.base F_78032fa4.prog s)
    (hc_78033260 : CodeAt F_78033260.base F_78033260.prog s)
    (hc_78035f88 : CodeAt F_78035f88.base F_78035f88.prog s)
    (hc_78035fe0 : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hc_780360c8 : CodeAt F_780360c8.base F_780360c8.prog s)
    (hc_780360e0 : CodeAt F_780360e0.base F_780360e0.prog s)
    (hc_7803a0fc : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hc_7803a110 : CodeAt F_7803a110.base F_7803a110.prog s)
    (hc_7803dd28 : CodeAt F_7803dd28.base F_7803dd28.prog s)
    (hc_7803f54c : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hc_7803f57c : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1f60 sp)
    (hx10 : s.getReg .x10 = sp + 0xaf8#64)
    (hx11 : s.getReg .x11 = sp + 0x4a8#64)
    (hx12 : s.getReg .x12 = 0x20#64)
    (hx18 : s.getReg .x18 = sp + 0x798#64)
    (hx19 : s.getReg .x19 = sp + 0x1067#64)
    (hx20 : s.getReg .x20 = ng)
    (hr22 : s.getReg .x22 = r22)
    (hr23 : s.getReg .x23 = r23)
    (hr24 : s.getReg .x24 = r24)
    (hr25 : s.getReg .x25 = r25)
    (hr26 : s.getReg .x26 = r26)
    (hr27 : s.getReg .x27 = r27)
    (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi sp 532)
    (hSv : Region (sp + 0x1068#64) [vs5, vs4, vs3, vs2, vs1, vs0, vra] s)
    (hRkI : Region (sp + 0x28#64) [kr0, kr1, kr2, kr3] s)
    (hNf : Region (sp + 0x48#64) [f0, f1, f2, f3] s)
    (hH : Region (sp + 0x88#64) H s)
    (hAkB : Region (sp + 0x4a8#64) [kb0, kb1, kb2, kb3] s)
    (hNkB : Region (sp + 0x4c8#64) [nb0, nb1, nb2, nb3] s)
    (hRextB : Region (sp + 0x4e8#64) [xb0, xb1, xb2, xb3] s)
    (hRivkB : Region (sp + 0x508#64) [ib0, ib1, ib2, ib3] s)
    (hGdB : Region (sp + 0x528#64) [gb0, gb1, gb2, gb3] s)
    (hRhoB : Region (sp + 0x548#64) [rb0, rb1, rb2, rb3] s)
    (hSeed : Region (sp + 0x568#64) [sd0, sd1, sd2, sd3] s)
    (hVal : Region (sp + 0x588#64) [vv] s)
    (hPw : Region (sp + 0x590#64) [pw] s)
    (hT12 : Region (sp + 0x598#64) [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] s)
    (hAlpha : Region (sp + 0x5f8#64) [al0, al1, al2, al3] s)
    (hW : Region (sp + 0x618#64) Wf s)
    (hNk : Region (sp + 0x698#64) Nk s)
    (hRext : Region (sp + 0x6b8#64) Re s)
    (hRk : Region (sp + 0x6d8#64) Rv s)
    (hR16 : Region (sp + 0x6f8#64) R16 s)
    (hAk : Region (sp + 0x778#64) Ak s)
    (hQ4 : Region (sp + 0x798#64) Q4 s)
    (hF16 : Region (sp + 0x7b8#64) F16 s)
    (hF8 : Region (sp + 0x838#64) F8 s)
    (hRi : Region (sp + 0x878#64) Ri s)
    (hIv4 : Region (sp + 0x898#64) Iv4 s)
    (hIv : Region (sp + 0x8b8#64) Iv s)
    (hGp : Region (sp + 0x8d8#64) Gp s)
    (hKp : Region (sp + 0x938#64) Kp s)
    (hRc : Region (sp + 0x998#64) Rc s)
    (hSc : Region (sp + 0x9b8#64) Sc s)
    (hPs : Region (sp + 0x9d8#64) Ps s)
    (hRm : Region (sp + 0x9f8#64) Rm s)
    (hD : Region (sp + 0xa18#64) D s)
    (hGb : Region (sp + 0xa78#64) Gb s)
    (hPb : Region (sp + 0xa98#64) Pb s)
    (hA : Region (sp + 0xab8#64) A s)
    (hX : Region (sp + 0xad8#64) X s)
    (hO13 : Region (sp + 0xaf8#64) O13 s)
    (hY : Region (sp + 0xb60#64) Y s)
    -- `A3`: the first decompression builds `FP_TABLES` (lazily, through `Once`): the call
    -- behaves as the same call from a state that differs only in the heap and holds the tables
    (hinit : ∀ u : MachineState, u.pc = 0x7801a258#64 → u.code = s.code →
      (∀ t : MachineState, t.pc = u.pc → t.code = u.code → (∀ r : Reg, t.getReg r = u.getReg r) →
        Unchanged [(0x78040620#64, 4162), (0x780488a8#64, 10), (0x78048980#64, 14780690128)] u t →
        ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
        IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
        RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 →
        RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 →
        RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 →
        RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 →
        RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
        ilen.toNat ≤ 1104 →
        0x78048980 ≤ iptr.toNat →
        0x78048980 ≤ tg0.toNat →
        0x78048980 ≤ tg1.toNat →
        0x78048980 ≤ tg2.toNat →
        0x78048980 ≤ tg3.toNat →
        iptr.toNat + 8 * 138 ≤ 0x1c00000000 →
        tg0.toNat + 8 * 1024 ≤ 0x1c00000000 →
        tg1.toNat + 8 * 1024 ≤ 0x1c00000000 →
        tg2.toNat + 8 * 1024 ≤ 0x1c00000000 →
        tg3.toNat + 8 * 516 ≤ 0x1c00000000 →
        SafeN G nb P t) → SafeN G nb P u)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN G nb P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → SafeN G nb P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = s.code → SafeN G nb P u)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G nb P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN G nb P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → SafeN G nb P u)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G nb P u)
    (hunwrap_opt : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = s.code → SafeN G nb P u)
    (hpaf_nf : ∀ u : MachineState, u.pc = 0x78019da0#64 → u.code = s.code → SafeN G nb P u)
    (hconst : ∀ (u : MachineState) (sp' a0' : Word) (O1 O2 O3 : List Word),
      O1.length = 3 → O2.length = 36 → O3.length = 36 →
      u.pc = 0x78023cbc#64 → u.code = s.code → u.getReg .x1 = 0x7802084c#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x60 sp' → u.getReg .x10 = a0' →
      Region a0' O1 u → Region (a0' + 0x18#64) O2 u → Region (a0' + 0x138#64) O3 u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 75 → Disjoint (sp' - 0x60#64) 12 a0' 75 →
      RoImage Ro.layout u → Disjoint 0x78040620#64 14780694332 a0' 75 →
      (∀ t, t.pc = 0x7802084c#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x60#64, 12), (a0', 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        ∀ (ptr : Word) (MI : List Word), MI.length = 36 →
        Region a0' [64#64, ptr, 64#64] t → Region (a0' + 0x18#64) Poseidon.mdsWords t →
        Region (a0' + 0x138#64) MI t →
        Region ptr Poseidon.rcWords t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 768 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc_nf : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 → u.getReg .x12 = 8#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → SafeN G nb P t) → SafeN G nb P u)
    (halloc_mp : ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x80#64 →
      u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x80 ≤ 0x1c00000000 → SafeN G nb P t) → SafeN G nb P u)
    (hreserve : ∀ (u : MachineState) (sp' hdr ptr : Word) (n : Nat) (B : List Word),
      u.pc = 0x7801cac0#64 → u.code = s.code → u.getReg .x1 = 0x7801d1e8#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x100 sp' → u.getReg .x10 = hdr → u.getReg .x11 = BitVec.ofNat 64 n →
      Region hdr [BitVec.ofNat 64 n, ptr, BitVec.ofNat 64 n] u → RegionOk Ro.layout.roBase Ro.layout.textHi hdr 3 →
      Disjoint (sp' - 0x100#64) 32 hdr 3 → Disjoint 0x78040620#64 14780694332 hdr 3 → 4 ≤ n → n ≤ 16 →
      B.length = 4 * n → Region ptr B u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 32 * n ≤ 0x1c00000000 →
      (∀ (t : MachineState) (ptr' : Word) (B' : List Word), t.pc = 0x7801d1e8#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x100#64, 32), (hdr, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region hdr [BitVec.ofNat 64 (2 * n), ptr', BitVec.ofNat 64 n] t → B'.length = 4 * n →
        Region ptr' (B ++ B') t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr' (8 * n) → 0x78048980 ≤ ptr'.toNat →
        ptr'.toNat + 64 * n ≤ 0x1c00000000 → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc : ∀ (u : MachineState) (sp' r ptr sz : Word), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 8#64 → 0x78048980 ≤ ptr.toNat →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc_cm : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → SafeN G nb P t) → SafeN G nb P u)
    (hfrom_nc : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (g0 g1 g2 g3 p0 p1 p2 p3 v r0 r1 r2 r3 q0 q1 q2 q3 : Word), O1.length = 3 →
      u.pc = 0x7801dfb4#64 → u.code = s.code → u.getReg .x1 = 0x78020dc4#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterW sp0 J0) u →
      Region (a1' + 0x88#64) [0#64] u →
      Region (sp0 - 0xb50#64 + 0xa80#64) ([g0, g1, g2, g3, p0, p1, p2, p3, v] ++
        reprW [r0, r1, r2, r3] ++ reprW [q0, q1, q2, q3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 18 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 18 →
      Disjoint a0' 3 a1' 18 →
      StackOk Ro.layout 0xb50 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xb50#64 + 0xa80#64) 17 → Disjoint a0' 3 (sp0 - 0xb50#64 + 0xa80#64) 17 → Disjoint a1' 18 (sp0 - 0xb50#64 + 0xa80#64) 17 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 18 →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x78020dc4#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 18 → Region a0' [cap, ptr, 1090#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 137 →
        (∀ o, o < 1090 → byteAt Bv o = bw (noteBit [g0, g1, g2, g3] [p0, p1, p2, p3] v
          (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 137 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → SafeN G nb P t) → SafeN G nb P u)

    (hdealloc_ivk : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word), C.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780215d8#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G nb P t) → SafeN G nb P u)
    (hfrom_ivk : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (a0 a1 a2 a3 n0 n1 n2 n3 : Word), O1.length = 3 →
      u.pc = 0x7801e110#64 → u.code = s.code → u.getReg .x1 = 0x780212ac#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterIvkW sp0 J0) u →
      Region (a1' + 0x58#64) [0#64] u →
      Region (sp0 - 0xaa0#64 + 0x9c8#64) (ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 12 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 12 →
      Disjoint a0' 3 a1' 12 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 8 * 138 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 8 * 516 ≤ 0x1c00000000 →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      StackOk Ro.layout 0xaa0 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a0' 3 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a1' 12 (sp0 - 0xaa0#64 + 0x9c8#64) 8 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 12 →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x780212ac#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 12 → Region a0' [cap, ptr, 510#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 65 →
        (∀ o, o < 510 → byteAt Bv o = bw (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G nb P t) → SafeN G nb P u)
    (hk : ∀ t : MachineState, t.pc = vra &&& ~~~1#64 → t.code = s.code →
      t.getReg .x1 = vra → t.getReg .x2 = sp + 0x10a0#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 →
      t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = r22 → t.getReg .x23 = r23 → t.getReg .x24 = r24 → t.getReg .x25 = r25 → t.getReg .x26 = r26 → t.getReg .x27 = r27 →
      Unchanged [(sp - 0x1f60#64, 1536), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000), (0x78040620#64, 4162), (0x780488a8#64, 10), (0x78048980#64, 14780690128)] s t →
      t.getReg .x10 = 0#64 →
      -- the accepting path's checks over the words this segment reads (`GuestW`), and the dispatch's tags
      Cases.Zip2005.Top.GuestW [kr0, kr1, kr2, kr3] [f0, f1, f2, f3] [kb0, kb1, kb2, kb3] [nb0, nb1, nb2, nb3]
        [xb0, xb1, xb2, xb3] [ib0, ib1, ib2, ib3] [gb0, gb1, gb2, gb3] [rb0, rb1, rb2, rb3] [sd0, sd1, sd2, sd3]
        [al0, al1, al2, al3] (skWord pw t0) (skWord t0 t1) (skWord t1 t2) (skWord t2 t3) (ng &&& 1#64) vv →
      extractByte t3 5 = 0#8 → extractByte t7 6 = 0#8 → extractByte pw 4 ≠ 0#8 → SafeN G nb P t) :
    SafeN G nb P s := by
  have hspHi : sp.toNat + 0x10a0 ≤ 0x78000000 := by
    have h3 := hokF.offCode; have h4 := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)); simp only [Ro.layout_textHi, Ro.layout_roBase] at h3; omega
  have hHeap := frame_disj_heap hspHi
  refine hinit s hpc rfl (fun t htpc htc hregs hunch tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx IV G0 G1 G2 G3 hIVl hG0l hG1l hG2l hG3l hTB hIVr hG0 hG1 hG2 hG3 hok_iptr hok_g0 hok_g1 hok_g2 hok_g3 hilen hlo_iptr hlo_g0 hlo_g1 hlo_g2 hlo_g3 hhi_iptr hhi_g0 hhi_g1 hhi_g2 hhi_g3 => ?_)
  exact main_seg_a2_spec (G := G) (nb := nb) (P := P) t sp vs0 vs1 vs2 vs3 vs4 vs5 vra r22 r23 r24 r25 r26 r27 f0 f1 f2
    f3 kr0 kr1 kr2 kr3 kb0 kb1 kb2 kb3 nb0 nb1 nb2 nb3 xb0 xb1 xb2 xb3 ib0 ib1 ib2 ib3 gb0 gb1 gb2
    gb3 rb0 rb1 rb2 rb3 sd0 sd1 sd2 sd3 vv pw al0 al1 al2 al3 ng t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10
    t11 tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx H Y D X A O13 Iv Gp Kp Rc Sc Ps Rm Gb Pb F16 F8 Ri
    Iv4 Wf Nk Re Rv Ak R16 Q4 IV G0 G1 G2 G3 hHl hYl hDl hXl hAl hO13l hIvl hGpl hKpl hRcl hScl hPsl
    hRml hGbl hPbl hF16l hF8l hRil hIv4l hWfl hNkl hRel hRvl hAkl hR16l hQ4l hIVl hG0l hG1l hG2l
    hG3l (htpc.trans hpc) (codeAt_of_code_eq htc hc_78016938) (codeAt_of_code_eq htc hc_7801775c)
    (codeAt_of_code_eq htc hc_7801806c) (codeAt_of_code_eq htc hc_7801823c)
    (codeAt_of_code_eq htc hc_780191c4) (codeAt_of_code_eq htc hc_780197cc)
    (codeAt_of_code_eq htc hc_78019918) (codeAt_of_code_eq htc hc_78019a10)
    (codeAt_of_code_eq htc hc_78019b50) (codeAt_of_code_eq htc hc_78019bf0)
    (codeAt_of_code_eq htc hc_78019cb8) (codeAt_of_code_eq htc hc_78019dd8)
    (codeAt_of_code_eq htc hc_78019f50) (codeAt_of_code_eq htc hc_78019ff4)
    (codeAt_of_code_eq htc hc_7801aed0) (codeAt_of_code_eq htc hc_7801b4d8)
    (codeAt_of_code_eq htc hc_7801beb0) (codeAt_of_code_eq htc hc_7801bf3c)
    (codeAt_of_code_eq htc hc_7801bf4c) (codeAt_of_code_eq htc hc_7801bf5c)
    (codeAt_of_code_eq htc hc_7801cb44) (codeAt_of_code_eq htc hc_7801ce6c)
    (codeAt_of_code_eq htc hc_7801ce90) (codeAt_of_code_eq htc hc_7801d074)
    (codeAt_of_code_eq htc hc_7801d098) (codeAt_of_code_eq htc hc_7801d2c8)
    (codeAt_of_code_eq htc hc_7801d2ec) (codeAt_of_code_eq htc hc_7801d360)
    (codeAt_of_code_eq htc hc_7801d3d4) (codeAt_of_code_eq htc hc_7801d51c)
    (codeAt_of_code_eq htc hc_7801d92c) (codeAt_of_code_eq htc hc_7801ddd8)
    (codeAt_of_code_eq htc hc_7801e26c) (codeAt_of_code_eq htc hc_7801e704)
    (codeAt_of_code_eq htc hc_7801ed68) (codeAt_of_code_eq htc hc_7801f120)
    (codeAt_of_code_eq htc hc_7801f5a4) (codeAt_of_code_eq htc hc_7801f780)
    (codeAt_of_code_eq htc hc_7801fb1c) (codeAt_of_code_eq htc hc_7801fbcc)
    (codeAt_of_code_eq htc hc_7802018c) (codeAt_of_code_eq htc hc_780203dc)
    (codeAt_of_code_eq htc hc_78020548) (codeAt_of_code_eq htc hc_780207e8)
    (codeAt_of_code_eq htc hc_78020ca0) (codeAt_of_code_eq htc hc_78020d50)
    (codeAt_of_code_eq htc hc_78021238) (codeAt_of_code_eq htc hc_7802233c)
    (codeAt_of_code_eq htc hc_78022514) (codeAt_of_code_eq htc hc_780227b4)
    (codeAt_of_code_eq htc hc_78022848) (codeAt_of_code_eq htc hc_78022a74)
    (codeAt_of_code_eq htc hc_78022ca0) (codeAt_of_code_eq htc hc_78022f5c)
    (codeAt_of_code_eq htc hc_780231e8) (codeAt_of_code_eq htc hc_78023230)
    (codeAt_of_code_eq htc hc_78023278) (codeAt_of_code_eq htc hc_780232f4)
    (codeAt_of_code_eq htc hc_78023308) (codeAt_of_code_eq htc hc_7802340c)
    (codeAt_of_code_eq htc hc_780234cc) (codeAt_of_code_eq htc hc_78023544)
    (codeAt_of_code_eq htc hc_78023594) (codeAt_of_code_eq htc hc_780235e8)
    (codeAt_of_code_eq htc hc_780237dc) (codeAt_of_code_eq htc hc_78023864)
    (codeAt_of_code_eq htc hc_780239bc) (codeAt_of_code_eq htc hc_78023a18)
    (codeAt_of_code_eq htc hc_78023d7c) (codeAt_of_code_eq htc hc_78023ec4)
    (codeAt_of_code_eq htc hc_78023f64) (codeAt_of_code_eq htc hc_7802413c)
    (codeAt_of_code_eq htc hc_78025164) (codeAt_of_code_eq htc hc_78025654)
    (codeAt_of_code_eq htc hc_78025854) (codeAt_of_code_eq htc hc_78025a1c)
    (codeAt_of_code_eq htc hc_78026258) (codeAt_of_code_eq htc hc_78026878)
    (codeAt_of_code_eq htc hc_78026928) (codeAt_of_code_eq htc hc_78026b44)
    (codeAt_of_code_eq htc hc_7802827c) (codeAt_of_code_eq htc hc_78028298)
    (codeAt_of_code_eq htc hc_78028718) (codeAt_of_code_eq htc hc_78028b34)
    (codeAt_of_code_eq htc hc_78028ce8) (codeAt_of_code_eq htc hc_78028d04)
    (codeAt_of_code_eq htc hc_78029468) (codeAt_of_code_eq htc hc_780297c0)
    (codeAt_of_code_eq htc hc_78029ae8) (codeAt_of_code_eq htc hc_78029b18)
    (codeAt_of_code_eq htc hc_78029b64) (codeAt_of_code_eq htc hc_78029d94)
    (codeAt_of_code_eq htc hc_7802e2b4) (codeAt_of_code_eq htc hc_7802e5b4)
    (codeAt_of_code_eq htc hc_7802e8ec) (codeAt_of_code_eq htc hc_7802e9b8)
    (codeAt_of_code_eq htc hc_7802ed10) (codeAt_of_code_eq htc hc_7802f038)
    (codeAt_of_code_eq htc hc_7802f358) (codeAt_of_code_eq htc hc_780315c0)
    (codeAt_of_code_eq htc hc_78031be8) (codeAt_of_code_eq htc hc_78032c1c)
    (codeAt_of_code_eq htc hc_78032db4) (codeAt_of_code_eq htc hc_78032fa4)
    (codeAt_of_code_eq htc hc_78033260) (codeAt_of_code_eq htc hc_78035f88)
    (codeAt_of_code_eq htc hc_78035fe0) (codeAt_of_code_eq htc hc_780360c8)
    (codeAt_of_code_eq htc hc_780360e0) (codeAt_of_code_eq htc hc_7803a0fc)
    (codeAt_of_code_eq htc hc_7803a110) (codeAt_of_code_eq htc hc_7803dd28)
    (codeAt_of_code_eq htc hc_7803f54c) (codeAt_of_code_eq htc hc_7803f57c)
    (fun a h => hcw a (by rw [htc] at h; exact h)) (hro.of_unchanged hunch heap_above_ro)
    ((hregs .x2).trans hsp) hstk ((hregs .x10).trans hx10) ((hregs .x11).trans hx11)
    ((hregs .x12).trans hx12) ((hregs .x18).trans hx18) ((hregs .x19).trans hx19)
    ((hregs .x20).trans hx20) ((hregs .x22).trans hr22) ((hregs .x23).trans hr23)
    ((hregs .x24).trans hr24) ((hregs .x25).trans hr25) ((hregs .x26).trans hr26)
    ((hregs .x27).trans hr27) hokF (hSv.of_unchanged' hunch rfl (hHeap 0x1068#64 7 (by decide))) hTB
    hIVr hG0 hG1 hG2 hG3 (hRkI.of_unchanged' hunch rfl (hHeap (0x28#64) 4 (by decide)))
    (hNf.of_unchanged' hunch rfl (hHeap (0x48#64) 4 (by decide)))
    (hH.of_unchanged' hunch hHl (hHeap (0x88#64) 128 (by decide)))
    (hAkB.of_unchanged' hunch rfl (hHeap (0x4a8#64) 4 (by decide)))
    (hNkB.of_unchanged' hunch rfl (hHeap (0x4c8#64) 4 (by decide)))
    (hRextB.of_unchanged' hunch rfl (hHeap (0x4e8#64) 4 (by decide)))
    (hRivkB.of_unchanged' hunch rfl (hHeap (0x508#64) 4 (by decide)))
    (hGdB.of_unchanged' hunch rfl (hHeap (0x528#64) 4 (by decide)))
    (hRhoB.of_unchanged' hunch rfl (hHeap (0x548#64) 4 (by decide)))
    (hSeed.of_unchanged' hunch rfl (hHeap (0x568#64) 4 (by decide)))
    (hVal.of_unchanged' hunch rfl (hHeap (0x588#64) 1 (by decide)))
    (hPw.of_unchanged' hunch rfl (hHeap (0x590#64) 1 (by decide)))
    (hT12.of_unchanged' hunch rfl (hHeap (0x598#64) 12 (by decide)))
    (hAlpha.of_unchanged' hunch rfl (hHeap (0x5f8#64) 4 (by decide)))
    (hW.of_unchanged' hunch hWfl (hHeap (0x618#64) 16 (by decide)))
    (hNk.of_unchanged' hunch hNkl (hHeap (0x698#64) 4 (by decide)))
    (hRext.of_unchanged' hunch hRel (hHeap (0x6b8#64) 4 (by decide)))
    (hRk.of_unchanged' hunch hRvl (hHeap (0x6d8#64) 4 (by decide)))
    (hR16.of_unchanged' hunch hR16l (hHeap (0x6f8#64) 16 (by decide)))
    (hAk.of_unchanged' hunch hAkl (hHeap (0x778#64) 4 (by decide)))
    (hQ4.of_unchanged' hunch hQ4l (hHeap (0x798#64) 4 (by decide)))
    (hF16.of_unchanged' hunch hF16l (hHeap (0x7b8#64) 16 (by decide)))
    (hF8.of_unchanged' hunch hF8l (hHeap (0x838#64) 8 (by decide)))
    (hRi.of_unchanged' hunch hRil (hHeap (0x878#64) 4 (by decide)))
    (hIv4.of_unchanged' hunch hIv4l (hHeap (0x898#64) 4 (by decide)))
    (hIv.of_unchanged' hunch hIvl (hHeap (0x8b8#64) 4 (by decide)))
    (hGp.of_unchanged' hunch hGpl (hHeap (0x8d8#64) 12 (by decide)))
    (hKp.of_unchanged' hunch hKpl (hHeap (0x938#64) 12 (by decide)))
    (hRc.of_unchanged' hunch hRcl (hHeap (0x998#64) 4 (by decide)))
    (hSc.of_unchanged' hunch hScl (hHeap (0x9b8#64) 4 (by decide)))
    (hPs.of_unchanged' hunch hPsl (hHeap (0x9d8#64) 4 (by decide)))
    (hRm.of_unchanged' hunch hRml (hHeap (0x9f8#64) 4 (by decide)))
    (hD.of_unchanged' hunch hDl (hHeap (0xa18#64) 12 (by decide)))
    (hGb.of_unchanged' hunch hGbl (hHeap (0xa78#64) 4 (by decide)))
    (hPb.of_unchanged' hunch hPbl (hHeap (0xa98#64) 4 (by decide)))
    (hA.of_unchanged' hunch hAl (hHeap (0xab8#64) 4 (by decide)))
    (hX.of_unchanged' hunch hXl (hHeap (0xad8#64) 4 (by decide)))
    (hO13.of_unchanged' hunch hO13l (hHeap (0xaf8#64) 13 (by decide)))
    (hY.of_unchanged' hunch hYl (hHeap (0xb60#64) 117 (by decide))) hok_iptr hok_g0 hok_g1 hok_g2
    hok_g3 hilen hlo_iptr hlo_g0 hlo_g1 hlo_g2 hlo_g3 hhi_iptr hhi_g0 hhi_g1 hhi_g2 hhi_g3
    (by rw [htc]; exact hpaf) (by rw [htc]; exact hpanic) (by rw [htc]; exact hunwrap)
    (by rw [htc]; exact hpb) (by rw [htc]; exact hpp) (by rw [htc]; exact hprz)
    (by rw [htc]; exact hhandle_rv) (by rw [htc]; exact hunwrap_opt) (by rw [htc]; exact hpaf_nf)
    (by rw [htc]; exact hconst) (by rw [htc]; exact hdealloc_nf) (by rw [htc]; exact halloc_mp)
    (by rw [htc]; exact hreserve) (by rw [htc]; exact hdealloc) (by rw [htc]; exact hdealloc_cm)
    (by rw [htc]; exact hfrom_nc) (by rw [htc]; exact hdealloc_ivk) (by rw [htc]; exact hfrom_ivk)
    (fun t' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 b22 b23 b24 b25 b26 b27 hU a13 hf =>
      hk t' a1 (a2.trans htc) a3 a4 (a5.trans (hregs .x3)) (a6.trans (hregs .x4)) a7 a8 a9 a10 a11 a12 b22 b23 b24 b25 b26 b27 ((hunch.mono (by simp)).trans hU) a13 hf)

end Cases.Zip2005
