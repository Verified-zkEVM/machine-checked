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
import Cases.Zip2005.Main.MainSegA2b
import Cases.Zip2005.Main.MainFlag
import Cases.Zip2005.Main.MainAccept
import Cases.Zip2005.Image.Ro

/-!
# `main`, segment A2r

from the return of `SpendValidatingKey::randomize` to segment A2b: `parse_rk` on the instance's `rk` bytes, the `memcmp` of the randomized key's bytes against them, `from_bytes_unchecked` of `ak`'s bytes and its flag check. A spec at the internal pc `0x7801a34c` over `main`'s frame (`sp` is the frame base,
`0x10a0` bytes, the saved registers at `sp + 0x1068`), applied by the segment before it.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option asmverif.sym.foldBytes true in
theorem main_seg_a2r_spec {P : Prop} (s : MachineState) (sp vs0 vs1 vs2 vs3 vs4 vs5 vra r22 r23 r24 r25 r26 r27 : Word)
    (f0 f1 f2 f3 kr0 kr1 kr2 kr3 kb0 kb1 kb2 kb3 nb0 nb1 nb2 nb3 xb0 xb1 xb2 xb3 ib0 ib1 ib2 ib3 gb0 gb1 gb2 gb3 rb0 rb1 rb2 rb3 sd0 sd1 sd2 sd3 vv pw al0 al1 al2 al3 ng t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (H D X A Iv Gp Kp Rc Sc Ps Rm Gb Pb F16 F8 Ri Iv4 Wf Nk Re Rv Ak R16 Q4 IV G0 G1 G2 G3 : List Word)
    (hHl : H.length = 128) (hDl : D.length = 12) (hXl : X.length = 4) (hAl : A.length = 4) (hIvl : Iv.length = 4) (hGpl : Gp.length = 12) (hKpl : Kp.length = 12) (hRcl : Rc.length = 4) (hScl : Sc.length = 4) (hPsl : Ps.length = 4) (hRml : Rm.length = 4) (hGbl : Gb.length = 4) (hPbl : Pb.length = 4) (hF16l : F16.length = 16) (hF8l : F8.length = 8) (hRil : Ri.length = 4) (hIv4l : Iv4.length = 4) (hWfl : Wf.length = 16) (hNkl : Nk.length = 4) (hRel : Re.length = 4) (hRvl : Rv.length = 4) (hAkl : Ak.length = 4) (hR16l : R16.length = 16) (hQ4l : Q4.length = 4) (hIVl : IV.length = 138) (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpc : s.pc = 0x7801a34c#64)
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
    (hx18 : s.getReg .x18 = sp + 0x798#64)
    (hx19 : s.getReg .x19 = sp + 0x1067#64)
    (hx20 : s.getReg .x20 = ng)
    (hx8 : s.getReg .x8 = vv)
    (hr22 : s.getReg .x22 = r22)
    (hr23 : s.getReg .x23 = r23)
    (hr24 : s.getReg .x24 = r24)
    (hr25 : s.getReg .x25 = r25)
    (hr26 : s.getReg .x26 = r26)
    (hr27 : s.getReg .x27 = r27)
    (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi sp 532)
    (hSv : Region (sp + 0x1068#64) [vs5, vs4, vs3, vs2, vs1, vs0, vra] s)
    (hTB : Region (0x780488a8#64) [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] s)
    (hIVr : Region (iptr) IV s)
    (hG0 : Region (tg0) G0 s)
    (hG1 : Region (tg1) G1 s)
    (hG2 : Region (tg2) G2 s)
    (hG3 : Region (tg3) G3 s)
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
    (hAl : Region (sp + 0x5f8#64) [al0, al1, al2, al3] s)
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
    (hcNk : Accel.leLimbsToNat Nk < Fp.p)
    (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024)
    (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024)
    (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024)
    (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hlo_iptr : 0x78048980 ≤ iptr.toNat)
    (hlo_g0 : 0x78048980 ≤ tg0.toNat)
    (hlo_g1 : 0x78048980 ≤ tg1.toNat)
    (hlo_g2 : 0x78048980 ≤ tg2.toNat)
    (hlo_g3 : 0x78048980 ≤ tg3.toNat)
    (hhi_iptr : iptr.toNat + 8 * 138 ≤ 0x1c00000000)
    (hhi_g0 : tg0.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g1 : tg1.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g2 : tg2.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g3 : tg3.toNat + 8 * 516 ≤ 0x1c00000000)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → Safe P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = s.code → Safe P u)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → Safe P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → Safe P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → Safe P u)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → Safe P u)
    (hunwrap_opt : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = s.code → Safe P u)
    (hpaf_nf : ∀ u : MachineState, u.pc = 0x78019da0#64 → u.code = s.code → Safe P u)
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
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → Safe P t) → Safe P u)
    (hdealloc_nf : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 → u.getReg .x12 = 8#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Safe P t) → Safe P u)
    (halloc_mp : ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x80#64 →
      u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x80 ≤ 0x1c00000000 → Safe P t) → Safe P u)
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
        ptr'.toNat + 64 * n ≤ 0x1c00000000 → Safe P t) → Safe P u)
    (hdealloc : ∀ (u : MachineState) (sp' r ptr sz : Word), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 8#64 → 0x78048980 ≤ ptr.toNat →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Safe P t) → Safe P u)
    (hdealloc_cm : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Safe P t) → Safe P u)
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
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → Safe P t) → Safe P u)

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
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Safe P t) → Safe P u)
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
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Safe P t) → Safe P u)
    (hk : ∀ t : MachineState, t.pc = vra &&& ~~~1#64 → t.code = s.code →
      t.getReg .x1 = vra → t.getReg .x2 = sp + 0x10a0#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 →
      t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = r22 → t.getReg .x23 = r23 → t.getReg .x24 = r24 → t.getReg .x25 = r25 → t.getReg .x26 = r26 → t.getReg .x27 = r27 →
      Unchanged [(sp - 0x1f60#64, 1536), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000), (0x78040620#64, 4162), (0x780488a8#64, 10), (0x78048980#64, 14780690128)] s t →
      t.getReg .x10 = 0#64 →
      -- the instance's `rk` decodes (flag 1) and its bytes are the randomized key's (`memcmp`)
      (∃ (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : Word) (fr : BitVec 8), FromBytesPost kr0 kr1 kr2 kr3 (Accel.leLimbsToNat [u0, u1, u2, u3])
          (Accel.leLimbsToNat [u4, u5, u6, u7]) fr ∧ fr = 1#8 ∧
        Accel.leLimbsToNat [u8, u9, u10, u11] =
          (if Accel.leLimbsToNat [u0, u1, u2, u3] = 0 ∧ Accel.leLimbsToNat [u4, u5, u6, u7] = 0 then 0 else Fp.R)) →
      [R16[12]!, R16[13]!, R16[14]!, R16[15]!] = [kr0, kr1, kr2, kr3] →
      -- `ak`'s bytes decode (flag 1) to the point segment A2b reads, and A2b's facts over it
      (∃ (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Word), FromBytesPost Wf[12]! Wf[13]! Wf[14]! Wf[15]! (Accel.leLimbsToNat [a0, a1, a2, a3])
          (Accel.leLimbsToNat [a4, a5, a6, a7]) 1#8 ∧
        Accel.leLimbsToNat [a8, a9, a10, a11] =
          (if Accel.leLimbsToNat [a0, a1, a2, a3] = 0 ∧ Accel.leLimbsToNat [a4, a5, a6, a7] = 0 then 0 else Fp.R) ∧
        (∃ x : Nat, (Fp.toAffine (Accel.leLimbsToNat [a0, a1, a2, a3])
            (Accel.leLimbsToNat [a4, a5, a6, a7]) (Accel.leLimbsToNat [a8, a9, a10, a11])).1 = x ∧
          AcceptA2c (skWord pw t0) (skWord t0 t1) (skWord t1 t2) (skWord t2 t3) (ng &&& 1#64) [Nk[0]!, Nk[1]!, Nk[2]!, Nk[3]!]
            [f0, f1, f2, f3] [rb0, rb1, rb2, rb3] [sd0, sd1, sd2, sd3] [Wf[12]!, Wf[13]!, Wf[14]!, Wf[15]!]
            [Re[0]!, Re[1]!, Re[2]!, Re[3]!] [Rv[0]!, Rv[1]!, Rv[2]!, Rv[3]!]
            [BitVec.ofNat 64 (x >>> (64 * 0)), BitVec.ofNat 64 (x >>> (64 * 1)), BitVec.ofNat 64 (x >>> (64 * 2)),
              BitVec.ofNat 64 (x >>> (64 * 3))] [gb0, gb1, gb2, gb3] vv) ∧
        extractByte t3 5 = 0#8 ∧ extractByte t7 6 = 0#8 ∧ extractByte pw 4 ≠ 0#8) → Safe P t) :
    Safe P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1f60#64) 1536 := by
    have h1 := hstk.lo; have h2 := hstk.aligned; have h3 := hokF.offCode; have h4 := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
    have e : (sp - 0x1f60#64).toNat = sp.toNat - 0x1f60 := by bv_omega
    refine ⟨?_, ?_, ?_⟩ <;> rw [e] <;> simp only [SP1_MAX_MEMORY, Ro.layout_textLo, Ro.layout_textHi, Ro.layout_roBase] at * <;> omega
  have hokF' : RegionOk Ro.layout.textLo Ro.layout.textHi sp 532 := hokF.weaken (by decide) (Nat.le_refl _)
  have hspHi : sp.toNat + 0x10a0 ≤ 0x78000000 := by
    have h3 := hokF.offCode; have h4 := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)); simp only [Ro.layout_textHi, Ro.layout_roBase] at h3; omega
  have hu := Unchanged.refl [(sp - 0x1f60#64, 1536), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000), (0x78040620#64, 4162), (0x780488a8#64, 10), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokHpf : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 10 := fpTablesOk
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040618#64 1 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hokI : RegionOk Ro.layout.textLo Ro.layout.textHi 0x1c00000000#64 0x80000000 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hokT_28_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x28#64) 4 := hokF'.sub' 5 4 (by decide) (by bv_omega)
  have hokR_28_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x28#64) 4 := hokF.sub' 5 4 (by decide) (by bv_omega)
  have hokT_48_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x48#64) 4 := hokF'.sub' 9 4 (by decide) (by bv_omega)
  have hokR_48_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x48#64) 4 := hokF.sub' 9 4 (by decide) (by bv_omega)
  have hokT_88_128 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x88#64) 128 := hokF'.sub' 17 128 (by decide) (by bv_omega)
  have hokR_88_128 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x88#64) 128 := hokF.sub' 17 128 (by decide) (by bv_omega)
  have hokT_4a8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x4a8#64) 4 := hokF'.sub' 149 4 (by decide) (by bv_omega)
  have hokR_4a8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x4a8#64) 4 := hokF.sub' 149 4 (by decide) (by bv_omega)
  have hokT_4c8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x4c8#64) 4 := hokF'.sub' 153 4 (by decide) (by bv_omega)
  have hokR_4c8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x4c8#64) 4 := hokF.sub' 153 4 (by decide) (by bv_omega)
  have hokT_4e8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x4e8#64) 4 := hokF'.sub' 157 4 (by decide) (by bv_omega)
  have hokR_4e8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x4e8#64) 4 := hokF.sub' 157 4 (by decide) (by bv_omega)
  have hokT_508_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x508#64) 4 := hokF'.sub' 161 4 (by decide) (by bv_omega)
  have hokR_508_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x508#64) 4 := hokF.sub' 161 4 (by decide) (by bv_omega)
  have hokT_528_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x528#64) 4 := hokF'.sub' 165 4 (by decide) (by bv_omega)
  have hokR_528_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x528#64) 4 := hokF.sub' 165 4 (by decide) (by bv_omega)
  have hokT_548_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x548#64) 4 := hokF'.sub' 169 4 (by decide) (by bv_omega)
  have hokR_548_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x548#64) 4 := hokF.sub' 169 4 (by decide) (by bv_omega)
  have hokT_568_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x568#64) 4 := hokF'.sub' 173 4 (by decide) (by bv_omega)
  have hokR_568_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x568#64) 4 := hokF.sub' 173 4 (by decide) (by bv_omega)
  have hokT_588_1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x588#64) 1 := hokF'.sub' 177 1 (by decide) (by bv_omega)
  have hokR_588_1 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x588#64) 1 := hokF.sub' 177 1 (by decide) (by bv_omega)
  have hokT_590_1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x590#64) 1 := hokF'.sub' 178 1 (by decide) (by bv_omega)
  have hokR_590_1 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x590#64) 1 := hokF.sub' 178 1 (by decide) (by bv_omega)
  have hokT_598_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x598#64) 12 := hokF'.sub' 179 12 (by decide) (by bv_omega)
  have hokR_598_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x598#64) 12 := hokF.sub' 179 12 (by decide) (by bv_omega)
  have hokT_5f8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x5f8#64) 4 := hokF'.sub' 191 4 (by decide) (by bv_omega)
  have hokR_5f8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x5f8#64) 4 := hokF.sub' 191 4 (by decide) (by bv_omega)
  have hokT_618_16 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x618#64) 16 := hokF'.sub' 195 16 (by decide) (by bv_omega)
  have hokR_618_16 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x618#64) 16 := hokF.sub' 195 16 (by decide) (by bv_omega)
  have hokT_698_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x698#64) 4 := hokF'.sub' 211 4 (by decide) (by bv_omega)
  have hokR_698_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x698#64) 4 := hokF.sub' 211 4 (by decide) (by bv_omega)
  have hokT_6b8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x6b8#64) 4 := hokF'.sub' 215 4 (by decide) (by bv_omega)
  have hokR_6b8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x6b8#64) 4 := hokF.sub' 215 4 (by decide) (by bv_omega)
  have hokT_6d8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x6d8#64) 4 := hokF'.sub' 219 4 (by decide) (by bv_omega)
  have hokR_6d8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x6d8#64) 4 := hokF.sub' 219 4 (by decide) (by bv_omega)
  have hokT_6f8_16 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x6f8#64) 16 := hokF'.sub' 223 16 (by decide) (by bv_omega)
  have hokR_6f8_16 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x6f8#64) 16 := hokF.sub' 223 16 (by decide) (by bv_omega)
  have hokT_778_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x778#64) 4 := hokF'.sub' 239 4 (by decide) (by bv_omega)
  have hokR_778_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x778#64) 4 := hokF.sub' 239 4 (by decide) (by bv_omega)
  have hokT_798_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x798#64) 4 := hokF'.sub' 243 4 (by decide) (by bv_omega)
  have hokR_798_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x798#64) 4 := hokF.sub' 243 4 (by decide) (by bv_omega)
  have hokT_7b8_16 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x7b8#64) 16 := hokF'.sub' 247 16 (by decide) (by bv_omega)
  have hokR_7b8_16 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x7b8#64) 16 := hokF.sub' 247 16 (by decide) (by bv_omega)
  have hokT_838_8 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x838#64) 8 := hokF'.sub' 263 8 (by decide) (by bv_omega)
  have hokR_838_8 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x838#64) 8 := hokF.sub' 263 8 (by decide) (by bv_omega)
  have hokT_878_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x878#64) 4 := hokF'.sub' 271 4 (by decide) (by bv_omega)
  have hokR_878_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x878#64) 4 := hokF.sub' 271 4 (by decide) (by bv_omega)
  have hokT_898_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x898#64) 4 := hokF'.sub' 275 4 (by decide) (by bv_omega)
  have hokR_898_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x898#64) 4 := hokF.sub' 275 4 (by decide) (by bv_omega)
  have hokT_8b8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x8b8#64) 4 := hokF'.sub' 279 4 (by decide) (by bv_omega)
  have hokR_8b8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x8b8#64) 4 := hokF.sub' 279 4 (by decide) (by bv_omega)
  have hokT_8d8_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x8d8#64) 12 := hokF'.sub' 283 12 (by decide) (by bv_omega)
  have hokR_8d8_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x8d8#64) 12 := hokF.sub' 283 12 (by decide) (by bv_omega)
  have hokT_938_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x938#64) 12 := hokF'.sub' 295 12 (by decide) (by bv_omega)
  have hokR_938_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x938#64) 12 := hokF.sub' 295 12 (by decide) (by bv_omega)
  have hokT_998_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x998#64) 4 := hokF'.sub' 307 4 (by decide) (by bv_omega)
  have hokR_998_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x998#64) 4 := hokF.sub' 307 4 (by decide) (by bv_omega)
  have hokT_9b8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x9b8#64) 4 := hokF'.sub' 311 4 (by decide) (by bv_omega)
  have hokR_9b8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x9b8#64) 4 := hokF.sub' 311 4 (by decide) (by bv_omega)
  have hokT_9d8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x9d8#64) 4 := hokF'.sub' 315 4 (by decide) (by bv_omega)
  have hokR_9d8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x9d8#64) 4 := hokF.sub' 315 4 (by decide) (by bv_omega)
  have hokT_9f8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x9f8#64) 4 := hokF'.sub' 319 4 (by decide) (by bv_omega)
  have hokR_9f8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x9f8#64) 4 := hokF.sub' 319 4 (by decide) (by bv_omega)
  have hokT_a18_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa18#64) 12 := hokF'.sub' 323 12 (by decide) (by bv_omega)
  have hokR_a18_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa18#64) 12 := hokF.sub' 323 12 (by decide) (by bv_omega)
  have hokT_a78_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa78#64) 4 := hokF'.sub' 335 4 (by decide) (by bv_omega)
  have hokR_a78_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa78#64) 4 := hokF.sub' 335 4 (by decide) (by bv_omega)
  have hokT_a98_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa98#64) 4 := hokF'.sub' 339 4 (by decide) (by bv_omega)
  have hokR_a98_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa98#64) 4 := hokF.sub' 339 4 (by decide) (by bv_omega)
  have hokT_ab8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xab8#64) 4 := hokF'.sub' 343 4 (by decide) (by bv_omega)
  have hokR_ab8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xab8#64) 4 := hokF.sub' 343 4 (by decide) (by bv_omega)
  have hokT_ad8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xad8#64) 4 := hokF'.sub' 347 4 (by decide) (by bv_omega)
  have hokR_ad8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xad8#64) 4 := hokF.sub' 347 4 (by decide) (by bv_omega)
  have hokT_af8_130 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 130 := hokF'.sub' 351 130 (by decide) (by bv_omega)
  have hokR_af8_130 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 130 := hokF.sub' 351 130 (by decide) (by bv_omega)
  have hokT_af8_17 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 17 := hokF'.sub' 351 17 (by decide) (by bv_omega)
  have hokR_af8_17 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 17 := hokF.sub' 351 17 (by decide) (by bv_omega)
  have hokT_af8_13 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 13 := hokF'.sub' 351 13 (by decide) (by bv_omega)
  have hokR_af8_13 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 13 := hokF.sub' 351 13 (by decide) (by bv_omega)
  have hokT_af8_5 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 5 := hokF'.sub' 351 5 (by decide) (by bv_omega)
  have hokR_af8_5 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 5 := hokF.sub' 351 5 (by decide) (by bv_omega)
  have hokT_af8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 4 := hokF'.sub' 351 4 (by decide) (by bv_omega)
  have hokR_af8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 4 := hokF.sub' 351 4 (by decide) (by bv_omega)
  have hokT_af8_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 12 := hokF'.sub' 351 12 (by decide) (by bv_omega)
  have hokR_af8_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 12 := hokF.sub' 351 12 (by decide) (by bv_omega)
  have hokT_b00_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xb00#64) 12 := hokF'.sub' 352 12 (by decide) (by bv_omega)
  have hokR_b00_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xb00#64) 12 := hokF.sub' 352 12 (by decide) (by bv_omega)
  have hokT_b00_16 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xb00#64) 16 := hokF'.sub' 352 16 (by decide) (by bv_omega)
  have hokR_b00_16 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xb00#64) 16 := hokF.sub' 352 16 (by decide) (by bv_omega)
  have hokT_b00_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xb00#64) 4 := hokF'.sub' 352 4 (by decide) (by bv_omega)
  have hokR_b00_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xb00#64) 4 := hokF.sub' 352 4 (by decide) (by bv_omega)
  have hokT_b18_9 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xb18#64) 9 := hokF'.sub' 355 9 (by decide) (by bv_omega)
  have hokR_b18_9 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xb18#64) 9 := hokF.sub' 355 9 (by decide) (by bv_omega)
  have hokT_b58_1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xb58#64) 1 := hokF'.sub' 363 1 (by decide) (by bv_omega)
  have hokR_b58_1 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xb58#64) 1 := hokF.sub' 363 1 (by decide) (by bv_omega)
  have hokT_6f8_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x6f8#64) 12 := hokF'.sub' 223 12 (by decide) (by bv_omega)
  have hokR_6f8_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x6f8#64) 12 := hokF.sub' 223 12 (by decide) (by bv_omega)
  have hokT_758_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x758#64) 4 := hokF'.sub' 235 4 (by decide) (by bv_omega)
  have hokR_758_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x758#64) 4 := hokF.sub' 235 4 (by decide) (by bv_omega)
  have hokT_a98_1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa98#64) 1 := hokF'.sub' 339 1 (by decide) (by bv_omega)
  have hokR_a98_1 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa98#64) 1 := hokF.sub' 339 1 (by decide) (by bv_omega)
  have hokT_a18_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa18#64) 4 := hokF'.sub' 323 4 (by decide) (by bv_omega)
  have hokR_a18_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa18#64) 4 := hokF.sub' 323 4 (by decide) (by bv_omega)
  have hokT_818_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x818#64) 12 := hokF'.sub' 259 12 (by decide) (by bv_omega)
  have hokR_818_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x818#64) 12 := hokF.sub' 259 12 (by decide) (by bv_omega)
  have hokT_7b8_24 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x7b8#64) 24 := hokF'.sub' 247 24 (by decide) (by bv_omega)
  have hokR_7b8_24 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x7b8#64) 24 := hokF.sub' 247 24 (by decide) (by bv_omega)
  have hokT_7b8_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x7b8#64) 12 := hokF'.sub' 247 12 (by decide) (by bv_omega)
  have hokR_7b8_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x7b8#64) 12 := hokF.sub' 247 12 (by decide) (by bv_omega)
  have hokT_7b8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x7b8#64) 4 := hokF'.sub' 247 4 (by decide) (by bv_omega)
  have hokR_7b8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x7b8#64) 4 := hokF.sub' 247 4 (by decide) (by bv_omega)
  have hokT_618_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x618#64) 12 := hokF'.sub' 195 12 (by decide) (by bv_omega)
  have hokR_618_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x618#64) 12 := hokF.sub' 195 12 (by decide) (by bv_omega)
  have hokT_1068_7 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x1068#64) 7 := hokF'.sub' 525 7 (by decide) (by bv_omega)
  have hokR_1068_7 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x1068#64) 7 := hokF.sub' 525 7 (by decide) (by bv_omega)
  -- the table words pinned: a callee that reads the tables would otherwise get them as literals
  have hprk := parse_rk_spec (P := P) (cap := tcap) (iptr := iptr) (ilen := ilen) (g0 := tg0) (g1 := tg1) (g2 := tg2) (g3 := tg3) (hmod := hmod) (hx := hx) (IV := IV) (G0 := G0) (G1 := G1) (G2 := G2) (G3 := G3)
  have hfbu := ep_from_bytes_unchecked_spec (P := P) (cap := tcap) (iptr := iptr) (ilen := ilen) (g0 := tg0) (g1 := tg1) (g2 := tg2) (g3 := tg3) (hmod := hmod) (hx := hx) (IV := IV) (G0 := G0) (G1 := G1) (G2 := G2) (G3 := G3)
  -- the output slot and the scratch above it as one block: `parse_rk` writes 17 words over the first 13 and
  -- the next 4 (a 13-word region there would leave the executor a stale read-only bound)
  obtain ⟨OY, hOY, hOYl⟩ := Region.exists_junk (sp + 0xaf8#64) 130 s
  -- the executor attaches a read-only bound to a region by its base alone: keep none at this base
  clear hokR_af8_130 hokR_af8_17 hokR_af8_13 hokR_af8_5 hokR_af8_4 hokR_af8_12
  -- `nk`'s canonicity in the shape segment A2b's premise takes once the executor holds `Nk` as its cells
  have hcNk' : Accel.leLimbsToNat [Nk[0]!, Nk[1]!, Nk[2]!, Nk[3]!] < Fp.p := by
    rw [list4_eta hNkl]; exact hcNk
  sym_exec [hprk, memcmp4_spec, hfbu, main_seg_a2b_spec, hpaf, hpanic, hunwrap, hpb, hpp, hprz,
    hhandle_rv, hunwrap_opt, hpaf_nf, hconst, hdealloc_nf, halloc_mp, hreserve, hdealloc,
    hdealloc_cm] 3000
  all_goals (sym_close hk)
  all_goals first
    | exact ⟨post5_0, post5_1, post5_2, post5_3, post5_4, post5_5, post5_6, post5_7, post5_8, post5_9, post5_10, post5_11, post5_13, post5_19, fb_flag_nbeq0 post5_19 v6_def hbr7, post5_20⟩
    | have hL' := ‹post5_13 = 1#8 → _› (fb_flag_nbeq0 post5_19 v6_def hbr7); rw [v16_def, v17_def, v18_def, v19_def, post30_4.mp (memcmp_zero _ _ post30_5 v31_def hbr32), ← v8_def, ← v9_def, ← v10_def, ← v11_def, hL']; rfl
    | rw [fb_flag_ne1 post46_18 v47_def hbr50, ← v33_def, ← v34_def, ← v35_def, ← v36_def] at post46_18; simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at post51_20; exact ⟨post46_0, post46_1, post46_2, post46_3, post46_4, post46_5, post46_6, post46_7, post46_8, post46_9, post46_10, post46_11, post46_18, post46_19, post51_20, post51_21, post51_22, post51_23⟩


end Cases.Zip2005
