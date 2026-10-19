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
import Cases.Zip2005.Main.MainSegA1
import Cases.Zip2005.Bridge.MainAccepts
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `main` (0x78019ff4)

The guest: two `read_vec_raw`s (the instance, then the witness), the two visitors, the parses,
the derivations and the checks against the instance; `a0 = 0` on the accepting path, every
other path a panic or a rejecting halt. From `0x7801a1c4` on, the cut segments (`MainSegA1` …
`MainSegE`); the runtime underneath enters as the hypotheses of `docs/ASSUMPTIONS.md`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- `L` rounded up to a multiple of 8, the way `read_vec` advances the hint pointer. -/
theorem round8_toNat (L : Word) (h : L.toNat + 7 < 2 ^ 64) :
    (L + 7#64 &&& 18446744073709551608#64).toNat = (L.toNat + 7) / 8 * 8 := by
  have e : (L + 7#64 &&& 18446744073709551608#64) = ((L + 7#64) >>> 3) <<< 3 := by bv_decide
  rw [e, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option machineChecked.sym.foldBytes true in
theorem main_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp b : Word) (I : List (BitVec 8))
    (hpc : s.pc = 0x78019ff4#64)
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
    (hc_78032b38 : CodeAt F_78032b38.base F_78032b38.prog s)
    (hc_78030a94 : CodeAt F_78030a94.base F_78030a94.prog s)
    (hc_780326cc : CodeAt F_780326cc.base F_780326cc.prog s)
    (hc_78032560 : CodeAt F_78032560.base F_78032560.prog s)
    (hc_78032614 : CodeAt F_78032614.base F_78032614.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3000 sp)
    (hI : s.privateInput = I) (hIl : I.length < 2 ^ 60)
    (hB : Region 0x78040618#64 [b] s) (hb : 0x1c00000000 ≤ b.toNat)
    (hokJ : RegionOk Ro.layout.textLo Ro.layout.textHi b 175)
    -- the witness window: the second hint buffer starts at the rounded instance length
    -- the private input fits the hint area above `b`
    (hbI : b.toNat + I.length + 1416 ≤ 0x2000000000)
    -- `FP_TABLES` uninitialised (`Once` state 0): the first decompression builds them, through
    -- the allocator's contracts for the build
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : Word)
    (hT0 : Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] s)
    {c : Word → Option Instr} (hcc : s.code = c)
    (hsq_alloc : SqAlloc G nb P c) (hsq_realloc_g : SqReallocG G nb P c)
    (hsq_alloci : SqAllocInv G nb P c) (hsq_realloc : SqRealloc G nb P c)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G nb P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G nb P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G nb P u)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G nb P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G nb P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hhandle_al : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G nb P u)
    (hpaf_nf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78019da0#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hhalt_hint : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035e44#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hhalt_empty : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035f14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (hfmt : ∀ (u : MachineState) (sp' d : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fa4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78019fa4#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        S.length = 3 → Region d S t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (halloc : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r' → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (halloc_mp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x80#64 →
      u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x80 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 16) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (hreserve : ∀ (u : MachineState) (sp' hdr ptr : Word) (n : Nat) (B : List Word) (L' : List (Word × Nat)),
      u.pc = 0x7801cac0#64 → u.code = s.code → u.getReg .x1 = 0x7801d1e8#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x100 sp' → u.getReg .x10 = hdr → u.getReg .x11 = BitVec.ofNat 64 n →
      Region hdr [BitVec.ofNat 64 n, ptr, BitVec.ofNat 64 n] u → RegionOk Ro.layout.roBase Ro.layout.textHi hdr 3 →
      Disjoint (sp' - 0x100#64) 32 hdr 3 → Disjoint 0x78040620#64 14780694332 hdr 3 → 4 ≤ n → n ≤ 16 →
      B.length = 4 * n → Region ptr B u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 32 * n ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, 4 * n) :: L') u →
      (∀ (t : MachineState) (ptr' : Word) (B' : List Word), t.pc = 0x7801d1e8#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x100#64, 32), (hdr, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region hdr [BitVec.ofNat 64 (2 * n), ptr', BitVec.ofNat 64 n] t → B'.length = 4 * n →
        Region ptr' (B ++ B') t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr' (8 * n) → 0x78048980 ≤ ptr'.toNat →
        ptr'.toNat + 64 * n ≤ 0x1c00000000 → Run.HeapAt ((ptr', 8 * n) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc : ∀ (u : MachineState) (sp' r ptr sz : Word) (k : Nat) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 8#64 → 0x78048980 ≤ ptr.toNat →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc_hint : ∀ (u : MachineState) (sp' r ptr : Word) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → u.getReg .x10 = ptr → 0x1c00000000 ≤ ptr.toNat →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc_nf : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 → u.getReg .x12 = 8#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc_ivk : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      0x78040620 ≤ iptr.toNat → 0x78040620 ≤ tg0.toNat → 0x78040620 ≤ tg1.toNat → 0x78040620 ≤ tg2.toNat →
      0x78040620 ≤ tg3.toNat → IV.length = 138 → G0.length = 1024 → G1.length = 1024 →
      G2.length = 1024 → G3.length = 516 → ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780215d8#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (hdealloc_cm : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (hconst : ∀ (u : MachineState) (sp' a0' : Word) (O1 O2 O3 : List Word) (L' : List (Word × Nat)),
      O1.length = 3 → O2.length = 36 → O3.length = 36 →
      u.pc = 0x78023cbc#64 → u.code = s.code → u.getReg .x1 = 0x7802084c#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x60 sp' → u.getReg .x10 = a0' →
      Region a0' O1 u → Region (a0' + 0x18#64) O2 u → Region (a0' + 0x138#64) O3 u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 75 → Disjoint (sp' - 0x60#64) 12 a0' 75 →
      RoImage Ro.layout u → Disjoint 0x78040620#64 14780694332 a0' 75 →
      Run.HeapAt L' u →
      (∀ t, t.pc = 0x7802084c#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x60#64, 12), (a0', 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        ∀ (ptr : Word) (MI : List Word), MI.length = 36 →
        Region a0' [64#64, ptr, 64#64] t → Region (a0' + 0x18#64) Poseidon.mdsWords t →
        Region (a0' + 0x138#64) MI t →
        Region ptr Poseidon.rcWords t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 768 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 768) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (hfrom_ivk : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word)
      (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (a0 a1 a2 a3 n0 n1 n2 n3 : Word) (L' : List (Word × Nat)), O1.length = 3 →
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
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 12 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x780212ac#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 12 → Region a0' [cap, ptr, 510#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 65 →
        (∀ o, o < 510 → byteAt Bv o = bw (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((ptr, 64) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (hfrom_nc : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (g0 g1 g2 g3 p0 p1 p2 p3 v r0 r1 r2 r3 q0 q1 q2 q3 : Word) (L' : List (Word × Nat)), O1.length = 3 →
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
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 18 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x78020dc4#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 18 → Region a0' [cap, ptr, 1090#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 137 →
        (∀ o, o < 1090 → byteAt Bv o = bw (noteBit [g0, g1, g2, g3] [p0, p1, p2, p3] v
          (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 137 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 256) :: L') t → SafeN G nb P t) → SafeN G nb P u)

    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3000#64, 1536), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000),
        (0x78040620#64, 4162), (0x780488a8#64, 10), (0x78048980#64, 14780690128)] s t →
      t.getReg .x10 = 0#64 →
      -- the accepting path: the input decodes and the guest's statement holds (`Cases.Zip2005.Top.GuestAccepts`)
      Cases.Zip2005.Top.GuestAccepts I → SafeN G nb P t) :
    SafeN G nb P s := by
  subst hcc
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x3000#64) 1536 := hstk.frame 1536 (by decide)
  have hu := Unchanged.refl [(sp - 0x3000#64, 1536), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000),
    (0x78040620#64, 4162), (0x780488a8#64, 10), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokHpf : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 10 := fpTablesOk
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040618#64 1 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hokI : RegionOk Ro.layout.textLo Ro.layout.textHi 0x1c00000000#64 0x80000000 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hmS : sp &&& 7#64 = 0#64 := by
    have ha := hstk.aligned
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    simp only [BitVec.toNat_ofNat]
    rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10a0#64) 532 := hokS.sub' 1004 532 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x10a0#64) 532 s
  rw [MachineChecked.RiscV.Sym.List.eq_map_range F0 hF0l] at hF0
  obtain ⟨J, hJ, hJl⟩ := Region.exists_junk b 175 s
  -- `From<io::Error>` without the private-input clause, for the callees stated that way
  have hio_w : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u :=
    fun u sp' r' L' h1 h2 h3 h4 h5 h6 h7 h8 hk =>
      hio u sp' r' L' h1 h2 h3 h4 h5 h6 h7 h8 (fun t e a1 a2 a3 _ a4 a5 a6 => hk t e a1 a2 a3 a4 a5 a6)
  -- `__rust_dealloc` likewise, for segment A1, which does not state `privateInput`
  have hdealloc_w : ∀ (u : MachineState) (sp' r ptr sz : Word) (k : Nat) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 8#64 → 0x78048980 ≤ ptr.toNat →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u :=
    fun u sp' r ptr sz k L' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hk =>
      hdealloc u sp' r ptr sz k L' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 (fun t a1 a2 a3 _ a4 a5 => hk t a1 a2 a3 a4 a5)
  rw [MachineChecked.RiscV.Sym.List.eq_map_range J hJl] at hJ
  -- segment A1 with its code pinned to `main`'s: the executor would take the calling state's
  have ha1 := fun (L' : List (Word × Nat)) => main_seg_a1_spec (G := G) (nb := nb) (P := P) (L := L') (cd := s.code)
  sym_exec [read_vec_raw_spec', instance_visitor_spec', witness_visitor_spec,
    memcpy_d7s0_113_spec, memcpy_d0s0_113_spec, ha1, hpaf, hpp, hprz, hpb, hpanic,
    hunwrap, hhandle_rv, hhandle_al, hunwrap_opt, hpaf_nf, hhalt_hint, hhalt_empty, hio, hfmt,
    halloc, halloc_mp, hreserve, hdealloc, hdealloc_hint, hdealloc_nf, hdealloc_ivk, hdealloc_cm,
    hconst, hfrom_ivk, hfrom_nc, hio_w, hdealloc_w] stop [0x7801a030] 8000
  rcases post15_12 with ⟨hI1, hlen1, hD1, hB1, hb1⟩ | ⟨L, B, hL, hI2, hLI, hbB, hB, hBl, hBp, hD2, hb2⟩
  · -- no input: `empty_input_stream_halt`
    subst hD1 hB1 hb1
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at *
    sym_reframe
    sym_exec [read_vec_raw_spec', instance_visitor_spec', witness_visitor_spec,
      memcpy_d7s0_113_spec, memcpy_d0s0_113_spec, ha1, hpaf, hpp, hprz, hpb, hpanic,
      hunwrap, hhandle_rv, hhandle_al, hunwrap_opt, hpaf_nf, hhalt_hint, hhalt_empty, hio, hfmt,
      halloc, halloc_mp, hreserve, hdealloc, hdealloc_hint, hdealloc_nf, hdealloc_ivk, hdealloc_cm,
      hconst, hfrom_ivk, hfrom_nc, hio_w, hdealloc_w] 400
    -- no goal: every path ended in a halt contract
  · -- the instance vector at `b`
    subst hD2 hb2
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at *
    sym_reframe
    sym_exec [read_vec_raw_spec', instance_visitor_spec', witness_visitor_spec,
      memcpy_d7s0_113_spec, memcpy_d0s0_113_spec, ha1, hpaf, hpp, hprz, hpb, hpanic,
      hunwrap, hhandle_rv, hhandle_al, hunwrap_opt, hpaf_nf, hhalt_hint, hhalt_empty, hio, hfmt,
      halloc, halloc_mp, hreserve, hdealloc, hdealloc_hint, hdealloc_nf, hdealloc_ivk, hdealloc_cm,
      hconst, hfrom_ivk, hfrom_nc, hio_w, hdealloc_w] stop [0x7801a074] 400
    -- the stack pieces the callees cut out of the junk frame: their `RegionOk` facts
    have hokF0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10a0#64) 247 := hokF.sub' 0 247 (by decide) (by simp)
    have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10a0#64 + 1992#64) 102 := hokF.sub' 249 102 (by decide) rfl
    have hokF2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10a0#64 + 2944#64) 164 := hokF.sub' 368 164 (by decide) rfl
    have hokInst : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 18446744073709550168#64) 17 :=
      hokS.sub' 1355 17 (by decide) (by bv_omega)
    have hokDe : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 18446744073709549336#64) 2 :=
      hokS.sub' 1251 2 (by decide) (by bv_omega)
    -- the witness window at `bp`, junk, before either branch reads it
    obtain ⟨bp, hbp_eq⟩ : ∃ bp : Word, bp = b + (L + 7#64 &&& 18446744073709551608#64) := ⟨_, rfl⟩
    have hbpn : bp.toNat = b.toNat + (L.toNat + 7) / 8 * 8 := by
      rw [hbp_eq, BitVec.toNat_add, round8_toNat L (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have hbp : 0x1c00000000 ≤ bp.toNat := by omega
    have hokJ2 : RegionOk Ro.layout.textLo Ro.layout.textHi bp 175 :=
      ⟨by have := hokJ.aligned; omega, by simp only [SP1_MAX_MEMORY]; omega,
        .inr (by simp only [Ro.layout_textHi]; omega)⟩
    clear hbpn
    have hbp_eq' := hbp_eq
    simp only [← hbp_eq'] at *
    obtain ⟨J2, hJ2, hJ2l⟩ := Region.exists_junk bp 175 t
    rw [MachineChecked.RiscV.Sym.List.eq_map_range J2 hJ2l] at hJ2
    obtain ⟨hV, hd0, hd1, hl128⟩ | ⟨e, hVe, hlt⟩ := ‹_ ∨ _›
    · -- the instance read: `Ok`, tag byte 0; its vector's capacity is nonzero
      have htag : extractByte post17_0[0]! 0 = 0#8 := by rw [hV]; exact instW_tag _ _
      subst hV hd0 hd1
      rw [hBp] at htag
      have hcap : 128 ≤ (L + 7#64 &&& 18446744073709551608#64).toNat := round8_ge L hl128 (by omega)
      have hv9 : L + 7#64 &&& 18446744073709551608#64 = t.getReg Reg.x9 := by rw [hx9]; assumption
      have hcap9 : 128 ≤ (t.getReg Reg.x9).toNat := hv9 ▸ hcap
      rw [hx9] at hcap9
      sym_reframe
      sym_exec [read_vec_raw_spec', instance_visitor_spec', witness_visitor_spec,
        memcpy_d7s0_113_spec, memcpy_d0s0_113_spec, ha1, hpaf, hpp, hprz, hpb,
        hpanic, hunwrap, hhandle_rv, hhandle_al, hunwrap_opt, hpaf_nf, hhalt_hint, hhalt_empty,
        hio, hfmt, halloc, halloc_mp, hreserve, hdealloc, hdealloc_hint, hdealloc_nf, hdealloc_ivk,
        hdealloc_cm, hconst, hfrom_ivk, hfrom_nc, hio_w, hdealloc_w] stop [0x7801a174] 800
      obtain ⟨hI5, hlen5, hD5, hB5, hb5⟩ | ⟨L1, B1, hL1, hI6, hLI1, hbB1, hB1, hB1l, hBp1, hD6, hb6⟩ := ‹_ ∨ _›
      · -- no witness: `empty_input_stream_halt`
        subst hD5 hB5 hb5
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at *
        sym_reframe
        sym_exec [read_vec_raw_spec', instance_visitor_spec', witness_visitor_spec,
          memcpy_d7s0_113_spec, memcpy_d0s0_113_spec, ha1, hpaf, hpp, hprz, hpb,
          hpanic, hunwrap, hhandle_rv, hhandle_al, hunwrap_opt, hpaf_nf, hhalt_hint, hhalt_empty,
          hio, hfmt, halloc, halloc_mp, hreserve, hdealloc, hdealloc_hint, hdealloc_nf,
          hdealloc_ivk, hdealloc_cm, hconst, hfrom_ivk, hfrom_nc, hio_w, hdealloc_w] 400
        -- no goal: every path ended in a halt contract
      · -- the witness vector at `bp`: the visitor, then segment A1 at `0x7801a1c4`
        subst hD6 hb6
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at *
        have hokFA : RegionOk Ro.layout.roBase Ro.layout.textHi (sp - 0x10a0#64) 532 := by
          have h1 := hstk.lo; have h2 := hstk.aligned; have h4 := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
          have e : (sp - 0x10a0#64).toNat = sp.toNat - 0x10a0 := by bv_omega
          refine ⟨?_, ?_, ?_⟩ <;> rw [e] <;> simp only [SP1_MAX_MEMORY, Ro.layout_textLo, Ro.layout_textHi, Ro.layout_roBase] at * <;> omega
        sym_reframe
        sym_exec [read_vec_raw_spec', instance_visitor_spec', witness_visitor_spec,
          memcpy_d7s0_113_spec, memcpy_d0s0_113_spec, ha1, hpaf, hpp, hprz, hpb,
          hpanic, hunwrap, hhandle_rv, hhandle_al, hunwrap_opt, hpaf_nf, hhalt_hint, hhalt_empty,
          hio, hfmt, halloc, halloc_mp, hreserve, hdealloc, hdealloc_hint, hdealloc_nf,
          hdealloc_ivk, hdealloc_cm, hconst, hfrom_ivk, hfrom_nc, hio_w, hdealloc_w] 800
        all_goals (sym_close hk)
        all_goals first
          | exact hcode.trans hcode0
          | exact Cases.Zip2005.Top.guestAccepts_main (I := I) (hL := hL) (hLI := hLI) (hl128 := hl128) (hB := hB) (hBp := hBp)
              (hJL := rfl) (h27 := acc27_0_def) (h34 := acc34_0_def) (h56 := acc56_0_def) (hL1 := hL1) (hLI1 := hLI1)
              (hB1 := hB1) (hBp1 := hBp1) (hJL2 := rfl) (hWLl := by simp) (hWL := fun i hi => by interval_cases i <;> simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]) (hVL := fun k hk => by interval_cases k <;> simp only [List.getElem!_cons_zero, List.getElem!_cons_succ])
              (hok := post20_7) (halq := post21_20) (hG := post21_21) (hsk := post21_24) (hniche := post21_25)
    · -- the instance read failed: the error path
      have htag : extractByte post17_0[0]! 0 = 1#8 := by rw [hVe]; exact errW_tag _
      subst hVe
      sym_reframe
      sym_exec [read_vec_raw_spec', instance_visitor_spec', witness_visitor_spec,
        memcpy_d7s0_113_spec, memcpy_d0s0_113_spec, ha1, hpaf, hpp, hprz, hpb,
        hpanic, hunwrap, hhandle_rv, hhandle_al, hunwrap_opt, hpaf_nf, hhalt_hint, hhalt_empty,
        hio, hfmt, halloc, halloc_mp, hreserve, hdealloc, hdealloc_hint, hdealloc_nf, hdealloc_ivk,
        hdealloc_cm, hconst, hfrom_ivk, hfrom_nc, hio_w, hdealloc_w] 800
      -- no goal: every path ended in a halt contract

end Cases.Zip2005
