import Cases.Zip2005.Kit.CellsGlue
import Cases.Zip2005.Orchard.CommitIvk
import Cases.Zip2005.Field.CtEq
import Cases.Zip2005.Orchard.DeriveUnchecked
import Cases.Zip2005.Curve.EpMulFq
import Cases.Zip2005.Orchard.ExtractP
import Cases.Zip2005.Orchard.ExtractedNoteCommitment
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Curve.FromBytesUnchecked
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
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `main`, segment D

from the return of `NoteCommitment::derive` to `main`'s return: the commitment flag, `extract_p`, `parse_merkle_path` (its result unused: divergence 1), the instance nullifier through `ExtractedNoteCommitment::from_bytes`, `Nullifier::derive`, `ct_eq`. A spec at the internal pc `0x7801ab44` over `main`'s frame (`sp` is the frame base,
`0x10a0` bytes, the saved registers at `sp + 0x1068`), applied by the segment before it.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option machineChecked.sym.foldBytes true in
theorem main_seg_d_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp vs0 vs1 vs2 vs3 vs4 vs5 vra r22 r23 r24 r25 r26 r27 : Word)
    (f0 f1 f2 f3 n0 n1 n2 n3 q0 q1 q2 q3 r0 r1 r2 r3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 cf pw z : Word) (H Y D X : List Word)
    (hHl : H.length = 128) (hYl : Y.length = 117) (hDl : D.length = 12) (hXl : X.length = 4)
    (hpc : s.pc = 0x7801ab44#64)
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
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1f60 sp)
    (hx18 : s.getReg .x18 = sp + 0x798#64)
    (hx19 : s.getReg .x19 = sp + 0x1067#64)
    (hr22 : s.getReg .x22 = r22)
    (hr23 : s.getReg .x23 = r23)
    (hr24 : s.getReg .x24 = r24)
    (hr25 : s.getReg .x25 = r25)
    (hr26 : s.getReg .x26 = r26)
    (hr27 : s.getReg .x27 = r27)
    (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi sp 532)
    (hSv : Region (sp + 0x1068#64) [vs5, vs4, vs3, vs2, vs1, vs0, vra] s)
    (hNf : Region (sp + 0x48#64) [f0, f1, f2, f3] s)
    (hH : Region (sp + 0x88#64) H s)
    (hPw : Region (sp + 0x590#64) [pw] s)
    (hNk : Region (sp + 0x698#64) [n0, n1, n2, n3] s)
    (hPsi : Region (sp + 0x9d8#64) [q0, q1, q2, q3] s)
    (hD : Region (sp + 0xa18#64) D s)
    (hRho : Region (sp + 0xab8#64) [r0, r1, r2, r3] s)
    (hZ : Region (sp + 0xa98#64) [z] s)
    (hX : Region (sp + 0xad8#64) X s)
    (hCm : Region (sp + 0xaf8#64) [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, cf] s)
    (hY : Region (sp + 0xb60#64) Y s)
    (hcNk : Accel.leLimbsToNat [n0, n1, n2, n3] < Fp.p)
    (hcRho : Accel.leLimbsToNat [r0, r1, r2, r3] < Fp.p)
    (hcPsi : Accel.leLimbsToNat [q0, q1, q2, q3] < Fp.p)
    (hcZ : Accel.leLimbsToNat [c8, c9, c10, c11] < Fp.p)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G nb P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G nb P u)
    (hpaf_nf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78019da0#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
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
    (hdealloc_nf : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 → u.getReg .x12 = 8#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
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
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (hk : ∀ t : MachineState, t.pc = vra &&& ~~~1#64 → t.code = s.code →
      t.getReg .x1 = vra → t.getReg .x2 = sp + 0x10a0#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 →
      t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = r22 → t.getReg .x23 = r23 → t.getReg .x24 = r24 → t.getReg .x25 = r25 → t.getReg .x26 = r26 → t.getReg .x27 = r27 →
      Unchanged [(sp - 0x1f60#64, 1536), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000), (0x78040620#64, 4162), (0x780488a8#64, 10), (0x78048980#64, 14780690128)] s t →
      t.getReg .x10 = 0#64 →
      -- the note commitment is not ⊥, the instance nullifier is canonical, and the derived
      -- nullifier equals it (both in Montgomery form, limb by limb)
      extractByte cf 0 = 1#8 → Accel.leLimbsToNat [f0, f1, f2, f3] < Fp.p →
      Accel.natToLeLimbs 4 (nullifierX (Accel.leLimbsToNat [n0, n1, n2, n3]) (Accel.leLimbsToNat [r0, r1, r2, r3]) (Accel.leLimbsToNat [q0, q1, q2, q3]) [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]) = Accel.natToLeLimbs 4 (Fp.mul (Accel.leLimbsToNat [f0, f1, f2, f3]) Fp.R2) →
      -- `[nf scalar] K^Orchard` ran as its model says
      mulFacts kOrchardW (nullifierScalarW (Accel.leLimbsToNat [n0, n1, n2, n3]) (Accel.leLimbsToNat [r0, r1, r2, r3]) (Accel.leLimbsToNat [q0, q1, q2, q3])) → SafeN G nb P t) :
    SafeN G nb P s := by
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
  have hokT_48_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x48#64) 4 := hokF'.sub' 9 4 (by decide) (by bv_omega)
  have hokR_48_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x48#64) 4 := hokF.sub' 9 4 (by decide) (by bv_omega)
  have hokT_88_128 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x88#64) 128 := hokF'.sub' 17 128 (by decide) (by bv_omega)
  have hokR_88_128 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x88#64) 128 := hokF.sub' 17 128 (by decide) (by bv_omega)
  have hokT_590_1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x590#64) 1 := hokF'.sub' 178 1 (by decide) (by bv_omega)
  have hokR_590_1 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x590#64) 1 := hokF.sub' 178 1 (by decide) (by bv_omega)
  have hokT_698_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x698#64) 4 := hokF'.sub' 211 4 (by decide) (by bv_omega)
  have hokR_698_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x698#64) 4 := hokF.sub' 211 4 (by decide) (by bv_omega)
  have hokT_9d8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x9d8#64) 4 := hokF'.sub' 315 4 (by decide) (by bv_omega)
  have hokR_9d8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x9d8#64) 4 := hokF.sub' 315 4 (by decide) (by bv_omega)
  have hokT_a18_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa18#64) 12 := hokF'.sub' 323 12 (by decide) (by bv_omega)
  have hokR_a18_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa18#64) 12 := hokF.sub' 323 12 (by decide) (by bv_omega)
  have hokT_ab8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xab8#64) 4 := hokF'.sub' 343 4 (by decide) (by bv_omega)
  have hokR_ab8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xab8#64) 4 := hokF.sub' 343 4 (by decide) (by bv_omega)
  have hokT_a98_1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa98#64) 1 := hokF'.sub' 339 1 (by decide) (by bv_omega)
  have hokR_a98_1 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa98#64) 1 := hokF.sub' 339 1 (by decide) (by bv_omega)
  have hokT_ad8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xad8#64) 4 := hokF'.sub' 347 4 (by decide) (by bv_omega)
  have hokR_ad8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xad8#64) 4 := hokF.sub' 347 4 (by decide) (by bv_omega)
  have hokT_af8_13 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 13 := hokF'.sub' 351 13 (by decide) (by bv_omega)
  have hokR_af8_13 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 13 := hokF.sub' 351 13 (by decide) (by bv_omega)
  have hokT_b60_117 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xb60#64) 117 := hokF'.sub' 364 117 (by decide) (by bv_omega)
  have hokR_b60_117 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xb60#64) 117 := hokF.sub' 364 117 (by decide) (by bv_omega)
  have hokT_af8_130 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 130 := hokF'.sub' 351 130 (by decide) (by bv_omega)
  have hokR_af8_130 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 130 := hokF.sub' 351 130 (by decide) (by bv_omega)
  have hokT_af8_5 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 5 := hokF'.sub' 351 5 (by decide) (by bv_omega)
  have hokR_af8_5 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 5 := hokF.sub' 351 5 (by decide) (by bv_omega)
  have hokT_af8_4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 4 := hokF'.sub' 351 4 (by decide) (by bv_omega)
  have hokR_af8_4 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 4 := hokF.sub' 351 4 (by decide) (by bv_omega)
  have hokT_af8_12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xaf8#64) 12 := hokF'.sub' 351 12 (by decide) (by bv_omega)
  have hokR_af8_12 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xaf8#64) 12 := hokF.sub' 351 12 (by decide) (by bv_omega)
  have hokT_1068_7 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x1068#64) 7 := hokF'.sub' 525 7 (by decide) (by bv_omega)
  have hokR_1068_7 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x1068#64) 7 := hokF.sub' 525 7 (by decide) (by bv_omega)
  by_cases hc : Accel.leLimbsToNat [f0, f1, f2, f3] < Fp.p
  · sym_exec [memcpy96_spec, extract_p_spec, parse_merkle_path_spec', enc_from_bytes_ok_spec,
      nullifier_derive_spec, fp_ct_eq_spec, hpaf, hpanic, hhandle_rv, hunwrap_opt, hpaf_nf,
      hconst, hdealloc_nf, halloc_mp, hreserve, hdealloc] 3000
    all_goals (sym_close hk)
    all_goals first
      | with_reducible exact flag_of_br _ _ ‹_› ‹_›
      | with_reducible (rw [‹nullifierX _ _ _ _ = _›]; exact natToLeLimbs_four_eq _ _ _ _ _ _ (ct_of_br _ _ ‹_› ‹_›) ‹_› ‹_› ‹_› ‹_›)
  · sym_exec [memcpy96_spec, extract_p_spec, parse_merkle_path_spec', enc_from_bytes_bad_spec,
      nullifier_derive_spec, fp_ct_eq_spec, hpaf, hpanic, hhandle_rv, hunwrap_opt, hpaf_nf,
      hconst, hdealloc_nf, halloc_mp, hreserve, hdealloc] 3000


end Cases.Zip2005
