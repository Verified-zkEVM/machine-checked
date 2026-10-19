import Cases.Zip2005.Top.Accepting
import Cases.Zip2005.Sinsemilla.FromIterIvkContract
import Cases.Zip2005.Sinsemilla.FromIterNoteContract
import Cases.Zip2005.Poseidon.ConstantsContract
import Cases.Zip2005.Runtime.ReserveMp
import Cases.Zip2005.Image.Ro

/-!
# The assumptions, bundled

`MainAssumptions s ra sp b I` is every premise of `main_spec` except its continuation: the
loaded image, the entry state (`FP_TABLES` uninitialised among the statics, the private input
fitting the hint area above `b`), the runtime contracts (the allocator's, `FP_TABLES`' build's,
`From<io::Error>`) and the panic and reject-halt paths, for the entry state `s`, return address
`ra`, stack pointer `sp`, bump pointer `b` and private input `I`. `guest_accepting_run'` is the
top-level theorem with that single premise; `Top/Guest.lean` discharges the runtime contracts.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- The loaded code (A1): each function `main_spec` steps is loaded at its address, and the code
    map is confined to `.text`. Proved of the loaded image, against the generated image data,
    by `RunCode.of_image` (`Top/Load.lean`). -/
structure RunCode (s : MachineState) : Prop where
  hc_78016938 : CodeAt F_78016938.base F_78016938.prog s
  hc_7801775c : CodeAt F_7801775c.base F_7801775c.prog s
  hc_7801806c : CodeAt F_7801806c.base F_7801806c.prog s
  hc_7801823c : CodeAt F_7801823c.base F_7801823c.prog s
  hc_780191c4 : CodeAt F_780191c4.base F_780191c4.prog s
  hc_780197cc : CodeAt F_780197cc.base F_780197cc.prog s
  hc_78019918 : CodeAt F_78019918.base F_78019918.prog s
  hc_78019a10 : CodeAt F_78019a10.base F_78019a10.prog s
  hc_78019b50 : CodeAt F_78019b50.base F_78019b50.prog s
  hc_78019bf0 : CodeAt F_78019bf0.base F_78019bf0.prog s
  hc_78019cb8 : CodeAt F_78019cb8.base F_78019cb8.prog s
  hc_78019dd8 : CodeAt F_78019dd8.base F_78019dd8.prog s
  hc_78019f50 : CodeAt F_78019f50.base F_78019f50.prog s
  hc_78019ff4 : CodeAt F_78019ff4.base F_78019ff4.prog s
  hc_7801aed0 : CodeAt F_7801aed0.base F_7801aed0.prog s
  hc_7801b4d8 : CodeAt F_7801b4d8.base F_7801b4d8.prog s
  hc_7801beb0 : CodeAt F_7801beb0.base F_7801beb0.prog s
  hc_7801bf3c : CodeAt F_7801bf3c.base F_7801bf3c.prog s
  hc_7801bf4c : CodeAt F_7801bf4c.base F_7801bf4c.prog s
  hc_7801bf5c : CodeAt F_7801bf5c.base F_7801bf5c.prog s
  hc_7801cb44 : CodeAt F_7801cb44.base F_7801cb44.prog s
  hc_7801ce6c : CodeAt F_7801ce6c.base F_7801ce6c.prog s
  hc_7801ce90 : CodeAt F_7801ce90.base F_7801ce90.prog s
  hc_7801d074 : CodeAt F_7801d074.base F_7801d074.prog s
  hc_7801d098 : CodeAt F_7801d098.base F_7801d098.prog s
  hc_7801d2c8 : CodeAt F_7801d2c8.base F_7801d2c8.prog s
  hc_7801d2ec : CodeAt F_7801d2ec.base F_7801d2ec.prog s
  hc_7801d360 : CodeAt F_7801d360.base F_7801d360.prog s
  hc_7801d3d4 : CodeAt F_7801d3d4.base F_7801d3d4.prog s
  hc_7801d51c : CodeAt F_7801d51c.base F_7801d51c.prog s
  hc_7801d92c : CodeAt F_7801d92c.base F_7801d92c.prog s
  hc_7801ddd8 : CodeAt F_7801ddd8.base F_7801ddd8.prog s
  hc_7801e26c : CodeAt F_7801e26c.base F_7801e26c.prog s
  hc_7801e704 : CodeAt F_7801e704.base F_7801e704.prog s
  hc_7801ed68 : CodeAt F_7801ed68.base F_7801ed68.prog s
  hc_7801f120 : CodeAt F_7801f120.base F_7801f120.prog s
  hc_7801f5a4 : CodeAt F_7801f5a4.base F_7801f5a4.prog s
  hc_7801f780 : CodeAt F_7801f780.base F_7801f780.prog s
  hc_7801fb1c : CodeAt F_7801fb1c.base F_7801fb1c.prog s
  hc_7801fbcc : CodeAt F_7801fbcc.base F_7801fbcc.prog s
  hc_7802018c : CodeAt F_7802018c.base F_7802018c.prog s
  hc_780203dc : CodeAt F_780203dc.base F_780203dc.prog s
  hc_78020548 : CodeAt F_78020548.base F_78020548.prog s
  hc_780207e8 : CodeAt F_780207e8.base F_780207e8.prog s
  hc_78020ca0 : CodeAt F_78020ca0.base F_78020ca0.prog s
  hc_78020d50 : CodeAt F_78020d50.base F_78020d50.prog s
  hc_78021238 : CodeAt F_78021238.base F_78021238.prog s
  hc_7802233c : CodeAt F_7802233c.base F_7802233c.prog s
  hc_78022514 : CodeAt F_78022514.base F_78022514.prog s
  hc_780227b4 : CodeAt F_780227b4.base F_780227b4.prog s
  hc_78022848 : CodeAt F_78022848.base F_78022848.prog s
  hc_78022a74 : CodeAt F_78022a74.base F_78022a74.prog s
  hc_78022ca0 : CodeAt F_78022ca0.base F_78022ca0.prog s
  hc_78022f5c : CodeAt F_78022f5c.base F_78022f5c.prog s
  hc_780231e8 : CodeAt F_780231e8.base F_780231e8.prog s
  hc_78023230 : CodeAt F_78023230.base F_78023230.prog s
  hc_78023278 : CodeAt F_78023278.base F_78023278.prog s
  hc_780232f4 : CodeAt F_780232f4.base F_780232f4.prog s
  hc_78023308 : CodeAt F_78023308.base F_78023308.prog s
  hc_7802340c : CodeAt F_7802340c.base F_7802340c.prog s
  hc_780234cc : CodeAt F_780234cc.base F_780234cc.prog s
  hc_78023544 : CodeAt F_78023544.base F_78023544.prog s
  hc_78023594 : CodeAt F_78023594.base F_78023594.prog s
  hc_780235e8 : CodeAt F_780235e8.base F_780235e8.prog s
  hc_780237dc : CodeAt F_780237dc.base F_780237dc.prog s
  hc_78023864 : CodeAt F_78023864.base F_78023864.prog s
  hc_780239bc : CodeAt F_780239bc.base F_780239bc.prog s
  hc_78023a18 : CodeAt F_78023a18.base F_78023a18.prog s
  hc_78023d7c : CodeAt F_78023d7c.base F_78023d7c.prog s
  hc_78023ec4 : CodeAt F_78023ec4.base F_78023ec4.prog s
  hc_78023f64 : CodeAt F_78023f64.base F_78023f64.prog s
  hc_7802413c : CodeAt F_7802413c.base F_7802413c.prog s
  hc_78025164 : CodeAt F_78025164.base F_78025164.prog s
  hc_78025654 : CodeAt F_78025654.base F_78025654.prog s
  hc_78025854 : CodeAt F_78025854.base F_78025854.prog s
  hc_78025a1c : CodeAt F_78025a1c.base F_78025a1c.prog s
  hc_78026258 : CodeAt F_78026258.base F_78026258.prog s
  hc_78026878 : CodeAt F_78026878.base F_78026878.prog s
  hc_78026928 : CodeAt F_78026928.base F_78026928.prog s
  hc_78026b44 : CodeAt F_78026b44.base F_78026b44.prog s
  hc_7802827c : CodeAt F_7802827c.base F_7802827c.prog s
  hc_78028298 : CodeAt F_78028298.base F_78028298.prog s
  hc_78028718 : CodeAt F_78028718.base F_78028718.prog s
  hc_78028b34 : CodeAt F_78028b34.base F_78028b34.prog s
  hc_78028ce8 : CodeAt F_78028ce8.base F_78028ce8.prog s
  hc_78028d04 : CodeAt F_78028d04.base F_78028d04.prog s
  hc_78029468 : CodeAt F_78029468.base F_78029468.prog s
  hc_780297c0 : CodeAt F_780297c0.base F_780297c0.prog s
  hc_78029ae8 : CodeAt F_78029ae8.base F_78029ae8.prog s
  hc_78029b18 : CodeAt F_78029b18.base F_78029b18.prog s
  hc_78029b64 : CodeAt F_78029b64.base F_78029b64.prog s
  hc_78029d94 : CodeAt F_78029d94.base F_78029d94.prog s
  hc_7802e2b4 : CodeAt F_7802e2b4.base F_7802e2b4.prog s
  hc_7802e5b4 : CodeAt F_7802e5b4.base F_7802e5b4.prog s
  hc_7802e8ec : CodeAt F_7802e8ec.base F_7802e8ec.prog s
  hc_7802e9b8 : CodeAt F_7802e9b8.base F_7802e9b8.prog s
  hc_7802ed10 : CodeAt F_7802ed10.base F_7802ed10.prog s
  hc_7802f038 : CodeAt F_7802f038.base F_7802f038.prog s
  hc_7802f358 : CodeAt F_7802f358.base F_7802f358.prog s
  hc_780315c0 : CodeAt F_780315c0.base F_780315c0.prog s
  hc_78031be8 : CodeAt F_78031be8.base F_78031be8.prog s
  hc_78032c1c : CodeAt F_78032c1c.base F_78032c1c.prog s
  hc_78032db4 : CodeAt F_78032db4.base F_78032db4.prog s
  hc_78032fa4 : CodeAt F_78032fa4.base F_78032fa4.prog s
  hc_78033260 : CodeAt F_78033260.base F_78033260.prog s
  hc_78035f88 : CodeAt F_78035f88.base F_78035f88.prog s
  hc_78035fe0 : CodeAt F_78035fe0.base F_78035fe0.prog s
  hc_780360c8 : CodeAt F_780360c8.base F_780360c8.prog s
  hc_780360e0 : CodeAt F_780360e0.base F_780360e0.prog s
  hc_7803a0fc : CodeAt F_7803a0fc.base F_7803a0fc.prog s
  hc_7803a110 : CodeAt F_7803a110.base F_7803a110.prog s
  hc_7803dd28 : CodeAt F_7803dd28.base F_7803dd28.prog s
  hc_7803f54c : CodeAt F_7803f54c.base F_7803f54c.prog s
  hc_7803f57c : CodeAt F_7803f57c.base F_7803f57c.prog s
  hc_78032b38 : CodeAt F_78032b38.base F_78032b38.prog s
  hc_78030a94 : CodeAt F_78030a94.base F_78030a94.prog s
  hc_780326cc : CodeAt F_780326cc.base F_780326cc.prog s
  hc_78032560 : CodeAt F_78032560.base F_78032560.prog s
  hc_78032614 : CodeAt F_78032614.base F_78032614.prog s
  hc_7801cac0 : CodeAt F_7801cac0.base F_7801cac0.prog s
  hc_7801cdb4 : CodeAt F_7801cdb4.base F_7801cdb4.prog s
  hc_78023cbc : CodeAt F_78023cbc.base F_78023cbc.prog s
  hc_7801e110 : CodeAt F_7801e110.base F_7801e110.prog s
  hc_78021e7c : CodeAt F_78021e7c.base F_78021e7c.prog s
  hc_780221a4 : CodeAt F_780221a4.base F_780221a4.prog s
  hc_7802225c : CodeAt F_7802225c.base F_7802225c.prog s
  hc_7801dfb4 : CodeAt F_7801dfb4.base F_7801dfb4.prog s
  hc_78021720 : CodeAt F_78021720.base F_78021720.prog s
  hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s

/-- The premises of `main_spec` that are not about the image: the runtime contracts (the
    allocator at each call site, the `FP_TABLES` build's allocations, `From<io::Error>`) and the
    panic and reject-halt paths. Each mentions the state only through its code. -/
structure RunHyps (G : MachineState → Prop) (n : Nat) (s : MachineState) (I : List (BitVec 8)) : Prop where
  hsq_alloc : SqAlloc G n (Cases.Zip2005.Top.GuestAccepts I) s.code
  hsq_realloc_g : SqReallocG G n (Cases.Zip2005.Top.GuestAccepts I) s.code
  hsq_alloci : SqAllocInv G n (Cases.Zip2005.Top.GuestAccepts I) s.code
  hsq_realloc : SqRealloc G n (Cases.Zip2005.Top.GuestAccepts I) s.code
  hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhandle_al : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpaf_nf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78019da0#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhalt_hint : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035e44#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhalt_empty : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035f14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hfmt : ∀ (u : MachineState) (sp' d : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fa4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78019fa4#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        S.length = 3 → Region d S t → Run.HeapAt L' t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  halloc : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r' → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  halloc_mp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x80#64 →
      u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x80 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 16) :: L') t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hrealloc_mp : ReallocMp G n (Cases.Zip2005.Top.GuestAccepts I) s.code
  hdealloc : ∀ (u : MachineState) (sp' r ptr sz : Word) (k : Nat) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 8#64 → 0x78048980 ≤ ptr.toNat →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  -- `__rust_dealloc` of a hint-area pointer (the records `read_vec` returned)
  hdealloc_hint : ∀ (u : MachineState) (sp' r ptr : Word) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → u.getReg .x10 = ptr → 0x1c00000000 ≤ ptr.toNat →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hdealloc_nf : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 → u.getReg .x12 = 8#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hdealloc_ivk : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
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
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hdealloc_cm : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  -- `P128Pow5T3::constants()` is proved (`constants_contract`): its code (A1) and the allocator's
  -- instance at its call site (A4)
  halloc_c : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78023cf4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x1800#64 →
      u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78023cf4#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 768 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x1800 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 768) :: L') t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  -- `Vec<bool>::from_iter` of `commit_ivk`'s iterator is proved (`from_iter_ivk_contract`); what it
  -- assumes: its code loaded (A1) and the allocator's two instances at its call sites, keeping the
  -- hasher's tables (A4, A5)
  halloc_fi : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      0x78040620 ≤ iptr.toNat → 0x78040620 ≤ tg0.toNat → 0x78040620 ≤ tg1.toNat → 0x78040620 ≤ tg2.toNat →
      0x78040620 ≤ tg3.toNat → IV.length = 138 → G0.length = 1024 → G1.length = 1024 →
      G2.length = 1024 → G3.length = 516 → ∀ (u : MachineState) (sp : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e184#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      RoImage Ro.layout u → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e184#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
      Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
        Disjoint 0x780488a8#64 10 ptr 1 → Disjoint iptr 138 ptr 1 → Disjoint tg0 1024 ptr 1 → Disjoint tg1 1024 ptr 1 → Disjoint tg2 1024 ptr 1 → Disjoint tg3 516 ptr 1 → Run.HeapAt ((ptr, 1) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  -- `RawVec<u8>::reserve`'s slow path in `orchard` is proved (`reserve_or_fi`, `reserve_or_nc`):
  -- its code (A1) and `__rust_realloc`'s two instances under it (A4)
  hrealloc_fi : ReallocOrFi G n (Cases.Zip2005.Top.GuestAccepts I) s.code
  -- `Vec<bool>::from_iter` of `NoteCommitment::derive`'s iterator is proved (`from_iter_nc_contract`):
  -- its code (A1) and the allocator's two instances at its call sites (A4, A5)
  halloc_nc : ∀ (u : MachineState) (sp : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e028#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e028#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 1) :: L') t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hrealloc_nc : ReallocOrNc G n (Cases.Zip2005.Top.GuestAccepts I) s.code

/-- Every premise of `main_spec` that depends on the state only through its code: the loaded
    code and the contracts. It holds of any state with the same code (`RunContracts.of_code_eq`). -/
structure RunContracts (G : MachineState → Prop) (n : Nat) (s : MachineState) (I : List (BitVec 8)) : Prop
    extends RunCode s, RunHyps G n s I

/-- `RunContracts` and the entry state of `main` (A2): its pc, return address, stack, private input
    and the hint area. -/
structure MainAssumptions (G : MachineState → Prop) (n : Nat) (s : MachineState) (ra sp b : Word) (I : List (BitVec 8)) : Prop
    extends RunContracts G n s I where
  hpc : s.pc = 0x78019ff4#64
  hro : RoImage Ro.layout s
  hheap : Run.HeapAt [] s
  hra : s.getReg .x1 = ra
  hra1 : ra &&& ~~~1#64 = ra
  hsp : s.getReg .x2 = sp
  hstk : StackOk Ro.layout 0x3000 sp
  hI : s.privateInput = I
  hIl : I.length < 2 ^ 60
  hB : Region 0x78040618#64 [b] s
  hT0 : Region 0x780488a8#64 [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] s
  hb : 0x1c00000000 ≤ b.toNat
  hokJ : RegionOk Ro.layout.textLo Ro.layout.textHi b 175
  hbI : b.toNat + I.length + 1416 ≤ 0x2000000000

/-- The contracts and code facts depend on the state only through its code. -/
theorem RunContracts.of_code_eq {G : MachineState → Prop} {n : Nat} {s s' : MachineState} {I : List (BitVec 8)} (h : RunContracts G n s I)
    (hc : s'.code = s.code) : RunContracts G n s' I where
  hc_78016938 := codeAt_of_code_eq hc h.hc_78016938
  hc_7801775c := codeAt_of_code_eq hc h.hc_7801775c
  hc_7801806c := codeAt_of_code_eq hc h.hc_7801806c
  hc_7801823c := codeAt_of_code_eq hc h.hc_7801823c
  hc_780191c4 := codeAt_of_code_eq hc h.hc_780191c4
  hc_780197cc := codeAt_of_code_eq hc h.hc_780197cc
  hc_78019918 := codeAt_of_code_eq hc h.hc_78019918
  hc_78019a10 := codeAt_of_code_eq hc h.hc_78019a10
  hc_78019b50 := codeAt_of_code_eq hc h.hc_78019b50
  hc_78019bf0 := codeAt_of_code_eq hc h.hc_78019bf0
  hc_78019cb8 := codeAt_of_code_eq hc h.hc_78019cb8
  hc_78019dd8 := codeAt_of_code_eq hc h.hc_78019dd8
  hc_78019f50 := codeAt_of_code_eq hc h.hc_78019f50
  hc_78019ff4 := codeAt_of_code_eq hc h.hc_78019ff4
  hc_7801aed0 := codeAt_of_code_eq hc h.hc_7801aed0
  hc_7801b4d8 := codeAt_of_code_eq hc h.hc_7801b4d8
  hc_7801beb0 := codeAt_of_code_eq hc h.hc_7801beb0
  hc_7801bf3c := codeAt_of_code_eq hc h.hc_7801bf3c
  hc_7801bf4c := codeAt_of_code_eq hc h.hc_7801bf4c
  hc_7801bf5c := codeAt_of_code_eq hc h.hc_7801bf5c
  hc_7801cb44 := codeAt_of_code_eq hc h.hc_7801cb44
  hc_7801ce6c := codeAt_of_code_eq hc h.hc_7801ce6c
  hc_7801ce90 := codeAt_of_code_eq hc h.hc_7801ce90
  hc_7801d074 := codeAt_of_code_eq hc h.hc_7801d074
  hc_7801d098 := codeAt_of_code_eq hc h.hc_7801d098
  hc_7801d2c8 := codeAt_of_code_eq hc h.hc_7801d2c8
  hc_7801d2ec := codeAt_of_code_eq hc h.hc_7801d2ec
  hc_7801d360 := codeAt_of_code_eq hc h.hc_7801d360
  hc_7801d3d4 := codeAt_of_code_eq hc h.hc_7801d3d4
  hc_7801d51c := codeAt_of_code_eq hc h.hc_7801d51c
  hc_7801d92c := codeAt_of_code_eq hc h.hc_7801d92c
  hc_7801ddd8 := codeAt_of_code_eq hc h.hc_7801ddd8
  hc_7801e26c := codeAt_of_code_eq hc h.hc_7801e26c
  hc_7801e704 := codeAt_of_code_eq hc h.hc_7801e704
  hc_7801ed68 := codeAt_of_code_eq hc h.hc_7801ed68
  hc_7801f120 := codeAt_of_code_eq hc h.hc_7801f120
  hc_7801f5a4 := codeAt_of_code_eq hc h.hc_7801f5a4
  hc_7801f780 := codeAt_of_code_eq hc h.hc_7801f780
  hc_7801fb1c := codeAt_of_code_eq hc h.hc_7801fb1c
  hc_7801fbcc := codeAt_of_code_eq hc h.hc_7801fbcc
  hc_7802018c := codeAt_of_code_eq hc h.hc_7802018c
  hc_780203dc := codeAt_of_code_eq hc h.hc_780203dc
  hc_78020548 := codeAt_of_code_eq hc h.hc_78020548
  hc_780207e8 := codeAt_of_code_eq hc h.hc_780207e8
  hc_78020ca0 := codeAt_of_code_eq hc h.hc_78020ca0
  hc_78020d50 := codeAt_of_code_eq hc h.hc_78020d50
  hc_78021238 := codeAt_of_code_eq hc h.hc_78021238
  hc_7802233c := codeAt_of_code_eq hc h.hc_7802233c
  hc_78022514 := codeAt_of_code_eq hc h.hc_78022514
  hc_780227b4 := codeAt_of_code_eq hc h.hc_780227b4
  hc_78022848 := codeAt_of_code_eq hc h.hc_78022848
  hc_78022a74 := codeAt_of_code_eq hc h.hc_78022a74
  hc_78022ca0 := codeAt_of_code_eq hc h.hc_78022ca0
  hc_78022f5c := codeAt_of_code_eq hc h.hc_78022f5c
  hc_780231e8 := codeAt_of_code_eq hc h.hc_780231e8
  hc_78023230 := codeAt_of_code_eq hc h.hc_78023230
  hc_78023278 := codeAt_of_code_eq hc h.hc_78023278
  hc_780232f4 := codeAt_of_code_eq hc h.hc_780232f4
  hc_78023308 := codeAt_of_code_eq hc h.hc_78023308
  hc_7802340c := codeAt_of_code_eq hc h.hc_7802340c
  hc_780234cc := codeAt_of_code_eq hc h.hc_780234cc
  hc_78023544 := codeAt_of_code_eq hc h.hc_78023544
  hc_78023594 := codeAt_of_code_eq hc h.hc_78023594
  hc_780235e8 := codeAt_of_code_eq hc h.hc_780235e8
  hc_780237dc := codeAt_of_code_eq hc h.hc_780237dc
  hc_78023864 := codeAt_of_code_eq hc h.hc_78023864
  hc_780239bc := codeAt_of_code_eq hc h.hc_780239bc
  hc_78023a18 := codeAt_of_code_eq hc h.hc_78023a18
  hc_78023d7c := codeAt_of_code_eq hc h.hc_78023d7c
  hc_78023ec4 := codeAt_of_code_eq hc h.hc_78023ec4
  hc_78023f64 := codeAt_of_code_eq hc h.hc_78023f64
  hc_7802413c := codeAt_of_code_eq hc h.hc_7802413c
  hc_78025164 := codeAt_of_code_eq hc h.hc_78025164
  hc_78025654 := codeAt_of_code_eq hc h.hc_78025654
  hc_78025854 := codeAt_of_code_eq hc h.hc_78025854
  hc_78025a1c := codeAt_of_code_eq hc h.hc_78025a1c
  hc_78026258 := codeAt_of_code_eq hc h.hc_78026258
  hc_78026878 := codeAt_of_code_eq hc h.hc_78026878
  hc_78026928 := codeAt_of_code_eq hc h.hc_78026928
  hc_78026b44 := codeAt_of_code_eq hc h.hc_78026b44
  hc_7802827c := codeAt_of_code_eq hc h.hc_7802827c
  hc_78028298 := codeAt_of_code_eq hc h.hc_78028298
  hc_78028718 := codeAt_of_code_eq hc h.hc_78028718
  hc_78028b34 := codeAt_of_code_eq hc h.hc_78028b34
  hc_78028ce8 := codeAt_of_code_eq hc h.hc_78028ce8
  hc_78028d04 := codeAt_of_code_eq hc h.hc_78028d04
  hc_78029468 := codeAt_of_code_eq hc h.hc_78029468
  hc_780297c0 := codeAt_of_code_eq hc h.hc_780297c0
  hc_78029ae8 := codeAt_of_code_eq hc h.hc_78029ae8
  hc_78029b18 := codeAt_of_code_eq hc h.hc_78029b18
  hc_78029b64 := codeAt_of_code_eq hc h.hc_78029b64
  hc_78029d94 := codeAt_of_code_eq hc h.hc_78029d94
  hc_7802e2b4 := codeAt_of_code_eq hc h.hc_7802e2b4
  hc_7802e5b4 := codeAt_of_code_eq hc h.hc_7802e5b4
  hc_7802e8ec := codeAt_of_code_eq hc h.hc_7802e8ec
  hc_7802e9b8 := codeAt_of_code_eq hc h.hc_7802e9b8
  hc_7802ed10 := codeAt_of_code_eq hc h.hc_7802ed10
  hc_7802f038 := codeAt_of_code_eq hc h.hc_7802f038
  hc_7802f358 := codeAt_of_code_eq hc h.hc_7802f358
  hc_780315c0 := codeAt_of_code_eq hc h.hc_780315c0
  hc_78031be8 := codeAt_of_code_eq hc h.hc_78031be8
  hc_78032c1c := codeAt_of_code_eq hc h.hc_78032c1c
  hc_78032db4 := codeAt_of_code_eq hc h.hc_78032db4
  hc_78032fa4 := codeAt_of_code_eq hc h.hc_78032fa4
  hc_78033260 := codeAt_of_code_eq hc h.hc_78033260
  hc_78035f88 := codeAt_of_code_eq hc h.hc_78035f88
  hc_78035fe0 := codeAt_of_code_eq hc h.hc_78035fe0
  hc_780360c8 := codeAt_of_code_eq hc h.hc_780360c8
  hc_780360e0 := codeAt_of_code_eq hc h.hc_780360e0
  hc_7803a0fc := codeAt_of_code_eq hc h.hc_7803a0fc
  hc_7803a110 := codeAt_of_code_eq hc h.hc_7803a110
  hc_7803dd28 := codeAt_of_code_eq hc h.hc_7803dd28
  hc_7803f54c := codeAt_of_code_eq hc h.hc_7803f54c
  hc_7803f57c := codeAt_of_code_eq hc h.hc_7803f57c
  hc_78032b38 := codeAt_of_code_eq hc h.hc_78032b38
  hc_78030a94 := codeAt_of_code_eq hc h.hc_78030a94
  hc_780326cc := codeAt_of_code_eq hc h.hc_780326cc
  hc_78032560 := codeAt_of_code_eq hc h.hc_78032560
  hc_78032614 := codeAt_of_code_eq hc h.hc_78032614
  hcw := codeWithin_of_code_eq hc h.hcw
  hsq_alloc := by rw [hc]; exact h.hsq_alloc
  hsq_realloc_g := by rw [hc]; exact h.hsq_realloc_g
  hsq_alloci := by rw [hc]; exact h.hsq_alloci
  hsq_realloc := by rw [hc]; exact h.hsq_realloc
  hpaf := by rw [hc]; exact h.hpaf
  hpp := by rw [hc]; exact h.hpp
  hprz := by rw [hc]; exact h.hprz
  hpb := by rw [hc]; exact h.hpb
  hpanic := by rw [hc]; exact h.hpanic
  hunwrap := by rw [hc]; exact h.hunwrap
  hhandle_rv := by rw [hc]; exact h.hhandle_rv
  hhandle_al := by rw [hc]; exact h.hhandle_al
  hunwrap_opt := by rw [hc]; exact h.hunwrap_opt
  hpaf_nf := by rw [hc]; exact h.hpaf_nf
  hhalt_hint := by rw [hc]; exact h.hhalt_hint
  hhalt_empty := by rw [hc]; exact h.hhalt_empty
  hio := by rw [hc]; exact h.hio
  hfmt := by rw [hc]; exact h.hfmt
  halloc := by rw [hc]; exact h.halloc
  halloc_mp := by rw [hc]; exact h.halloc_mp
  hc_7801cac0 := codeAt_of_code_eq hc h.hc_7801cac0
  hc_7801cdb4 := codeAt_of_code_eq hc h.hc_7801cdb4
  hrealloc_mp := by rw [hc]; exact h.hrealloc_mp
  hdealloc := by rw [hc]; exact h.hdealloc
  hdealloc_hint := by rw [hc]; exact h.hdealloc_hint
  hdealloc_nf := by rw [hc]; exact h.hdealloc_nf
  hdealloc_ivk := by rw [hc]; exact h.hdealloc_ivk
  hdealloc_cm := by rw [hc]; exact h.hdealloc_cm
  hc_78023cbc := codeAt_of_code_eq hc h.hc_78023cbc
  halloc_c := by rw [hc]; exact h.halloc_c
  hc_7801e110 := codeAt_of_code_eq hc h.hc_7801e110
  hc_78021e7c := codeAt_of_code_eq hc h.hc_78021e7c
  halloc_fi := by rw [hc]; exact h.halloc_fi
  hc_780221a4 := codeAt_of_code_eq hc h.hc_780221a4
  hc_7802225c := codeAt_of_code_eq hc h.hc_7802225c
  hrealloc_fi := by rw [hc]; exact h.hrealloc_fi
  hc_7801dfb4 := codeAt_of_code_eq hc h.hc_7801dfb4
  hc_78021720 := codeAt_of_code_eq hc h.hc_78021720
  halloc_nc := by rw [hc]; exact h.halloc_nc
  hrealloc_nc := by rw [hc]; exact h.hrealloc_nc

/-- **The top-level theorem, with its premises bundled.** -/
theorem guest_accepting_run' {G : MachineState → Prop} {n : Nat} (s : MachineState) (ra sp b : Word) (I : List (BitVec 8))
    (h : MainAssumptions G n s ra sp b I) : SafeN G n (Cases.Zip2005.Top.GuestAccepts I) s :=
  guest_accepting_run s ra sp b I h.hpc h.hc_78016938 h.hc_7801775c h.hc_7801806c h.hc_7801823c
    h.hc_780191c4 h.hc_780197cc h.hc_78019918 h.hc_78019a10 h.hc_78019b50 h.hc_78019bf0
    h.hc_78019cb8 h.hc_78019dd8 h.hc_78019f50 h.hc_78019ff4 h.hc_7801aed0 h.hc_7801b4d8
    h.hc_7801beb0 h.hc_7801bf3c h.hc_7801bf4c h.hc_7801bf5c h.hc_7801cb44 h.hc_7801ce6c
    h.hc_7801ce90 h.hc_7801d074 h.hc_7801d098 h.hc_7801d2c8 h.hc_7801d2ec h.hc_7801d360
    h.hc_7801d3d4 h.hc_7801d51c h.hc_7801d92c h.hc_7801ddd8 h.hc_7801e26c h.hc_7801e704
    h.hc_7801ed68 h.hc_7801f120 h.hc_7801f5a4 h.hc_7801f780 h.hc_7801fb1c h.hc_7801fbcc
    h.hc_7802018c h.hc_780203dc h.hc_78020548 h.hc_780207e8 h.hc_78020ca0 h.hc_78020d50
    h.hc_78021238 h.hc_7802233c h.hc_78022514 h.hc_780227b4 h.hc_78022848 h.hc_78022a74
    h.hc_78022ca0 h.hc_78022f5c h.hc_780231e8 h.hc_78023230 h.hc_78023278 h.hc_780232f4
    h.hc_78023308 h.hc_7802340c h.hc_780234cc h.hc_78023544 h.hc_78023594 h.hc_780235e8
    h.hc_780237dc h.hc_78023864 h.hc_780239bc h.hc_78023a18 h.hc_78023d7c h.hc_78023ec4
    h.hc_78023f64 h.hc_7802413c h.hc_78025164 h.hc_78025654 h.hc_78025854 h.hc_78025a1c
    h.hc_78026258 h.hc_78026878 h.hc_78026928 h.hc_78026b44 h.hc_7802827c h.hc_78028298
    h.hc_78028718 h.hc_78028b34 h.hc_78028ce8 h.hc_78028d04 h.hc_78029468 h.hc_780297c0
    h.hc_78029ae8 h.hc_78029b18 h.hc_78029b64 h.hc_78029d94 h.hc_7802e2b4 h.hc_7802e5b4
    h.hc_7802e8ec h.hc_7802e9b8 h.hc_7802ed10 h.hc_7802f038 h.hc_7802f358 h.hc_780315c0
    h.hc_78031be8 h.hc_78032c1c h.hc_78032db4 h.hc_78032fa4 h.hc_78033260 h.hc_78035f88
    h.hc_78035fe0 h.hc_780360c8 h.hc_780360e0 h.hc_7803a0fc h.hc_7803a110 h.hc_7803dd28
    h.hc_7803f54c h.hc_7803f57c h.hc_78032b38 h.hc_78030a94 h.hc_780326cc h.hc_78032560 h.hc_78032614
    h.hcw h.hro h.hheap h.hra h.hra1 h.hsp h.hstk h.hI h.hIl h.hB h.hb h.hokJ
    h.hbI h.hT0 h.hsq_alloc h.hsq_realloc_g h.hsq_alloci h.hsq_realloc h.hpaf h.hpp h.hprz h.hpb h.hpanic h.hunwrap h.hhandle_rv
    h.hhandle_al h.hunwrap_opt h.hpaf_nf h.hhalt_hint h.hhalt_empty h.hio h.hfmt h.halloc
    h.halloc_mp
    (reserve_mp_contract s h.hc_7801cac0 h.hc_7801cdb4 h.hcw h.hrealloc_mp h.hhandle_rv)
    h.hdealloc h.hdealloc_hint h.hdealloc_nf h.hdealloc_ivk h.hdealloc_cm
    (constants_contract s h.hc_78023cbc h.hc_7801aed0 h.hc_7801b4d8 h.hcw h.halloc_c h.hhandle_rv)
    (from_iter_ivk_contract s h.hc_7801e110 h.hc_78021e7c h.hc_7801b4d8 h.hc_7801aed0 h.hcw h.halloc_fi
      h.hc_780221a4 h.hc_7802225c h.hrealloc_fi h.hunwrap_opt h.hhandle_rv)
    (from_iter_nc_contract s h.hc_7801dfb4 h.hc_78021720 h.hc_7801b4d8 h.hc_7801aed0 h.hcw h.halloc_nc
      h.hc_780221a4 h.hc_7802225c h.hrealloc_nc h.hhandle_rv)

end Cases.Zip2005
