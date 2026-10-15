import Cases.Zip2005.Curve.FromBytesUnchecked
import Cases.Zip2005.Field.SqOnce
import Cases.Zip2005.Field.SqReserve

/-!
# `EpAffine::from_bytes` building `FP_TABLES`

The first decompression of the run finds the `Once` at `0x780488a8` uninitialised (state `0`):
`from_bytes` builds the tables (`fp_tables_init_spec`) before its `sqrt`. These are the
`from_bytes` specifications from that state; the tables, their contents arbitrary, come out in
the postcondition with the heap that now holds them.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- A block below the arena and a table in it do not overlap. -/
theorem disj_tab {b p : Word} {n k : Nat} (hb : b.toNat + 8 * n ≤ 0x78048980)
    (hp : 0x78048980 ≤ p.toNat) (hp2 : p.toNat + 8 * k ≤ 0x1c00000000) : Disjoint b n p k :=
  ⟨.inl (by omega), by omega, by omega⟩

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `fp_tables_init_spec` with `from_iter`'s growth through `__rust_realloc` (`SqReallocG`), and the
    tables' contents named. -/
theorem fp_tables_init_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp : Word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : Word)
    (hpcS : s.pc = 0x78032b38#64) (hcodeO : CodeAt F_78032b38.base F_78032b38.prog s)
    (hcodeN : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeFI : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMs : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeD : CodeAt F_78032560.base F_78032560.prog s) (hcodeG : CodeAt F_78032614.base F_78032614.prog s)
    (hcwS : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hroS : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x430 sp)
    (ha0 : s.getReg .x10 = 0x780488a8#64)
    (hT : Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] s)
    (halloc : SqAlloc G n P s.code) (hrealloc_g : SqReallocG G n P s.code) (halloci : SqAllocInv G n P s.code)
    (hrealloc : SqRealloc G n P s.code)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    (hk : ∀ (t : MachineState) (iptr tg0 tg1 tg2 tg3 hx : Word) (IV G0 G1 G2 G3 : List Word),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x430#64, 134), (0x780488a8#64, 10), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] s t →
      t.getReg .x10 = 0x780488a8#64 →
      Region 0x780488a8#64 [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64, hx, 2#64] t →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      Region iptr IV t → Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 1104 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 0x1020 ≤ 0x1c00000000 →
      RoImage Ro.layout t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hres : SqReserve G n P s.code := sq_reserve_of_realloc s hcodeD hcodeG hcwS hrealloc_g hhandle_rv
  refine fp_tables_init_spec s ra sp w0 w1 w2 w3 w4 w5 w6 w7 w8 hpcS hcodeO hcodeN hcodeFI hcodeM hcodeSh
    hcodeMs hcodeL hcodeCpy hcwS hroS hheap hra hra1 hsp hstk ha0 hT halloc hres halloci hrealloc
    hhandle_rv hpp hunwrap_opt ?_
  intro t iptr tg0 tg1 tg2 tg3 hx a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
    a21 a22 a23 a24 a25
  obtain ⟨IV, hIV, hIVl⟩ := Region.exists_junk iptr 138 t
  obtain ⟨G0, hG0, hG0l⟩ := Region.exists_junk tg0 1024 t
  obtain ⟨G1, hG1, hG1l⟩ := Region.exists_junk tg1 1024 t
  obtain ⟨G2, hG2, hG2l⟩ := Region.exists_junk tg2 1024 t
  obtain ⟨G3, hG3, hG3l⟩ := Region.exists_junk tg3 516 t
  exact hk t iptr tg0 tg1 tg2 tg3 hx IV G0 G1 G2 G3 a1 a2 a3 a4 a5 a6 hIVl hG0l hG1l hG2l hG3l hIV hG0
    hG1 hG2 hG3 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `EpAffine::from_bytes` (`0x78025a1c`) from the `Once` uninitialised: `ep_affine_from_bytes_spec`'s
    postcondition, and the tables built (their contents arbitrary) into the heap. -/
theorem ep_affine_from_bytes_init_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 w0 w1 w2 w3 w4 w5 w6 w7 w8 : Word) (O : List Word)
    (hOl : O.length = 9)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    {c : Word → Option Instr} (hcc : s.code = c)
    (halloc : SqAlloc G n P c) (hrealloc_g : SqReallocG G n P c) (halloci : SqAllocInv G n P c)
    (hrealloc : SqRealloc G n P c)
    (hpc : s.pc = 0x78025a1c#64) (hcode : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeO : CodeAt F_78032b38.base F_78032b38.prog s)
    (hcodeN : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeFI : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMs : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeD : CodeAt F_78032560.base F_78032560.prog s) (hcodeG : CodeAt F_78032614.base F_78032614.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x6f0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.textLo Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hbelow0 : a0.toNat + 8 * 9 ≤ 0x78040620)
    -- `FP_TABLES`, uninitialised (`Once` state byte 0 at 0x780488f0, padding zero)
    (hT0 : Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] s)
    (hd0 : Disjoint (sp - 0x6f0#64) 222 a0 9) (hd_a1 : Disjoint (sp - 0x6f0#64) 222 a1 4)
    (hd_tb : Disjoint (sp - 0x6f0#64) 222 0x780488a8#64 10)
    (he_a1 : Disjoint a0 9 a1 4) (he_tb : Disjoint a0 9 0x780488a8#64 10)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 : Word) (f : BitVec 8),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x6f0#64, 222), (a0, 9), (0x780488a8#64, 10), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] s t →
      Region a0 [x0, x1, x2, x3, y0, y1, y2, y3, replaceByte O[8]! 0 f] t →
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f →
      ∀ (iptr tg0 tg1 tg2 tg3 hx : Word) (IV G0 G1 G2 G3 : List Word),
      Region 0x780488a8#64 [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64, hx, 2#64] t →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      Region iptr IV t → Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 1104 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 0x1020 ≤ 0x1c00000000 →
      RoImage Ro.layout t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L) t →
      SafeN G n P t) :
    SafeN G n P s := by
  subst hcc
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6f0#64) 222 := hstk.frame 222 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 38 := hokW.sub' 184 38 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 25 := hokF.sub' 0 25 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 25 13 (by decide) (by bv_omega)
  have hok_tb : RegionOk Ro.layout.roBase Ro.layout.textHi 0x780488a8#64 10 := ⟨by decide, by decide, Or.inr (by decide)⟩
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0x130#64) 25 s
  obtain ⟨S, hS, hSl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x6f0#64, 222), (a0, 9), (0x780488a8#64, 10), (0x78040620#64, 4162),
    (0x78048980#64, 14780690128)] s
  have hokTb : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 10 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokAr : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hinit : ∀ (u : MachineState) (ra' sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78032b38#64 →
      u.code = s.code → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x1 = ra' →
      ra' &&& ~~~1#64 = ra' → u.getReg .x2 = sp' → StackOk Ro.layout 0x430 sp' →
      u.getReg .x10 = 0x780488a8#64 → Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] u →
      (∀ (t : MachineState) (iptr tg0 tg1 tg2 tg3 hx : Word) (IV G0 G1 G2 G3 : List Word),
        t.pc = ra' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x430#64, 134), (0x780488a8#64, 10), (0x78040620#64, 4162),
          (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = 0x780488a8#64 →
        Region 0x780488a8#64 [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64, hx, 2#64] t →
        IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
        Region iptr IV t → Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
        RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 →
        RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 →
        RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
        0x78048980 ≤ iptr.toNat → iptr.toNat + 1104 ≤ 0x1c00000000 →
        0x78048980 ≤ tg0.toNat → tg0.toNat + 0x2000 ≤ 0x1c00000000 →
        0x78048980 ≤ tg1.toNat → tg1.toNat + 0x2000 ≤ 0x1c00000000 →
        0x78048980 ≤ tg2.toNat → tg2.toNat + 0x2000 ≤ 0x1c00000000 →
        0x78048980 ≤ tg3.toNat → tg3.toNat + 0x1020 ≤ 0x1c00000000 →
        RoImage Ro.layout t →
        Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t →
        SafeN G n P t) → SafeN G n P u :=
    fun u ra' sp' L' hpcu hcu hrou hhu hrau hra1u hspu hstku ha0u hTu ku =>
      fp_tables_init_spec' u ra' sp' w0 w1 w2 w3 w4 w5 w6 w7 w8 hpcu (codeAt_of_code_eq hcu hcodeO)
        (codeAt_of_code_eq hcu hcodeN) (codeAt_of_code_eq hcu hcodeFI) (codeAt_of_code_eq hcu hcodeM)
        (codeAt_of_code_eq hcu hcodeSh) (codeAt_of_code_eq hcu hcodeMs) (codeAt_of_code_eq hcu hcodeL)
        (codeAt_of_code_eq hcu hcodeCpy) (codeAt_of_code_eq hcu hcodeD) (codeAt_of_code_eq hcu hcodeG)
        (fun a ha => hcw a (hcu ▸ ha)) hrou hhu hrau hra1u hspu hstku ha0u hTu (hcu.symm ▸ halloc)
        (hcu.symm ▸ hrealloc_g) (hcu.symm ▸ halloci) (hcu.symm ▸ hrealloc)
        (fun v sp'' L'' hv hcv => hhandle_rv v sp'' L'' hv (hcv.trans hcu))
        (fun v sp'' L'' hv hcv => hpp v sp'' L'' hv (hcv.trans hcu))
        (fun v sp'' L'' hv hcv => hunwrap_opt v sp'' L'' hv (hcv.trans hcu)) ku
  -- run 1: up to the `sqrt` call
  sym_exec [uint256_mulmod_spec, fp_from_raw_spec, black_box_spec, hpb, hpp, hprz, hinit] stop [0x78026050]
  -- the tables, built, against the frame and the output
  have hfr : (sp - 0x6f0#64).toNat + 8 * 222 ≤ 0x78048980 := by
    have h1 := hstk.lo; have h2 := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    rw [BitVec.toNat_sub]; simp; omega
  have hao : a0.toNat + 8 * 9 ≤ 0x78048980 := by omega
  have hd_iptr := disj_tab (k := 138) hfr post420_32 post420_33
  have hd_g0 := disj_tab (k := 1024) hfr post420_34 post420_35
  have hd_g1 := disj_tab (k := 1024) hfr post420_36 post420_37
  have hd_g2 := disj_tab (k := 1024) hfr post420_38 post420_39
  have hd_g3 := disj_tab (k := 516) hfr post420_40 post420_41
  have he_iptr := disj_tab (k := 138) hao post420_32 post420_33
  have he_g0 := disj_tab (k := 1024) hao post420_34 post420_35
  have he_g1 := disj_tab (k := 1024) hao post420_36 post420_37
  have he_g2 := disj_tab (k := 1024) hao post420_38 post420_39
  have he_g3 := disj_tab (k := 516) hao post420_40 post420_41
  clear hfr hao
  -- the encoding's words, reassembled from bytes
  have hb0 : v40 = b0 := by
    rw [← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v34_def, ← v33_def,
      ← v32_def, ← v31_def, ← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def,
      ← v24_def, ← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def]
    exact bytes_word b0
  have hb1 : v62 = b1 := by
    rw [← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def, ← v56_def, ← v55_def,
      ← v54_def, ← v53_def, ← v52_def, ← v51_def, ← v50_def, ← v49_def, ← v48_def, ← v47_def,
      ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def]
    exact bytes_word b1
  have hb2 : v84 = b2 := by
    rw [← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def,
      ← v76_def, ← v75_def, ← v74_def, ← v73_def, ← v72_def, ← v71_def, ← v70_def, ← v69_def,
      ← v68_def, ← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def]
    exact bytes_word b2
  have hb3 : v108 = b3 := by
    rw [← v108_def, ← v107_def, ← v106_def, ← v105_def, ← v104_def, ← v103_def, ← v100_def,
      ← v99_def, ← v98_def, ← v97_def, ← v96_def, ← v95_def, ← v94_def, ← v93_def, ← v92_def,
      ← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def]
    exact bytes_word b3
  have hhi : v106 = b3 >>> 32 := by
    rw [← v106_def, ← v105_def, ← v104_def, ← v103_def, ← v100_def, ← v99_def, ← v98_def, ← v97_def,
      ← v96_def, ← v95_def]
    exact bytes_word_hi b3
  have hx3 : v116 = b3 &&& 0x7fffffffffffffff#64 := by rw [← v116_def, ← v115_def, hb3, shl1_shr1]
  have hys : bw b3.msb = v113 := by rw [← v113_def, ← v109_def, hhi, sign_word, bb_bw]
  obtain ⟨X, hX⟩ : ∃ X, leLimbsToNat [b0, b1, b2, b3 &&& 0x7fffffffffffffff#64] = X := ⟨_, rfl⟩
  -- the canonical check (`from_repr`, inlined)
  have hXe : X = b0.toNat + 2 ^ 64 * b1.toNat + 2 ^ 128 * b2.toNat +
      2 ^ 192 * (b3 &&& 0x7fffffffffffffff#64).toNat := by
    rw [← hX]; simp only [leLimbsToNat_cons, leLimbsToNat_nil]; ring
  have fl := lt_flag (P0 := 11037532056220336129) (N0 := 7409212017489215487)
    (P1 := 2469829653914515739) (N1 := 15976914419795035877) (by decide) (by decide) (by decide)
    (by decide) v123_def v128_def v129_def v130_def v132_def v133_def v135_def v136_def v137_def
    v138_def v139_def v140_def v141_def v142_def v146_def v147_def
  dsimp only at fl
  rw [show 11037532056220336129 + 2 ^ 64 * 2469829653914515739 + 2 ^ 192 * 2 ^ 62 = Fp.p by decide,
    hb0, hb1, hb2, hx3, ← hXe] at fl
  obtain ⟨canon, hcanon⟩ : ∃ c, decide (X < Fp.p) = c := ⟨_, rfl⟩
  have h201 : bw canon = v201 := by
    rw [← v201_def, ← hcanon]
    by_cases hc : X < Fp.p
    · rw [show v147 = 0#64 from BitVec.eq_of_toNat_eq (fl.1 hc), decide_eq_true hc]; rfl
    · rw [show v147 = 1#64 from BitVec.eq_of_toNat_eq (fl.2 (by omega)), decide_eq_false hc]; rfl
  have h205 : bw canon = v205 := by rw [← v205_def, ← h201, bb_bw]
  have h207 : -(bw canon) = v207 := by rw [← v207_def, ← v206_def, ← h201, bb_bw, and255_bw]
  have h208 : (if canon then v197 else 0#64) = v208 := by rw [← v208_def, ← h207, and_negbw]
  have h209 : (if canon then v198 else 0#64) = v209 := by rw [← v209_def, ← h207, and_negbw]
  have h210 : (if canon then v199 else 0#64) = v210 := by rw [← v210_def, ← h207, and_negbw]
  have h211 : (if canon then v200 else 0#64) = v211 := by rw [← v211_def, ← h207, and_negbw]
  -- `x` in Montgomery form, masked by the flag
  have hXm : acc196_0 = Fp.mul X Fp.R2 := by
    rw [mulpair acc177_0_def acc196_0_def, hb0, hb1, hb2, hx3, hX, Fp.limbs_R2]
  have hXc : leLimbsToNat [v197, v198, v199, v200] = acc196_0 := by
    rw [← v197_def, ← v198_def, ← v199_def, ← v200_def]; exact cells_lt (acc_ltp acc196_0_def)
  obtain ⟨xm, hxm_def⟩ : ∃ m, leLimbsToNat [v208, v209, v210, v211] = m := ⟨_, rfl⟩
  have hxm : (if canon then Fp.mul X Fp.R2 else 0) = xm := by
    rw [← hxm_def, ← h208, ← h209, ← h210, ← h211]
    cases canon
    · simp only [Bool.false_eq_true, if_false]; rfl
    · simp only [if_true]; rw [hXc, hXm]
  -- `x.is_zero()`
  obtain ⟨zero, hzero_def⟩ :
    ∃ z, (v211 == 0#64 && (v210 == 0#64 && (v209 == 0#64 && v208 == 0#64))) = z := ⟨_, rfl⟩
  have h246 : bw zero = v246 := by
    rw [← v246_def, ← v242_def, ← v241_def, ← v237_def, ← v236_def, ← v232_def, ← v231_def,
      ← v227_def, ← v226_def, ← v222_def, ← v221_def, ← v217_def, ← v216_def, ← v212_def,
      ← hzero_def]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw]
  have hzero : zero = true ↔ xm = 0 := by
    rw [← hzero_def, ← hxm_def, limbs_zero4]
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩, fun ⟨a, b, c, d⟩ => ⟨d, c, b, a⟩⟩
  -- the identity case `x.is_zero() & !ysign`, and its negation
  have h247 : bw (!b3.msb) = v247 := by rw [← v247_def, ← v114_def, v113_def, ← hys, not1_bw]
  obtain ⟨ident, hident_def⟩ : ∃ i, (!b3.msb && zero) = i := ⟨_, rfl⟩
  have h256 : bw ident = v256 := by
    rw [← v256_def, ← v252_def, ← v251_def, ← h247, ← h246, bb_bw, and_bw, and255_bw, bb_bw, hident_def]
  have h262 : bw (!ident) = v262 := by
    rw [← v262_def, ← v258_def, ← v257_def, v256_def, ← h256, not1_bw, bb_bw]
  -- `x³ + 5`
  have hsq2 : acc302_0 = Fp.mul xm xm := by rw [mulpair acc281_0_def acc302_0_def, hxm_def]
  have hc302 : leLimbsToNat [v303, v304, v305, v306] = acc302_0 := by
    rw [← v303_def, ← v304_def, ← v305_def, ← v306_def]; exact cells_lt (acc_ltp acc302_0_def)
  have hcube : acc337_0 = Fp.mul (Fp.mul xm xm) xm := by
    rw [mulpair acc324_0_def acc337_0_def, hc302, hsq2, hxm_def]
  have h5 : acc351_0 = Fp.mul 5 Fp.R2 := by
    rw [← acc351_0_def, show leLimbsToNat [5#64, 0#64, 0#64, 0#64] = 5 by decide]
  have hA5 : leLimbsToNat [v352, v353, v354, v355] = acc351_0 := by
    rw [← v352_def, ← v353_def, ← v354_def, ← v355_def]
    exact cells_lt (by rw [← acc351_0_def]; exact Fp.mul_lt _ _)
  have hB3 : leLimbsToNat [v338, v339, v340, v341] = acc337_0 := by
    rw [← v338_def, ← v339_def, ← v340_def, ← v341_def]; exact cells_lt (acc_ltp acc337_0_def)
  have hU : leLimbsToNat [v395, v400, v403, v407] = Fp.rhs xm := by
    rw [fadd_chain v356_def v357_def v358_def v359_def v360_def v361_def v362_def v363_def v364_def
      v365_def v366_def v367_def v368_def v369_def v372_def v374_def v375_def v376_def v379_def
      v380_def v382_def v383_def v384_def v385_def v386_def v387_def v388_def v389_def v391_def
      v392_def v394_def v395_def v396_def v397_def v398_def v399_def v400_def v401_def v402_def
      v403_def v404_def v405_def v406_def v407_def
      (by rw [hA5, h5]; exact Fp.mul_lt _ _) (by rw [hB3]; exact acc_ltp acc337_0_def),
      hA5, hB3, h5, hcube]
    rfl
  have hUlt : leLimbsToNat [v395, v400, v403, v407] < Fp.p := by
    rw [hU]; exact Nat.mod_lt _ Fp.p_pos
  clear hb0 hb1 hb2 hb3 hhi hx3 fl hXe hXm hXc hsq2 hc302 hcube h5 hA5 hB3 h201 h207 h247 h246
  -- a second run from the call site: its own frame fact, the first run's kept aside
  have hU1 : ∀ u, Unchanged [(sp - 0x6f0#64, 222), (a0, 9), (0x780488a8#64, 10), (0x78040620#64, 4162),
      (0x78048980#64, 14780690128)] s_422 u →
      Unchanged [(sp - 0x6f0#64, 222), (a0, 9), (0x780488a8#64, 10), (0x78040620#64, 4162),
      (0x78048980#64, 14780690128)] s u := fun u h => hunch.trans h
  clear hunch
  have hu2 := Unchanged.refl [(sp - 0x6f0#64, 222), (a0, 9), (0x780488a8#64, 10), (0x78040620#64, 4162),
      (0x78048980#64, 14780690128)] s_422
  have hpb' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s_422.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u :=
    fun u sp' L' h1 h2 => hpb u sp' L' h1 (h2.trans hcode)
  have hpp' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s_422.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u :=
    fun u sp' L' h1 h2 => hpp u sp' L' h1 (h2.trans hcode)
  have hprz' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s_422.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u :=
    fun u sp' L' h1 h2 => hprz u sp' L' h1 (h2.trans hcode)
  clear hpb hpp hprz
  have hcodeS : s_422.code = s.code := hcode
  have hro2 : RoImage Ro.layout s_422 := hro
  -- the callee's frame facts against the fixed table address, in the shape the spec states them
  have hd_tb' : Disjoint (sp + 18446744073709551312#64 - 1472#64) 184 0x780488a8#64 9 := by
    rw [AsmVerif.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  have he_tb' : Disjoint (sp + 18446744073709551448#64) 5 0x780488a8#64 9 := by
    rw [AsmVerif.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  -- run 2: from the `sqrt` call to the return
  sym_exec [uint256_mulmod_spec, sqrt_alt_spec, fp_to_repr_spec, black_box_spec, hpb', hpp', hprz']
  -- the square root `R` and its flag `sq`
  obtain ⟨R, hR_def⟩ : ∃ r, leLimbsToNat [post6_1, post6_2, post6_3, post6_4] = r := ⟨_, rfl⟩
  rw [hR_def] at post6_10 post6_11 post6_12
  rw [hU] at post6_11 post6_12
  obtain ⟨sq, hsq_def⟩ : ∃ b, decide (Fp.mul R R = Fp.rhs xm) = b := ⟨_, rfl⟩
  have hv7 : bw sq = v7 := by
    rw [← v7_def, extractByte_replaceByte _ 0 (by decide), hR_def, zext_if8, hsq_def]
  -- the `CtOption` value: `R` under the flag
  obtain ⟨Y, hY_def⟩ : ∃ y, leLimbsToNat [v13, v14, v15, v16] = y := ⟨_, rfl⟩
  have hY : Y = if sq then R else 0 := by
    rw [← hY_def, ← v13_def, ← v14_def, ← v15_def, ← v16_def, ← v12_def, ← hv7, and_negbw, and_negbw,
      and_negbw, and_negbw]
    cases sq
    · simp only [Bool.false_eq_true, if_false]; rfl
    · simp only [if_true]; exact hR_def
  have hYlt : Y < Fp.p := by
    rw [hY]; cases sq
    · simp only [Bool.false_eq_true, if_false]; exact Fp.p_pos
    · simp only [if_true]; exact post6_10
  -- `y.is_odd()`
  have hpar : bw (decide (Fp.fromMont Y % 2 = 1)) = v27 := by
    rw [← v27_def, ← v26_def, ← acc25_0_def, low_bit, hY_def]; rfl
  -- `-y`
  have hneg : leLimbsToNat [v52, v53, v54, v55] = Fp.sub 0 Y := by
    rw [← hY_def]
    exact fneg_chain v31_def v32_def v33_def v34_def v35_def v36_def v38_def v39_def v40_def rfl
      v41_def v42_def v43_def v44_def rfl v46_def v47_def v48_def v49_def v50_def v52_def v53_def
      v54_def v55_def (hY_def ▸ hYlt)
  -- `conditional_select(&y, &-y, ysign ^ sign)`
  obtain ⟨flip, hflip_def⟩ : ∃ f, (decide (Fp.fromMont Y % 2 = 1) != b3.msb) = f := ⟨_, rfl⟩
  have h63 : -(bw flip) = v63 := by
    rw [← v63_def, ← v62_def, ← v58_def, ← v57_def, ← hpar, bb_bw, ← hys, xor_bw, and255_bw, bb_bw,
      and255_bw, hflip_def]
  have hy0 : (if flip then v52 else v13) = v66 := by rw [← v66_def, ← v65_def, ← v64_def, ← h63, sel_bw]
  have hy1 : (if flip then v53 else v14) = v69 := by rw [← v69_def, ← v68_def, ← v67_def, ← h63, sel_bw]
  have hy2 : (if flip then v54 else v15) = v72 := by rw [← v72_def, ← v71_def, ← v70_def, ← h63, sel_bw]
  have hy3 : (if flip then v55 else v16) = v75 := by rw [← v75_def, ← v74_def, ← v73_def, ← h63, sel_bw]
  have hYf : leLimbsToNat [v66, v69, v72, v75] = if flip then Fp.sub 0 Y else Y := by
    rw [← hy0, ← hy1, ← hy2, ← hy3]
    cases flip
    · simp only [Bool.false_eq_true, if_false]; exact hY_def
    · simp only [if_true]; exact hneg
  -- the `CtOption` masks and the final flag
  have hv80 : bw sq = v80 := by rw [← v80_def, ← hv7, and1_bw]
  have hv86 : -(bw (!ident)) = v86 := by rw [← v86_def, ← v85_def, ← h262, and255_bw]
  have hx0 : (if !ident then v208 else 0#64) = v88 := by rw [← v88_def, ← hv86, and_negbw]
  have hx1 : (if !ident then v209 else 0#64) = v89 := by rw [← v89_def, ← hv86, and_negbw]
  have hx2 : (if !ident then v210 else 0#64) = v90 := by rw [← v90_def, ← hv86, and_negbw]
  have hx3 : (if !ident then v211 else 0#64) = v91 := by rw [← v91_def, ← hv86, and_negbw]
  have hy0' : (if !ident then v66 else 0#64) = v92 := by rw [← v92_def, ← hv86, and_negbw]
  have hy1' : (if !ident then v69 else 0#64) = v93 := by rw [← v93_def, ← hv86, and_negbw]
  have hy2' : (if !ident then v72 else 0#64) = v94 := by rw [← v94_def, ← hv86, and_negbw]
  have hy3' : (if !ident then v75 else 0#64) = v95 := by rw [← v95_def, ← hv86, and_negbw]
  have hv105 : -(bw (!ident)) = v105 := by rw [← v105_def, ← h262, sext_neg_bw]
  have hv109 : (if !ident then bw sq else bw ident) = v109 := by
    rw [← v109_def, ← v108_def, ← v107_def, ← hv80, bb_bw, ← h256, ← hv105, sel_bw]
  have hv112 : bw ((if !ident then sq else ident) && canon) = v112 := by
    rw [← v112_def, ← v111_def, ← hv109, ite_bw, ← h205, and_bw, and255_bw]
  rw [← hv112, bb_bw, bw_trunc8] at v116_def
  subst v116_def
  sym_close hk _ _ _ _ _ _ _ _ _ _
  all_goals first | exact hU1 _ hunch | exact hcode.trans hcodeS | skip
  -- the postcondition
  have hxout : leLimbsToNat [if !ident then v208 else 0#64, if !ident then v209 else 0#64,
      if !ident then v210 else 0#64, if !ident then v211 else 0#64] = if !ident then xm else 0 := by
    cases ident
    · simp only [Bool.not_false, if_true]; exact hxm_def
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]; rfl
  have hyout : leLimbsToNat [if !ident then v66 else 0#64, if !ident then v69 else 0#64,
      if !ident then v72 else 0#64, if !ident then v75 else 0#64] =
      if !ident then (if flip then Fp.sub 0 Y else Y) else 0 := by
    cases ident
    · simp only [Bool.not_false, if_true]; exact hYf
    · simp only [Bool.not_true, Bool.false_eq_true, if_false]; rfl
  rw [← hx0, ← hx1, ← hx2, ← hx3, ← hy0', ← hy1', ← hy2', ← hy3', hxout, hyout]
  exact fb_post hX hcanon hxm hzero hident_def post6_10 hsq_def post6_12 hY hflip_def


set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `Ep::from_bytes_unchecked` (`0x78026928`) from the `Once` uninitialised (see
    `ep_affine_from_bytes_init_spec`): `from_bytes`, then `to_curve`. The output is
    the projective point `(x, y, z)` with the flag; `x, y` satisfy `FromBytesPost` (they are
    zeroed under a clear flag, which the postcondition allows) and `z` is `R` (Montgomery one)
    unless `(x, y) = (0, 0)`, the affine identity, where `z = 0`. -/
theorem ep_from_bytes_unchecked_init_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 w0 w1 w2 w3 w4 w5 w6 w7 w8 : Word) (O : List Word)
    (hOl : O.length = 13)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n P u)
    {c : Word → Option Instr} (hcc : s.code = c)
    (halloc : SqAlloc G n P c) (hrealloc_g : SqReallocG G n P c) (halloci : SqAllocInv G n P c)
    (hrealloc : SqRealloc G n P c)
    (hpc : s.pc = 0x78026928#64) (hcode : CodeAt F_78026928.base F_78026928.prog s)
    (hcodeF : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeO : CodeAt F_78032b38.base F_78032b38.prog s)
    (hcodeN : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeFI : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMs : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeD : CodeAt F_78032560.base F_78032560.prog s) (hcodeG : CodeAt F_78032614.base F_78032614.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x7a0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.textLo Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 13)
    (hbelow0 : a0.toNat + 8 * 13 ≤ 0x78040620)
    -- `FP_TABLES`, uninitialised (`Once` state byte 0 at 0x780488f0, padding zero)
    (hT0 : Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] s)
    (hd0 : Disjoint (sp - 0x7a0#64) 244 a0 13) (hd_a1 : Disjoint (sp - 0x7a0#64) 244 a1 4)
    (hd_tb : Disjoint (sp - 0x7a0#64) 244 0x780488a8#64 10)
    (he_a1 : Disjoint a0 13 a1 4) (he_tb : Disjoint a0 13 0x780488a8#64 10)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (f : BitVec 8),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x7a0#64, 244), (a0, 13), (0x780488a8#64, 10), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] s t →
      Region a0 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, replaceByte O[12]! 0 f] t →
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f →
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) →
      ∀ (iptr tg0 tg1 tg2 tg3 hx : Word) (IV G0 G1 G2 G3 : List Word),
      Region 0x780488a8#64 [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64, hx, 2#64] t →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      Region iptr IV t → Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 1104 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 0x1020 ≤ 0x1c00000000 →
      RoImage Ro.layout t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L) t →
      SafeN G n P t) :
    SafeN G n P s := by
  subst hcc
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x7a0#64) 244 := hstk.frame 244 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 22 := hokW.sub' 222 22 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb0#64) 9 := hokF.sub' 0 9 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 9 13 (by decide) (by bv_omega)
  obtain ⟨Sl, hSl, hSll⟩ := Region.exists_junk (sp - 0xb0#64) 9 s
  obtain ⟨Sv, hSv, hSvl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x7a0#64, 244), (a0, 13), (0x780488a8#64, 10), (0x78040620#64, 4162),
    (0x78048980#64, 14780690128)] s
  have hokTb : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 10 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokAr : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hbo : (sp + 18446744073709551440#64).toNat + 8 * 9 ≤ 0x78040620 := by
    have h1 := hstk.lo; have h2 := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    rw [AsmVerif.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide), BitVec.toNat_sub]; simp; omega
  have hlo := hstk.lo
  -- the output region survives the callee (its frame, its output slot), and the callee's frame
  -- facts against the fixed table address: stated in the shapes the executor needs
  have hsurv : Disjoint a0 13 (sp + 18446744073709551440#64 - 1776#64) 222 := by
    rw [AsmVerif.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd0 ⊢
    omega
  have hsurv2 : Disjoint a0 13 (sp + 18446744073709551440#64) 9 := by
    rw [AsmVerif.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd0 ⊢
    omega
  have hd_tb' : Disjoint (sp + 18446744073709551440#64 - 1776#64) 222 0x780488a8#64 10 := by
    rw [AsmVerif.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  have he_tb' : Disjoint (sp + 18446744073709551440#64) 9 0x780488a8#64 10 := by
    rw [AsmVerif.RiscV.Sym.add_ofNat_big _ _ (by decide) (by decide)]
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_sub, BitVec.toNat_ofNat] at hd_tb ⊢
    omega
  sym_exec [ep_affine_from_bytes_init_spec, black_box_spec, hpb, hpp, hprz]
  -- the flag and the `CtOption::map` masks
  have h01 := post18_14.flag01
  obtain ⟨c, hc⟩ : ∃ c, decide (post18_8 = 1#8) = c := ⟨_, rfl⟩
  have hv19e : BitVec.zeroExtend 64 post18_8 = v19 := by
    rw [← v19_def, extractByte_replaceByte _ 0 (by decide)]
  have hv19 : bw c = v19 := by rw [← hv19e, zext_byte01 h01, hc]
  have hv20 : -(bw c) = v20 := by rw [← v20_def, ← hv19]
  have h25 : (if c then post18_0 else 0#64) = v25 := by rw [← v25_def, ← hv20, and_negbw]
  have h26 : (if c then post18_1 else 0#64) = v26 := by rw [← v26_def, ← hv20, and_negbw]
  have h27 : (if c then post18_2 else 0#64) = v27 := by rw [← v27_def, ← hv20, and_negbw]
  have h28 : (if c then post18_3 else 0#64) = v28 := by rw [← v28_def, ← hv20, and_negbw]
  have h33 : (if c then post18_4 else 0#64) = v33 := by rw [← v33_def, ← hv20, and_negbw]
  have h34 : (if c then post18_5 else 0#64) = v34 := by rw [← v34_def, ← hv20, and_negbw]
  have h35 : (if c then post18_6 else 0#64) = v35 := by rw [← v35_def, ← hv20, and_negbw]
  have h36 : (if c then post18_7 else 0#64) = v36 := by rw [← v36_def, ← hv20, and_negbw]
  -- `to_curve`: the identity test through `black_box`
  obtain ⟨xz, hxz⟩ : ∃ z, (v28 == 0#64 && (v27 == 0#64 && (v26 == 0#64 && v25 == 0#64))) = z := ⟨_, rfl⟩
  obtain ⟨yz, hyz⟩ : ∃ z, (v36 == 0#64 && (v35 == 0#64 && (v34 == 0#64 && v33 == 0#64))) = z := ⟨_, rfl⟩
  have h71 : bw xz = v71 := by
    rw [← v71_def, ← v67_def, ← v66_def, ← v62_def, ← v61_def, ← v57_def, ← v56_def, ← v52_def,
      ← v51_def, ← v47_def, ← v46_def, ← v42_def, ← v41_def, ← v37_def, ← hxz]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw]
  have h102 : bw yz = v102 := by
    rw [← v102_def, ← v101_def, ← v97_def, ← v96_def, ← v92_def, ← v91_def, ← v87_def, ← v86_def,
      ← v82_def, ← v81_def, ← v77_def, ← v76_def, ← v72_def, ← hyz]
    simp only [seqz_bw, bb_bw, and_bw, and255_bw]
  have h111 : bw (yz && xz) = v111 := by
    rw [← v111_def, ← v107_def, ← v106_def, ← h102, ← h71, bb_bw, and_bw, and255_bw, bb_bw, and255_bw]
  -- `z`: `R`, or `0` at the identity
  have h119 : (if (yz && xz) then 0#64 else 3780891978758094845#64) = v119 := by
    rw [← v119_def, ← h111, and_notmask]
  have h120 : (if (yz && xz) then 0#64 else 11037255111966004397#64) = v120 := by
    rw [← v120_def, ← h111, and_notmask]
  have h122 : (if (yz && xz) then 0#64 else 4611686018427387903#64) = v122 := by
    rw [← v122_def, ← v121_def, shl2_shr2, ← h111, and_notmask]
  have hz2 : (if (yz && xz) then 0#64 else 18446744073709551615#64) =
      v111 + 18446744073709551615#64 := by
    rw [← h111, bw_add_ones]
  rw [← hv19e, trunc8_zext] at v135_def
  subst v135_def
  sym_close hk _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · rw [← h25, ← h26, ← h27, ← h28, ← h33, ← h34, ← h35, ← h36]
    exact fbu_post post18_14 hc
  · rw [← h119, ← h120, ← h122, ← hz2]
    exact fbu_z hxz hyz


end Cases.Zip2005
