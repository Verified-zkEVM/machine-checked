import Cases.Zip2005.Runtime.ReserveMp
import Cases.Zip2005.Sinsemilla.HasherKept
import Cases.Zip2005.Image.F_780221a4
import Cases.Zip2005.Image.F_7802225c
import Cases.Zip2005.Image.Ro

/-!
# `RawVec<u8>::reserve`'s slow path in `orchard` (0x780221a4, `finish_grow` 0x7802225c)

`do_reserve_and_handle(&v, C, 1, 1, 1)` on a full byte `Vec` of capacity `C` (the two padded
bit iterators' `from_iter`) doubles it through `__rust_realloc(p, C, 1, 2C)`, which keeps the old
contents (ledger A4: `ReallocOrFi` at `commit_ivk`'s call site, also keeping the hasher's six
table regions; `ReallocOrNc` at `NoteCommitment::derive`'s). `reserve_or_fi` and
`reserve_or_nc` are the growth contracts (ledger A5), proved. `do_reserve_and_handle` and
`finish_grow` take `0x30` bytes of stack each, `__rust_realloc` at most `0x60`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- `__rust_realloc(p0, C, 1, 2C)` at `finish_grow`'s call (`0x780222cc`), keeping the six
    hasher regions `T` (in the arena) and returning a block off them. -/
def ReallocOrFi (G : MachineState → Prop) (n : Nat) (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (T : HasherT), Arena6 T → ∀ (u : MachineState) (sp' p0 : Word) (C : Nat) (W : List Word),
    (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256) → W.length = C / 8 →
    u.pc = 0x7801bd38#64 → u.code = code → u.getReg .x1 = 0x780222cc#64 → u.getReg .x2 = sp' →
    StackOk Ro.layout 0x60 sp' → u.getReg .x10 = p0 → u.getReg .x11 = BitVec.ofNat 64 C →
    u.getReg .x12 = 1#64 → u.getReg .x13 = BitVec.ofNat 64 (2 * C) →
    Region p0 W u → 0x78048980 ≤ p0.toNat → p0.toNat + C ≤ 0x1c00000000 →
    Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u →
    Region T.b5 T.L5 u → Region T.b6 T.L6 u →
    (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x780222cc#64 → CalleeSaved u t →
      t.code = u.code →
      Unchanged [(sp' - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = p' → W'.length = C / 8 + 1 → Region p' (W ++ W') t →
      RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) → 0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
      Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t →
      Region T.b5 T.L5 t → Region T.b6 T.L6 t →
      AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) →
      AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) →
      AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → SafeN G n P t) →
    SafeN G n P u

/-- `__rust_realloc(p0, C, 1, 2C)` at `finish_grow`'s call (`0x780222cc`), `NoteCommitment::derive`'s
    capacities. -/
def ReallocOrNc (G : MachineState → Prop) (n : Nat) (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (u : MachineState) (sp' p0 : Word) (C : Nat) (W : List Word),
    (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024) → W.length = C / 8 →
    u.pc = 0x7801bd38#64 → u.code = code → u.getReg .x1 = 0x780222cc#64 → u.getReg .x2 = sp' →
    StackOk Ro.layout 0x60 sp' → u.getReg .x10 = p0 → u.getReg .x11 = BitVec.ofNat 64 C →
    u.getReg .x12 = 1#64 → u.getReg .x13 = BitVec.ofNat 64 (2 * C) →
    Region p0 W u → 0x78048980 ≤ p0.toNat → p0.toNat + C ≤ 0x1c00000000 →
    (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x780222cc#64 → CalleeSaved u t →
      t.code = u.code →
      Unchanged [(sp' - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = p' → W'.length = C / 8 + 1 → Region p' (W ++ W') t →
      RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) → 0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
      SafeN G n P t) →
    SafeN G n P u

theorem toNat_sp_hdr {sp : Word} (h : StackOk Ro.layout 0x100 sp) :
    AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 sp 3 := by
  obtain ⟨_, h2, h3⟩ := h
  rw [Ro.layout_stackTop] at h3
  unfold AsmVerif.RiscV.Sym.Disjoint
  simp only [BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `do_reserve_and_handle(hdr, C, 1, 1, 1)` on a full byte `Vec` of capacity `C`, its header in
    the caller's frame at `sp`: the block doubled through `finish_grow`'s `__rust_realloc`. -/
theorem reserve_or_fi_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState) (sp ra : Word) (C : Nat) (p : Word) (W : List Word)
    (T : HasherT) (hTA : Arena6 T)
    (hpcS : s.pc = 0x780221a4#64)
    (hcd : CodeAt F_780221a4.base F_780221a4.prog s) (hcf : CodeAt F_7802225c.base F_7802225c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hrealloc : ReallocOrFi G nb P s.code)
    (hhr : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G nb P u)
    (hC : C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256) (hWl : W.length = C / 8)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra) (hsp : s.getReg .x2 = sp)
    (hstk : StackOk Ro.layout 0x100 sp) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3) (ha0 : s.getReg .x10 = sp)
    (ha1 : s.getReg .x11 = BitVec.ofNat 64 C) (ha2 : s.getReg .x12 = 1#64) (ha3 : s.getReg .x13 = 1#64)
    (ha4 : s.getReg .x14 = 1#64) (hH : Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] s)
    (hW : Region p W s) (hplo : 0x78048980 ≤ p.toNat) (hphi : p.toNat + C ≤ 0x1c00000000)
    (hr1 : Region T.b1 T.L1 s) (hr2 : Region T.b2 T.L2 s) (hr3 : Region T.b3 T.L3 s)
    (hr4 : Region T.b4 T.L4 s) (hr5 : Region T.b5 T.L5 s) (hr6 : Region T.b6 T.L6 s)
    (hk : ∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = ra → CalleeSaved s t →
        t.code = s.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t →
        Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) →
        AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) →
        AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → SafeN G nb P t) :
    SafeN G nb P s := by
  have hrea := fun v sp'' p1 W1 hW1 hpcv (hcv : v.code = s.code) =>
    hrealloc T hTA v sp'' p1 C W1 hC hW1 hpcv hcv
  clear hrealloc
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x100#64) 32 := hstk.frame 32 (by decide)
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hdSH : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp - 0x100#64) 32 :=
    Disjoint.heap_frame (n := 32) hstk (by decide)
  have hdHH := toNat_sp_hdr hstk
  have hdF : Away6 (sp - 0x100#64) 32 T := Away6.of_heap hTA hdSH
  have hdV : Away6 sp 3 T := Away6.of_heap hTA hdHH
  have hdF1 := hdF.d1
  have hdF2 := hdF.d2
  have hdF3 := hdF.d3
  have hdF4 := hdF.d4
  have hdF5 := hdF.d5
  have hdF6 := hdF.d6
  have hdV1 := hdV.d1
  have hdV2 := hdV.d2
  have hdV3 := hdV.d3
  have hdV4 := hdV.d4
  have hdV5 := hdV.d5
  have hdV6 := hdV.d6
  have hl1 := T.l1
  have hl2 := T.l2
  have hl3 := T.l3
  have hl4 := T.l4
  have hl5 := T.l5
  have hl6 := T.l6
  clear hdF hdV
  -- the header as the cells the callee writes (`cap`, `ptr`) and the one it keeps (`len`)
  have hH0 : Region sp [BitVec.ofNat 64 C, p] s := hH.take 2
  have hH2 : Region (sp + 0x10#64) [BitVec.ofNat 64 C] s := hH.shift 2
  have hokH0 : RegionOk Ro.layout.roBase Ro.layout.textHi sp 2 := hokH.sub' 0 2 (by decide) (by simp)
  have hokH2 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x10#64) 1 := hokH.sub' 2 1 (by decide) rfl
  clear hH hokH
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hokS.sub' 20 12 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x60#64) 12 s
  have hu := Unchanged.refl [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 8), post54_0, BitVec.ofNat 64 8] s_79 := Region.append hR7 hR8
    clear hR7 hR8
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 3) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 16), post54_0, BitVec.ofNat 64 16] s_79 := Region.append hR7 hR8
    clear hR7 hR8
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 5) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 32), post54_0, BitVec.ofNat 64 32] s_79 := Region.append hR7 hR8
    clear hR7 hR8
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 9) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 64), post54_0, BitVec.ofNat 64 64] s_79 := Region.append hR7 hR8
    clear hR7 hR8
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 17) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 128), post54_0, BitVec.ofNat 64 128] s_79 := Region.append hR7 hR8
    clear hR7 hR8
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 33) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 256), post54_0, BitVec.ofNat 64 256] s_79 := Region.append hR7 hR8
    clear hR7 hR8
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 65) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm

/-- `reserve_or_fi_spec` as its callers' contract (ledger A5). -/
theorem reserve_or_fi {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (hcodeD : CodeAt F_780221a4.base F_780221a4.prog s) (hcodeF : CodeAt F_7802225c.base F_7802225c.prog s)
    (hcwS : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hrealloc : ReallocOrFi G n P s.code)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G n P u)
    (T : HasherT) (hTA : Arena6 T) :
    ∀ (u : MachineState) (sp ra : Word) (C : Nat) (p : Word) (W : List Word),
      (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256) → W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = s.code → u.getReg .x1 = ra → ra &&& ~~~1#64 = ra →
      u.getReg .x2 = sp → StackOk Ro.layout 0x100 sp → RegionOk Ro.layout.roBase Ro.layout.textHi sp 3 → u.getReg .x10 = sp →
      u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u →
      Region T.b5 T.L5 u → Region T.b6 T.L6 u →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = ra → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t →
        Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) →
        AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) →
        AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → SafeN G n P t) →
      SafeN G n P u :=
  fun u sp ra C p W hC hWl hpc hc hra hra1 hsp hstk hokH ha0 ha1 ha2 ha3 ha4 hH hW hplo hphi r1 r2 r3 r4 r5 r6 hk =>
    reserve_or_fi_spec u sp ra C p W T hTA hpc (codeAt_of_code_eq hc hcodeD)
      (codeAt_of_code_eq hc hcodeF) (fun a ha => hcwS a (hc ▸ ha)) (hc ▸ hrealloc)
      (fun v hv hcv => hhandle_rv v hv (hcv.trans hc)) hC hWl hra hra1 hsp hstk hokH ha0 ha1 ha2 ha3 ha4
      hH hW hplo hphi r1 r2 r3 r4 r5 r6 hk

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `do_reserve_and_handle(hdr, C, 1, 1, 1)` on a full byte `Vec` of capacity `C`, its header in
    the caller's frame at `sp`: the block doubled through `finish_grow`'s `__rust_realloc`. -/
theorem reserve_or_nc_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState) (sp ra : Word) (C : Nat) (p : Word) (W : List Word)
    (hpcS : s.pc = 0x780221a4#64)
    (hcd : CodeAt F_780221a4.base F_780221a4.prog s) (hcf : CodeAt F_7802225c.base F_7802225c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hrealloc : ReallocOrNc G nb P s.code)
    (hhr : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G nb P u)
    (hC : C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024) (hWl : W.length = C / 8)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra) (hsp : s.getReg .x2 = sp)
    (hstk : StackOk Ro.layout 0x100 sp) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3) (ha0 : s.getReg .x10 = sp)
    (ha1 : s.getReg .x11 = BitVec.ofNat 64 C) (ha2 : s.getReg .x12 = 1#64) (ha3 : s.getReg .x13 = 1#64)
    (ha4 : s.getReg .x14 = 1#64) (hH : Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] s)
    (hW : Region p W s) (hplo : 0x78048980 ≤ p.toNat) (hphi : p.toNat + C ≤ 0x1c00000000)
    (hk : ∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = ra → CalleeSaved s t →
        t.code = s.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        SafeN G nb P t) :
    SafeN G nb P s := by
  have hrea := fun v sp'' p1 W1 hW1 hpcv (hcv : v.code = s.code) =>
    hrealloc v sp'' p1 C W1 hC hW1 hpcv hcv
  clear hrealloc
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x100#64) 32 := hstk.frame 32 (by decide)
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hdHH := toNat_sp_hdr hstk
  have hH0 : Region sp [BitVec.ofNat 64 C, p] s := hH.take 2
  have hH2 : Region (sp + 0x10#64) [BitVec.ofNat 64 C] s := hH.shift 2
  have hokH0 : RegionOk Ro.layout.roBase Ro.layout.textHi sp 2 := hokH.sub' 0 2 (by decide) (by simp)
  have hokH2 : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x10#64) 1 := hokH.sub' 2 1 (by decide) rfl
  clear hH hokH
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hokS.sub' 20 12 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x60#64) 12 s
  have hu := Unchanged.refl [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 8), post54_0, BitVec.ofNat 64 8] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 3) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 16), post54_0, BitVec.ofNat 64 16] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 5) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 32), post54_0, BitVec.ofNat 64 32] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 9) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 64), post54_0, BitVec.ofNat 64 64] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 17) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 128), post54_0, BitVec.ofNat 64 128] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 33) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 256), post54_0, BitVec.ofNat 64 256] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 65) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 512), post54_0, BitVec.ofNat 64 512] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    refine (cells_eq_append (n := 129) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7])).trans ?_
    congr 1; exact (AsmVerif.RiscV.Sym.List.eq_map_range W hWl).symm
  · sym_exec [hrea, hhr]
    have hRH : Region sp [BitVec.ofNat 64 (2 * 1024), post54_0, BitVec.ofNat 64 1024] s_79 := Region.append hR1 hR2
    clear hR1 hR2
    sym_close hk _ post54_0 post54_1
    exact cells_eq_append (n := 257) acc54_0_def (by rw [← acc54_0_def]; simp [post54_7, hWl])

/-- `reserve_or_nc_spec` as its callers' contract (ledger A5). -/
theorem reserve_or_nc {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (hcodeD : CodeAt F_780221a4.base F_780221a4.prog s) (hcodeF : CodeAt F_7802225c.base F_7802225c.prog s)
    (hcwS : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hrealloc : ReallocOrNc G n P s.code)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G n P u) :
    ∀ (u : MachineState) (sp ra : Word) (C : Nat) (p : Word) (W : List Word),
      (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024) → W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = s.code → u.getReg .x1 = ra → ra &&& ~~~1#64 = ra →
      u.getReg .x2 = sp → StackOk Ro.layout 0x100 sp → RegionOk Ro.layout.roBase Ro.layout.textHi sp 3 → u.getReg .x10 = sp →
      u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = ra → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        SafeN G n P t) →
      SafeN G n P u :=
  fun u sp ra C p W hC hWl hpc hc hra hra1 hsp hstk hokH ha0 ha1 ha2 ha3 ha4 hH hW hplo hphi hk =>
    reserve_or_nc_spec u sp ra C p W hpc (codeAt_of_code_eq hc hcodeD)
      (codeAt_of_code_eq hc hcodeF) (fun a ha => hcwS a (hc ▸ ha)) (hc ▸ hrealloc)
      (fun v hv hcv => hhandle_rv v hv (hcv.trans hc)) hC hWl hra hra1 hsp hstk hokH ha0 ha1 ha2 ha3 ha4
      hH hW hplo hphi hk


end Cases.Zip2005
