import Cases.Zip2005.Field.SqIterGrow
import Cases.Zip2005.Image.F_78032560
import Cases.Zip2005.Image.F_78032614
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `RawVec<Fp>::reserve`'s slow path (`do_reserve_and_handle`, `finish_grow`), as functions

`pasta_curves`' instances at `0x78032560` / `0x78032614`: a full buffer of `n` elements
(`n ∈ {4, …, 128}`) grows to `2n` through `__rust_realloc(p, 32 n, 8, 64 n)` (the contract
`SqReallocG`, ledger A4). The growth contract `SqReserve` of `from_iter` is then a theorem.
`__rust_realloc` takes at most `0x60` bytes of stack (its own `0x30` and TLSF `alloc`'s `0x30`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- `__rust_realloc(p0, 32 n, 8, 64 n)` at `finish_grow`'s call (`0x7803265c`). -/
def SqReallocG (G : MachineState → Prop) (nb : Nat) (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (u : MachineState) (sp' p0 : Word) (n : Nat) (L' : List (Word × Nat)),
    (n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 ∨ n = 128) →
    u.pc = 0x7801bd38#64 → u.code = code → u.getReg .x1 = 0x7803265c#64 → u.getReg .x2 = sp' →
    StackOk Ro.layout 0x60 sp' → u.getReg .x10 = p0 → u.getReg .x11 = BitVec.ofNat 64 (32 * n) →
    u.getReg .x12 = 8#64 → u.getReg .x13 = BitVec.ofNat 64 (64 * n) → 0x78048980 ≤ p0.toNat →
    RoImage Ro.layout u → Run.HeapAt ((p0, 4 * n) :: L') u →
    (∀ (t : MachineState) (p' : Word), t.pc = 0x7803265c#64 → CalleeSaved u t → t.code = u.code →
      Unchanged [(sp' - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = p' → RegionOk Ro.layout.roBase Ro.layout.textHi p' (8 * n) →
      (p'.toNat = 0 ∨ 0x78048980 ≤ p'.toNat) →
      p'.toNat + 64 * n ≤ 0x1c00000000 → Run.HeapAt ((p', 8 * n) :: L') t → SafeN G nb P t) →
    SafeN G nb P u

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `do_reserve_and_handle` at `from_iter`'s call (returning to `0x78032a24`): the header at
    `sp' + 0x20` doubled, its block grown through `finish_grow`'s `__rust_realloc`. -/
theorem sq_reserve_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp' p0 n : Word) (hpcS : s.pc = 0x78032560#64)
    (hcd : CodeAt F_78032560.base F_78032560.prog s) (hcf : CodeAt F_78032614.base F_78032614.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt ((p0, 4 * n.toNat) :: L) s) (hrealloc : SqReallocG G nb P s.code)
    (hhr : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hra : s.getReg .x1 = 0x78032a24#64) (hsp : s.getReg .x2 = sp') (hstk : StackOk Ro.layout 0x100 sp')
    (ha0 : s.getReg .x10 = sp' + 0x20#64) (ha1 : s.getReg .x11 = n) (ha2 : s.getReg .x12 = 1#64)
    (hR : Region (sp' + 0x20#64) [n, p0, n] s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp' + 0x20#64) 3)
    (hn : n.toNat = 4 ∨ n.toNat = 8 ∨ n.toNat = 16 ∨ n.toNat = 32 ∨ n.toNat = 64 ∨ n.toNat = 128)
    (hplo : 0x78048980 ≤ p0.toNat) (hphi : p0.toNat + 32 * n.toNat ≤ 0x1c00000000)
    (hk : ∀ (t : MachineState) (p' : Word), t.pc = 0x78032a24#64 → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp' - 0x100#64, 32), (sp' + 0x20#64, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region (sp' + 0x20#64) [n + n, p'] t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (8 * n.toNat) →
      0x78048980 ≤ p'.toNat → p'.toNat + 64 * n.toNat ≤ 0x1c00000000 →
      Run.HeapAt ((p', 8 * n.toNat) :: L) t → SafeN G nb P t) :
    SafeN G nb P s := by
  unfold SqReallocG at hrealloc
  have hrea := fun v sp'' p1 m L1 hm hpcv (hcv : v.code = s.code) => hrealloc v sp'' p1 m L1 hm hpcv hcv
  clear hrealloc
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp' - 0x100#64) 32 := hstk.frame 32 (by decide)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokH : RegionOk Ro.layout.roBase Ro.layout.textHi (sp' + 0x20#64) 2 := hokR.sub' 0 2 (by decide) (by simp)
  have hokL : RegionOk Ro.layout.roBase Ro.layout.textHi (sp' + 0x20#64 + 0x10#64) 1 := hokR.sub' 2 1 (by decide) rfl
  have hRa : Region (sp' + 0x20#64) [n, p0] s := hR.sub 0 2 (by simp) rfl
  have hRb : Region (sp' + 0x20#64 + 0x10#64) [n] s := hR.sub 2 1 rfl rfl
  clear hR hokR
  have hu := Unchanged.refl [(sp' - 0x100#64, 32), (sp' + 0x20#64, 2), (0x78040620#64, 4162),
    (0x78048980#64, 14780690128)] s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp' - 0x50#64) 10 := hokS.sub' 22 10 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp' - 0x50#64) 10 s
  obtain ⟨k, hk', rfl⟩ : ∃ k : Nat, (k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32 ∨ k = 64 ∨ k = 128) ∧
      n = BitVec.ofNat 64 k := ⟨n.toNat, hn, BitVec.eq_of_toNat_eq (by simp)⟩
  clear hn
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
  · have hr := fun v sp'' p1 L1 => hrea v sp'' p1 4 L1 (by decide)
    sym_exec [hr, hhr]
    sym_close hk _ post36_0
    exact ‹RegionOk Ro.layout.roBase Ro.layout.textHi post36_0 _›
  · have hr := fun v sp'' p1 L1 => hrea v sp'' p1 8 L1 (by decide)
    sym_exec [hr, hhr]
    sym_close hk _ post36_0
    exact ‹RegionOk Ro.layout.roBase Ro.layout.textHi post36_0 _›
  · have hr := fun v sp'' p1 L1 => hrea v sp'' p1 16 L1 (by decide)
    sym_exec [hr, hhr]
    sym_close hk _ post36_0
    exact ‹RegionOk Ro.layout.roBase Ro.layout.textHi post36_0 _›
  · have hr := fun v sp'' p1 L1 => hrea v sp'' p1 32 L1 (by decide)
    sym_exec [hr, hhr]
    sym_close hk _ post36_0
    exact ‹RegionOk Ro.layout.roBase Ro.layout.textHi post36_0 _›
  · have hr := fun v sp'' p1 L1 => hrea v sp'' p1 64 L1 (by decide)
    sym_exec [hr, hhr]
    sym_close hk _ post36_0
    exact ‹RegionOk Ro.layout.roBase Ro.layout.textHi post36_0 _›
  · have hr := fun v sp'' p1 L1 => hrea v sp'' p1 128 L1 (by decide)
    sym_exec [hr, hhr]
    sym_close hk _ post36_0
    exact ‹RegionOk Ro.layout.roBase Ro.layout.textHi post36_0 _›

/-- `sq_reserve_spec` as `from_iter`'s growth contract `SqReserve`. -/
theorem sq_reserve_of_realloc {G : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState)
    (hcodeD : CodeAt F_78032560.base F_78032560.prog s) (hcodeF : CodeAt F_78032614.base F_78032614.prog s)
    (hcwS : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hrealloc : SqReallocG G nb P s.code)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u) :
    SqReserve G nb P s.code :=
  fun u sp' p0 n _ hpc hc hra hsp hstk ha0 ha1 ha2 hR hokR hn hplo hphi hro hheap hk =>
    sq_reserve_spec u sp' p0 n hpc (codeAt_of_code_eq hc hcodeD) (codeAt_of_code_eq hc hcodeF)
      (fun a ha => hcwS a (hc ▸ ha)) hro hheap (hc ▸ hrealloc)
      (fun v sp'' L'' hv hcv => hhandle_rv v sp'' L'' hv (hcv.trans hc))
      hra hsp hstk ha0 ha1 ha2 hR hokR hn hplo hphi hk

end Cases.Zip2005
