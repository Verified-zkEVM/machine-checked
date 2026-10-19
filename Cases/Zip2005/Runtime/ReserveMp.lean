import MachineChecked.RiscV.Sym
import Cases.Zip2005.Runtime.Heap
import Mathlib.Tactic.IntervalCases
import Cases.Zip2005.Image.F_7801cac0
import Cases.Zip2005.Image.F_7801cdb4
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `RawVec<Fp>::reserve`'s slow path in `zip_2005_lib` (0x7801cac0, `finish_grow` 0x7801cdb4)

The full `Vec` of `n` elements (`4 ≤ n ≤ 16`, 32 bytes each) grows to `2n` through
`__rust_realloc(p, 32 n, 8, 64 n)`, which keeps the old contents (the contract `ReallocMp`,
ledger A4). `reserve_mp_contract` is the growth contract `hreserve` (ledger A5), proved.
`__rust_realloc` takes at most `0x60` bytes of stack (its own `0x30` and TLSF `alloc`'s `0x30`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- `__rust_realloc(p0, 32 n, 8, 64 n)` at `finish_grow`'s call (`0x7801cdfc`): null, or a block
    of `64 n` bytes holding the old `32 n`; the old block leaves the live list, the new one enters. -/
def ReallocMp (G : MachineState → Prop) (nb : Nat) (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (u : MachineState) (sp' p0 : Word) (n : Nat) (B : List Word) (L' : List (Word × Nat)), 4 ≤ n → n ≤ 16 →
    u.pc = 0x7801bd38#64 → u.code = code → u.getReg .x1 = 0x7801cdfc#64 → u.getReg .x2 = sp' →
    StackOk Ro.layout 0x60 sp' → u.getReg .x10 = p0 → u.getReg .x11 = BitVec.ofNat 64 (32 * n) →
    u.getReg .x12 = 8#64 → u.getReg .x13 = BitVec.ofNat 64 (64 * n) →
    B.length = 4 * n → Region p0 B u → 0x78048980 ≤ p0.toNat → p0.toNat + 32 * n ≤ 0x1c00000000 →
    RoImage Ro.layout u → Run.HeapAt ((p0, 4 * n) :: L') u →
    (∀ (t : MachineState) (p' : Word) (B' : List Word), t.pc = 0x7801cdfc#64 → CalleeSaved u t →
      t.code = u.code →
      Unchanged [(sp' - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = p' → B'.length = 4 * n →
      RegionOk Ro.layout.roBase Ro.layout.textHi p' (8 * n) → p'.toNat + 64 * n ≤ 0x1c00000000 →
      (p'.toNat = 0 ∨ (0x78048980 ≤ p'.toNat ∧ Region p' (B ++ B') t)) →
      Run.HeapAt ((p', 8 * n) :: L') t → SafeN G nb P t) →
    SafeN G nb P u

/-- A block the executor holds cell by cell is the list it was made from. -/
theorem cells_eq_append {B B' A : List Word} {n : Nat} (hA : B ++ B' = A) (hlen : A.length = n) :
    (List.range n).map (fun i => A[i]!) = B ++ B' := by
  rw [hA]; exact (MachineChecked.RiscV.Sym.List.eq_map_range A hlen).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `do_reserve_and_handle(hdr, n)` on a full `Vec<Fp>` of `n` elements (`4 ≤ n ≤ 16`), returning
    to `0x7801d1e8`: the block doubled through `finish_grow`'s `__rust_realloc`. -/
theorem reserve_mp_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp' hdr ptr : Word) (n : Nat) (B : List Word)
    (hpcS : s.pc = 0x7801cac0#64)
    (hcd : CodeAt F_7801cac0.base F_7801cac0.prog s) (hcf : CodeAt F_7801cdb4.base F_7801cdb4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt ((ptr, 4 * n) :: L) s) (hrealloc : ReallocMp G nb P s.code)
    (hhr : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hra : s.getReg .x1 = 0x7801d1e8#64) (hsp : s.getReg .x2 = sp')
    (hstk : StackOk Ro.layout 0x100 sp') (ha0 : s.getReg .x10 = hdr) (ha1 : s.getReg .x11 = BitVec.ofNat 64 n)
    (hR : Region hdr [BitVec.ofNat 64 n, ptr, BitVec.ofNat 64 n] s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi hdr 3)
    (hdS : Disjoint (sp' - 0x100#64) 32 hdr 3) (hdH : Disjoint 0x78040620#64 14780694332 hdr 3)
    (hn4 : 4 ≤ n) (hn16 : n ≤ 16) (hBl : B.length = 4 * n) (hB : Region ptr B s)
    (hplo : 0x78048980 ≤ ptr.toNat) (hphi : ptr.toNat + 32 * n ≤ 0x1c00000000)
    (hk : ∀ (t : MachineState) (ptr' : Word) (B' : List Word), t.pc = 0x7801d1e8#64 → CalleeSaved s t →
        t.code = s.code → Unchanged [(sp' - 0x100#64, 32), (hdr, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
        Region hdr [BitVec.ofNat 64 (2 * n), ptr', BitVec.ofNat 64 n] t → B'.length = 4 * n →
        Region ptr' (B ++ B') t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr' (8 * n) → 0x78048980 ≤ ptr'.toNat →
        ptr'.toNat + 64 * n ≤ 0x1c00000000 → Run.HeapAt ((ptr', 8 * n) :: L) t → SafeN G nb P t) :
    SafeN G nb P s := by
  unfold ReallocMp at hrealloc
  have hrea := fun v sp'' p1 m B1 L1 h1 h2 hpcv (hcv : v.code = s.code) => hrealloc v sp'' p1 m B1 L1 h1 h2 hpcv hcv
  clear hrealloc
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp' - 0x100#64) 32 := hstk.frame 32 (by decide)
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp' - 0x50#64) 10 := hokS.sub' 22 10 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp' - 0x50#64) 10 s
  have hu := Unchanged.refl [(sp' - 0x100#64, 32), (hdr, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hr := fun v sp'' p1 B1 L1 => hrea v sp'' p1 n B1 L1 hn4 hn16
  clear hrea
  interval_cases n
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 32) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 40) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 48) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 56) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 64) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 72) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 80) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 88) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 96) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 104) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 112) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 120) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm
  · sym_exec [hr, hhr]
    sym_close hk _ post36_0 post36_1
    refine (cells_eq_append (n := 128) acc36_0_def (by rw [← acc36_0_def]; simp [post36_7])).trans ?_
    congr 1; exact (MachineChecked.RiscV.Sym.List.eq_map_range B hBl).symm

/-- `reserve_mp_spec` as its callers' contract (`hreserve`, ledger A5). -/
theorem reserve_mp_contract {G : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState)
    (hcodeD : CodeAt F_7801cac0.base F_7801cac0.prog s) (hcodeF : CodeAt F_7801cdb4.base F_7801cdb4.prog s)
    (hcwS : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hrealloc : ReallocMp G nb P s.code)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u) :
    ∀ (u : MachineState) (sp' hdr ptr : Word) (n : Nat) (B : List Word) (L' : List (Word × Nat)),
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
        ptr'.toNat + 64 * n ≤ 0x1c00000000 → Run.HeapAt ((ptr', 8 * n) :: L') t → SafeN G nb P t) →
      SafeN G nb P u :=
  fun u sp' hdr ptr n B _ hpc hc hra hsp hstk ha0 ha1 hR hokR hdS hdH hn4 hn16 hBl hB hplo hphi hro hheap hk =>
    reserve_mp_spec u sp' hdr ptr n B hpc (codeAt_of_code_eq hc hcodeD) (codeAt_of_code_eq hc hcodeF)
      (fun a ha => hcwS a (hc ▸ ha)) hro hheap (hc ▸ hrealloc)
      (fun v sp'' L'' hv hcv => hhandle_rv v sp'' L'' hv (hcv.trans hc))
      hra hsp hstk ha0 ha1 hR hokR hdS hdH hn4 hn16 hBl hB hplo hphi hk

end Cases.Zip2005
