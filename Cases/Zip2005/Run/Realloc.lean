/-
  Cases.Zip2005.Run.Realloc

  `__rust_realloc` (`0x7801bd38`) under the run's invariant (milestone M1), growing the live
  list's head.

  The shim calls rlsf's `alloc` for the new size (`heap_alloc`); on null it returns null, the old
  buffer left live but dropped from the list. Otherwise it copies the old size with `memcpy`
  (a functional specification of that length, a premise), frees the old block (`heap_dealloc`)
  and returns the new pointer, which holds the old buffer's words.
-/

import Cases.Zip2005.Run.Discharge
import Cases.Zip2005.Image.F_7801bd38
import Cases.Zip2005.Runtime.MemcpyLoop

set_option maxRecDepth 100000

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Sym Cases.Zip2005 Cases.Zip2005.Image

/-- `heap_alloc` at `__rust_realloc`'s call (`0x7801bd78`), keeping the old buffer `W` and every
    live buffer's bytes. -/
theorem realloc_alloc_core {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    {p0 al : Word} {k0 k1 kc : Nat} {W : List Word} {c : Word → Option Instr} (hcode : c = C)
    (hal : al = 1#64 ∨ al = 8#64) (hk01 : kc ≤ k0) (hk01' : kc ≤ k1) (hk1 : 8 * k1 ≤ 0x78000000)
    (hWl : W.length = kc) (hlo : 0x78048980 ≤ p0.toNat) :
    ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801c18c#64 → u.code = c →
      u.getReg .x1 = 0x7801bd7c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x78040620#64 → u.getReg .x11 = al →
      u.getReg .x12 = BitVec.ofNat 64 (8 * k1) → RoImage Ro.layout u →
      HeapAt ((p0, k0) :: L) u → Region p0 W u →
      (∀ (t : MachineState) (q : Word), t.pc = 0x7801bd7c#64 → CalleeSaved u t →
        t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = q → RoImage Ro.layout t → HeapAt ((q, k1) :: (p0, k0) :: L) t →
        (q = 0#64 ∨ (0x78048980 ≤ q.toNat ∧ q.toNat + 8 * k1 ≤ 0x1c00000000 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi q k1 ∧
          RegionOk Ro.layout.textLo Ro.layout.textHi q kc ∧ Disjoint q kc p0 kc ∧ Region p0 W t)) →
        (∀ r ∈ (p0, k0) :: L, ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
        SafeN G n P t) → SafeN G n P u := by
  intro u sp' h1 h2 h3 h4 h5 h6 h7 h8 hro hh hW k
  have hal' : al &&& (al - 1#64) = 0#64 ∧ al ≠ 0#64 ∧ al < 32#64 := by
    rcases hal with rfl | rfl <;> decide
  have hs1 := h5.lo
  have hs2 : sp'.toNat ≤ 0x78000000 := h5.hi
  have hp0 : p0 ≠ 0#64 := fun e => by rw [e] at hlo; simp at hlo
  have hb := hh.bound (List.mem_cons_self ..)
  refine heap_alloc (k := k1) h1 (h2.trans hcode) (by rw [h4]; omega) (by rw [h4]; omega) h6 h8
    (Nat.le_refl _) (by omega) (by omega) h7 hal'.1 hal'.2.1 hal'.2.2 hro hh ?_
  intro t q hpc' hcs hcode' hpriv hun hx hro' hh' hq hkeep
  rw [h4] at hun
  refine k t q (by rw [hpc', h3]; decide) hcs hcode' hpriv hun hx hro' hh' ?_ hkeep
  rcases hq with hq0 | ⟨hqlo, hqhi⟩
  · exact .inl (BitVec.eq_of_toNat_eq hq0)
  · have hq0 : q ≠ 0#64 := fun e => by rw [e] at hqlo; simp at hqlo
    have hal8 := hh'.aligned (List.mem_cons_self ..)
    have hd := hh'.disjoint (y := (p0, k0)) (List.mem_cons_self ..) hq0 hp0
    have hb0 := hh'.bound (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [TOP] at hqhi hb0
    obtain ⟨hd, _, _⟩ := hd
    dsimp only at hd hb0
    refine .inr ⟨by omega, hqhi, ⟨hal8, ?_, .inr ?_⟩, ⟨hal8, ?_, .inr ?_⟩, ⟨by omega, by omega, by omega⟩,
      Region.kept hW (by omega) (by simp only [TOP] at hb; omega)
        fun a ha => hkeep _ (List.mem_cons_self ..) a hp0 ha⟩ <;>
      simp only [SP1_MAX_MEMORY, Ro.layout_textHi] at * <;> omega

/-- `heap_alloc` at `__rust_realloc`'s call (`0x7801bd78`), keeping the old buffer `W`. -/
theorem realloc_alloc {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    {p0 al : Word} {k0 k1 kc : Nat} {W : List Word} {c : Word → Option Instr} (hcode : c = C)
    (hal : al = 1#64 ∨ al = 8#64) (hk01 : kc ≤ k0) (hk01' : kc ≤ k1) (hk1 : 8 * k1 ≤ 0x78000000)
    (hWl : W.length = kc) (hlo : 0x78048980 ≤ p0.toNat) :
    ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801c18c#64 → u.code = c →
      u.getReg .x1 = 0x7801bd7c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x78040620#64 → u.getReg .x11 = al →
      u.getReg .x12 = BitVec.ofNat 64 (8 * k1) → RoImage Ro.layout u →
      HeapAt ((p0, k0) :: L) u → Region p0 W u →
      (∀ (t : MachineState) (q : Word), t.pc = 0x7801bd7c#64 → CalleeSaved u t →
        t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = q → RoImage Ro.layout t → HeapAt ((q, k1) :: (p0, k0) :: L) t →
        (q = 0#64 ∨ (0x78048980 ≤ q.toNat ∧ q.toNat + 8 * k1 ≤ 0x1c00000000 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi q k1 ∧
          RegionOk Ro.layout.textLo Ro.layout.textHi q kc ∧ Disjoint q kc p0 kc ∧ Region p0 W t)) →
        SafeN G n P t) → SafeN G n P u :=
  fun u sp' h1 h2 h3 h4 h5 h6 h7 h8 hro hh hW k =>
    realloc_alloc_core hcode hal hk01 hk01' hk1 hWl hlo u sp' h1 h2 h3 h4 h5 h6 h7 h8 hro hh hW
      fun t q a1 a2 a3 a4 a5 a6 a7 a8 a9 _ => k t q a1 a2 a3 a4 a5 a6 a7 a8 a9

/-- `heap_dealloc` at `__rust_realloc`'s call (`0x7801bdc4`), keeping the new buffer and every
    live buffer's bytes. -/
theorem realloc_dealloc_core {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    {p0 al : Word} {k0 k1 kc : Nat} {c : Word → Option Instr} (hcode : c = C)
    (hal : al = 1#64 ∨ al = 8#64) (hk01 : kc ≤ k1) (hlo : 0x78048980 ≤ p0.toNat) :
    ∀ (u : MachineState) (sp' q : Word) (V : List Word), V.length = kc →
      u.pc = 0x7801c620#64 → u.code = c →
      u.getReg .x1 = 0x7801bdc8#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' →
      u.getReg .x19 = q → u.getReg .x10 = 0x78040620#64 → u.getReg .x11 = p0 → u.getReg .x12 = al →
      HeapAt ((p0, k0) :: (q, k1) :: L) u → Region q V u → 0x78048980 ≤ q.toNat →
      (∀ t, t.pc = 0x7801bdc8#64 → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        HeapAt ((q, k1) :: L) t → Region q V t →
        (∀ r ∈ (q, k1) :: L, ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
        SafeN G n P t) → SafeN G n P u := by
  intro u sp' q V hV h1 h2 h3 h4 h5 _ h6 h7 h8 hh hV' hq k
  have hs1 := h5.lo
  have hs2 : sp'.toNat ≤ 0x78000000 := h5.hi
  have hp0 : p0 ≠ 0#64 := fun e => by rw [e] at hlo; simp at hlo
  have hq0 : q ≠ 0#64 := fun e => by rw [e] at hq; simp at hq
  have hal31 : al ≤ 31#64 := by rcases hal with rfl | rfl <;> decide
  have hb := hh.bound (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [TOP] at hb
  refine heap_dealloc h1 (h2.trans hcode) (by rw [h4]; omega) (by rw [h4]; omega) h6 h7 hp0 h8 hal31
    hh ?_
  intro t hpc' hcs hcode' hpriv hun hh' hkeep
  rw [h4] at hun
  exact k t (by rw [hpc', h3]; decide) hcs hcode' hpriv hun hh'
    (Region.kept hV' (hV ▸ hk01) (by omega) fun a ha => hkeep _ (List.mem_cons_self ..) a hq0 ha) hkeep

/-- `heap_dealloc` at `__rust_realloc`'s call (`0x7801bdc4`), keeping the new buffer. -/
theorem realloc_dealloc {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    {p0 al : Word} {k0 k1 kc : Nat} {c : Word → Option Instr} (hcode : c = C)
    (hal : al = 1#64 ∨ al = 8#64) (hk01 : kc ≤ k1) (hlo : 0x78048980 ≤ p0.toNat) :
    ∀ (u : MachineState) (sp' q : Word) (V : List Word), V.length = kc →
      u.pc = 0x7801c620#64 → u.code = c →
      u.getReg .x1 = 0x7801bdc8#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' →
      u.getReg .x19 = q → u.getReg .x10 = 0x78040620#64 → u.getReg .x11 = p0 → u.getReg .x12 = al →
      HeapAt ((p0, k0) :: (q, k1) :: L) u → Region q V u → 0x78048980 ≤ q.toNat →
      (∀ t, t.pc = 0x7801bdc8#64 → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        HeapAt ((q, k1) :: L) t → Region q V t → SafeN G n P t) → SafeN G n P u :=
  fun u sp' q V hV h1 h2 h3 h4 h5 h19 h6 h7 h8 hh hV' hq k =>
    realloc_dealloc_core hcode hal hk01 hlo u sp' q V hV h1 h2 h3 h4 h5 h19 h6 h7 h8 hh hV' hq
      fun t a1 a2 a3 a4 a5 a6 a7 _ => k t a1 a2 a3 a4 a5 a6 a7

set_option maxHeartbeats 400000000 in
/-- `memcpy(dst, src, 8 N)`, `N` one or two doublewords, 8-aligned and disjoint. -/
theorem memcpy_small {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word)
    (S : List Word) (N : Nat) (hN : N = 1 ∨ N = 2) (hSl : S.length = N)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = BitVec.ofNat 64 (8 * N))
    (hS : Region src S s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst N)
    (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src N) (hdj : Disjoint dst N src N)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → t.privateInput = s.privateInput →
      Unchanged [(dst, N)] s t → Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hI : s.privateInput = s.privateInput := rfl
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk dst N s
  have hu := Unchanged.refl [(dst, N)] s
  rcases hN with rfl | rfl
  all_goals
    rw [AsmVerif.RiscV.Sym.List.eq_map_range S hSl] at hS
    sym_exec
    sym_close hk
    sym_subst
    exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

/-- The copy at `__rust_realloc`'s `memcpy` call (`0x7801bd9c`): `8 k0` bytes, `k0` one, two or a
    multiple of four doublewords. -/
theorem realloc_copy {G : MachineState → Prop} {n : Nat} {P : Prop} {c : Word → Option Instr}
    (hcode : c = C) {p0 : Word} {k0 : Nat} {W : List Word}
    (hk0 : k0 = 1 ∨ k0 = 2 ∨ (4 ∣ k0 ∧ 4 ≤ k0)) (hWl : W.length = k0)
    (hokP : RegionOk Ro.layout.textLo Ro.layout.textHi p0 k0) :
    ∀ (u : MachineState) (q : Word), u.pc = 0x7801b4d8#64 → u.code = c →
      u.getReg .x1 = 0x7801bda0#64 → u.getReg .x10 = q → u.getReg .x11 = p0 →
      u.getReg .x12 = BitVec.ofNat 64 (8 * k0) → Region p0 W u →
      RegionOk Ro.layout.textLo Ro.layout.textHi q k0 → Disjoint q k0 p0 k0 →
      (∀ t, t.pc = 0x7801bda0#64 → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput → Unchanged [(q, k0)] u t → Region q W t →
        SafeN G n P t) → SafeN G n P u := by
  intro u q h1 h2 h3 h4 h5 h6 hW hokQ hdj k
  have hc : CodeAt F_7801b4d8.base F_7801b4d8.prog u :=
    codeAt_of_image Loaded.codeWF Layout.code_F_7801b4d8 Loaded.memcpy_decode (h2.trans hcode)
  have hcw := codeWithin_C (h2.trans hcode)
  rcases hk0 with h | h | ⟨⟨m, rfl⟩, hm⟩
  · exact memcpy_small u _ q p0 W k0 (.inl h) hWl h1 hc hcw h3 (by decide) h4 h5 h6 hW hokQ hokP hdj k
  · exact memcpy_small u _ q p0 W k0 (.inr h) hWl h1 hc hcw h3 (by decide) h4 h5 h6 hW hokQ hokP hdj k
  · exact memcpy_mul4_spec u _ q p0 W m (by omega) hWl h1 hc hcw h3 (by decide) h4 h5 h6 hokQ hW hokP
      hdj k

/-- The reallocations the run makes, `(old, new, copied)` in doublewords: `Vec<bool>::from_iter`'s
    byte buffers doubling from 8 bytes (to 256 for `commit_ivk`, to 1024 for
    `NoteCommitment::derive`), the `Vec<Fp>`s of `MerklePath` parsing and of the `FP_TABLES` build,
    from `4 n` doublewords to `8 n`, and the build's last table shrunk from 256 elements to 129. -/
def reallocSizes : List (Nat × Nat × Nat) :=
  [(1, 2, 1), (2, 4, 2), (4, 8, 4), (8, 16, 8), (16, 32, 16), (20, 40, 20),
    (24, 48, 24), (28, 56, 28), (32, 64, 32), (36, 72, 36), (40, 80, 40), (44, 88, 44),
    (48, 96, 48), (52, 104, 52), (56, 112, 56), (60, 120, 60), (64, 128, 64), (128, 256, 128),
    (256, 512, 256), (512, 1024, 512), (1024, 516, 516)]

set_option maxHeartbeats 400000000 in
/-- **`__rust_realloc(p0, 8 k0, al, 8 k1)`** of the live list's head, `k0 ≤ k1`: the new buffer
    (null, or in the arena holding the old words) heads the list in place of the old one. -/
theorem heap_realloc {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    (s : MachineState) (ra sp p0 al : Word) (k0 k1 kc : Nat) (W : List Word)
    (hpc : s.pc = 0x7801bd38#64) (hcode : s.code = C)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x60 sp)
    (ha0 : s.getReg .x10 = p0) (ha1 : s.getReg .x11 = BitVec.ofNat 64 (8 * k0))
    (ha2 : s.getReg .x12 = al) (ha3 : s.getReg .x13 = BitVec.ofNat 64 (8 * k1))
    (hal : al = 1#64 ∨ al = 8#64) (hsz : (k0, k1, kc) ∈ reallocSizes)
    (hW : Region p0 W s) (hWl : W.length = kc) (hlo : 0x78048980 ≤ p0.toNat)
    (hro : RoImage Ro.layout s) (hh : HeapAt ((p0, k0) :: L) s)
    (hcpy : ∀ (u : MachineState) (q : Word), u.pc = 0x7801b4d8#64 → u.code = s.code →
      u.getReg .x1 = 0x7801bda0#64 → u.getReg .x10 = q → u.getReg .x11 = p0 →
      u.getReg .x12 = BitVec.ofNat 64 (8 * kc) → Region p0 W u →
      RegionOk Ro.layout.textLo Ro.layout.textHi q kc → Disjoint q kc p0 kc →
      (∀ t, t.pc = 0x7801bda0#64 → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput → Unchanged [(q, kc)] u t → Region q W t →
        SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t : MachineState, t.pc = ra → CalleeSaved s t → t.code = s.code →
      t.privateInput = s.privateInput →
      Unchanged [(sp - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      RoImage Ro.layout t → HeapAt ((t.getReg .x10, k1) :: L) t →
      ((t.getReg .x10).toNat = 0 ∨ (0x78048980 ≤ (t.getReg .x10).toNat ∧ (t.getReg .x10).toNat + 8 * k1 ≤ 0x1c00000000 ∧
        RegionOk Ro.layout.roBase Ro.layout.textHi (t.getReg .x10) k1 ∧ Region (t.getReg .x10) W t)) →
      SafeN G n P t) :
    SafeN G n P s := by
  have hk01 : kc ≤ k0 ∧ kc ≤ k1 ∧ 8 * k1 ≤ 0x78000000 := by
    simp only [reallocSizes, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hsz
    omega
  have hcodeR : CodeAt F_7801bd38.base F_7801bd38.prog s :=
    codeAt_of_image Loaded.codeWF Layout.code_F_7801bd38 F_7801bd38.decode_ok hcode
  have hcw := codeWithin_C hcode
  have hA := realloc_alloc (G := G) (n := n) (P := P) (L := L) (W := W) (c := s.code) hcode hal hk01.1
    hk01.2.1 hk01.2.2 hWl hlo
  have hD := realloc_dealloc (G := G) (n := n) (P := P) (L := L) (p0 := p0) (k0 := k0) (k1 := k1)
    (c := s.code) hcode hal hk01.2.1 hlo
  have hu := Unchanged.refl [(sp - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hI : s.privateInput = s.privateInput := rfl
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hstk.frame 12 (by decide)
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo' := hstk.lo
  have hokF6 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x30#64) 6 s
  have hb0 := hh.bound (List.mem_cons_self ..)
  have hdjF : Disjoint (sp - 0x30#64) 6 p0 kc := by
    have := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    have e : (sp - 0x30#64).toNat = sp.toNat - 0x30 := by
      rw [BitVec.toNat_sub]; simp; omega
    simp only [TOP] at hb0
    unfold AsmVerif.RiscV.Sym.Disjoint; rw [e]; simp at hb0 ⊢; omega
  clear hk01
  simp only [reallocSizes, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hsz
  rcases hsz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    sym_exec [hA, hcpy, hD]
    all_goals sym_close hk
    all_goals rw [hx10]
    all_goals first
      | (rw [hpost] at hcarry; exact hcarry.sublist (List.Sublist.cons_cons _ (List.sublist_cons_self _ _)))
      | exact hcarry.sublist (List.Sublist.cons_cons _ (List.sublist_cons_self _ _))
      | exact hcarry
      | (left; rfl)
      | (right; refine ⟨by assumption, by assumption, by assumption, ?_⟩)
    all_goals
      refine Region.of_eq hR2 ?_
      first
        | rfl
        | (conv => rhs; rw [AsmVerif.RiscV.Sym.List.eq_map_range W hWl]
           rfl)

end Cases.Zip2005.Run
