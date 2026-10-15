/-
  Cases.Zip2005.Run.ReallocOr

  `__rust_realloc`'s contracts at `RawVec<u8>::reserve`'s `finish_grow` in `orchard`, discharged
  (milestone M1): `ReallocOrNc` (`NoteCommitment::derive`'s `Vec<bool>`) from `heap_realloc`,
  and `ReallocOrFi` (`commit_ivk`'s, the hasher's tables kept) from `heap_realloc6`.
-/

import Cases.Zip2005.Run.ReallocContracts
import Cases.Zip2005.Runtime.ReserveOr

set_option maxRecDepth 100000

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Sym Cases.Zip2005 Cases.Zip2005.Image
  Cases.Zip2005.Runtime

/-- A table off the head's block: `Disjoint` from a live entry, shrunk to `k0 ≤ k1` words. -/
theorem table_apart {x : Word × Nat} {L : List (Word × Nat)} {t : MachineState}
    (h : HeapAt (x :: L) t) {b : Word} {m : Nat} (hm : (b, m) ∈ L) (hb : 0x78040620 ≤ b.toNat)
    (hx : 0x78048980 ≤ x.1.toNat) {k0 : Nat} (hk : k0 ≤ x.2) : Disjoint b m x.1 k0 := by
  have hd := h.disjoint hm (fun e => by rw [e] at hx; simp at hx) (fun e => by
    dsimp only at e; rw [e] at hb; simp at hb)
  obtain ⟨hd, h1, h2⟩ := hd
  dsimp only at hd h1 h2
  exact ⟨by omega, by omega, by omega⟩

/-- `realloc_alloc`, also keeping the hasher's five heap tables. -/
theorem realloc_alloc6 {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    {p0 al : Word} {k0 k1 : Nat} {W : List Word} {c : Word → Option Instr} (hcode : c = C)
    (T : HasherT) (hT : Arena6 T)
    (hal : al = 1#64 ∨ al = 8#64) (hk01 : k0 ≤ k1) (hk1 : 8 * k1 ≤ 0x78000000)
    (hWl : W.length = k0) (hlo : 0x78048980 ≤ p0.toNat) :
    ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801c18c#64 → u.code = c →
      u.getReg .x1 = 0x7801bd7c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x78040620#64 → u.getReg .x11 = al →
      u.getReg .x12 = BitVec.ofNat 64 (8 * k1) → RoImage Ro.layout u →
      HeapAt ((p0, k0) :: T.live L) u → Region p0 W u →
      Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u →
      Region T.b6 T.L6 u →
      (∀ (t : MachineState) (q : Word), t.pc = 0x7801bd7c#64 → CalleeSaved u t →
        t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = q → RoImage Ro.layout t → HeapAt ((q, k1) :: (p0, k0) :: T.live L) t →
        Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t →
        Region T.b6 T.L6 t →
        (q = 0#64 ∨ (0x78048980 ≤ q.toNat ∧ q.toNat + 8 * k1 ≤ 0x1c00000000 ∧
          RegionOk Ro.layout.roBase Ro.layout.textHi q k1 ∧
          RegionOk Ro.layout.textLo Ro.layout.textHi q k0 ∧ Disjoint q k0 p0 k0 ∧ Region p0 W t ∧
          Disjoint T.b2 138 q k0 ∧ Disjoint T.b3 1024 q k0 ∧ Disjoint T.b4 1024 q k0 ∧
          Disjoint T.b5 1024 q k0 ∧ Disjoint T.b6 516 q k0)) →
        SafeN G n P t) → SafeN G n P u := by
  intro u sp' h1 h2 h3 h4 h5 h6 h7 h8 hro hh hW r2 r3 r4 r5 r6 k
  have hne : ∀ {b : Word}, 0x78040620 ≤ b.toNat → b ≠ 0#64 := fun hb e => by
    rw [e] at hb; simp at hb
  refine realloc_alloc_core (L := T.live L) hcode hal (Nat.le_refl _) hk01 hk1 hWl hlo u sp' h1 h2 h3 h4 h5 h6 h7 h8
    hro hh hW ?_
  intro t q a1 a2 a3 a4 a5 a6 a7 hh' hres hkeep
  refine k t q a1 a2 a3 a4 a5 a6 a7 hh'
    (Region.kept_live r2 T.l2 (hne hT.lo2) hh (by simp) hkeep)
    (Region.kept_live r3 T.l3 (hne hT.lo3) hh (by simp) hkeep)
    (Region.kept_live r4 T.l4 (hne hT.lo4) hh (by simp) hkeep)
    (Region.kept_live r5 T.l5 (hne hT.lo5) hh (by simp) hkeep)
    (Region.kept_live r6 T.l6 (hne hT.lo6) hh (by simp) hkeep) ?_
  rcases hres with h | ⟨hq, h2, h3, h4, h5, h6⟩
  · exact .inl h
  · have hh'' := hh'.sub (L' := (q, k1) :: T.live L)
      (List.Sublist.cons_cons _ (List.sublist_cons_self _ _))
    exact .inr ⟨hq, h2, h3, h4, h5, h6,
      table_apart (x := (q, k1)) hh'' (by simp) hT.lo2 hq hk01,
      table_apart (x := (q, k1)) hh'' (by simp) hT.lo3 hq hk01,
      table_apart (x := (q, k1)) hh'' (by simp) hT.lo4 hq hk01,
      table_apart (x := (q, k1)) hh'' (by simp) hT.lo5 hq hk01,
      table_apart (x := (q, k1)) hh'' (by simp) hT.lo6 hq hk01⟩

/-- `realloc_dealloc`, also keeping the hasher's five heap tables. -/
theorem realloc_dealloc6 {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    {p0 al : Word} {k0 k1 : Nat} {c : Word → Option Instr} (hcode : c = C) (T : HasherT)
    (hT : Arena6 T) (hal : al = 1#64 ∨ al = 8#64) (hk01 : k0 ≤ k1) (hlo : 0x78048980 ≤ p0.toNat) :
    ∀ (u : MachineState) (sp' q : Word) (V : List Word), V.length = k0 →
      u.pc = 0x7801c620#64 → u.code = c →
      u.getReg .x1 = 0x7801bdc8#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' →
      u.getReg .x19 = q → u.getReg .x10 = 0x78040620#64 → u.getReg .x11 = p0 → u.getReg .x12 = al →
      HeapAt ((p0, k0) :: (q, k1) :: T.live L) u → Region q V u → 0x78048980 ≤ q.toNat →
      Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u →
      Region T.b6 T.L6 u →
      (∀ t, t.pc = 0x7801bdc8#64 → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        HeapAt ((q, k1) :: T.live L) t → Region q V t →
        Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t →
        Region T.b6 T.L6 t → SafeN G n P t) → SafeN G n P u := by
  intro u sp' q V hV h1 h2 h3 h4 h5 h19 h6 h7 h8 hh hV' hq r2 r3 r4 r5 r6 k
  have hne : ∀ {b : Word}, 0x78040620 ≤ b.toNat → b ≠ 0#64 := fun hb e => by
    rw [e] at hb; simp at hb
  have hh0 := hh.sub (List.sublist_cons_self _ _)
  refine realloc_dealloc_core (L := T.live L) hcode hal hk01 hlo u sp' q V hV h1 h2 h3 h4 h5 h19 h6 h7
    h8 hh hV' hq ?_
  intro t a1 a2 a3 a4 a5 a6 a7 hkeep
  exact k t a1 a2 a3 a4 a5 a6 a7
    (Region.kept_live r2 T.l2 (hne hT.lo2) hh0 (by simp) hkeep)
    (Region.kept_live r3 T.l3 (hne hT.lo3) hh0 (by simp) hkeep)
    (Region.kept_live r4 T.l4 (hne hT.lo4) hh0 (by simp) hkeep)
    (Region.kept_live r5 T.l5 (hne hT.lo5) hh0 (by simp) hkeep)
    (Region.kept_live r6 T.l6 (hne hT.lo6) hh0 (by simp) hkeep)

/-- `commit_ivk`'s byte buffer's reallocations, `(old, new)` in doublewords. -/
def reallocSizesFi : List (Nat × Nat) := [(1, 2), (2, 4), (4, 8), (8, 16), (16, 32), (32, 64)]

set_option maxHeartbeats 400000000 in
/-- `heap_realloc` behind the hasher's five heap tables (`from_iter` in `commit_ivk`): they are
    kept. -/
theorem heap_realloc6 {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)}
    (T : HasherT) (hT : Arena6 T) (s : MachineState) (ra sp p0 al : Word) (k0 k1 : Nat) (W : List Word)
    (hpc : s.pc = 0x7801bd38#64) (hcode : s.code = C)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x60 sp)
    (ha0 : s.getReg .x10 = p0) (ha1 : s.getReg .x11 = BitVec.ofNat 64 (8 * k0))
    (ha2 : s.getReg .x12 = al) (ha3 : s.getReg .x13 = BitVec.ofNat 64 (8 * k1))
    (hal : al = 1#64 ∨ al = 8#64) (hsz : (k0, k1) ∈ reallocSizesFi)
    (hW : Region p0 W s) (hWl : W.length = k0) (hlo : 0x78048980 ≤ p0.toNat)
    (hro : RoImage Ro.layout s) (hh : HeapAt ((p0, k0) :: T.live L) s)
    (r2 : Region T.b2 T.L2 s) (r3 : Region T.b3 T.L3 s) (r4 : Region T.b4 T.L4 s)
    (r5 : Region T.b5 T.L5 s) (r6 : Region T.b6 T.L6 s)
    (hcpy : ∀ (u : MachineState) (q : Word), u.pc = 0x7801b4d8#64 → u.code = s.code →
      u.getReg .x1 = 0x7801bda0#64 → u.getReg .x10 = q → u.getReg .x11 = p0 →
      u.getReg .x12 = BitVec.ofNat 64 (8 * k0) → Region p0 W u →
      RegionOk Ro.layout.textLo Ro.layout.textHi q k0 → Disjoint q k0 p0 k0 →
      (∀ t, t.pc = 0x7801bda0#64 → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput → Unchanged [(q, k0)] u t → Region q W t →
        SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t : MachineState, t.pc = ra → CalleeSaved s t → t.code = s.code →
      t.privateInput = s.privateInput →
      Unchanged [(sp - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      RoImage Ro.layout t → HeapAt ((t.getReg .x10, k1) :: T.live L) t →
      Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t →
      Region T.b6 T.L6 t →
      ((t.getReg .x10).toNat = 0 ∨ (0x78048980 ≤ (t.getReg .x10).toNat ∧ (t.getReg .x10).toNat + 8 * k1 ≤ 0x1c00000000 ∧
        RegionOk Ro.layout.roBase Ro.layout.textHi (t.getReg .x10) k1 ∧ Region (t.getReg .x10) W t)) →
      SafeN G n P t) :
    SafeN G n P s := by
  have hk01 : k0 ≤ k1 ∧ 8 * k1 ≤ 0x78000000 := by
    simp only [reallocSizesFi, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hsz
    omega
  have hcodeR : CodeAt F_7801bd38.base F_7801bd38.prog s :=
    codeAt_of_image Loaded.codeWF Layout.code_F_7801bd38 F_7801bd38.decode_ok hcode
  have hcw := codeWithin_C hcode
  have hA := realloc_alloc6 (G := G) (n := n) (P := P) (L := L) (W := W) (c := s.code) hcode T hT hal
    hk01.1 hk01.2 hWl hlo
  have hD := realloc_dealloc6 (G := G) (n := n) (P := P) (L := L) (p0 := p0) (k1 := k1) (c := s.code)
    hcode T hT hal hk01.1 hlo
  clear hk01
  have hu := Unchanged.refl [(sp - 0x60#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hI : s.privateInput = s.privateInput := rfl
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hstk.frame 12 (by decide)
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo' := hstk.lo
  have hokF6 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x30#64) 6 s
  have hb0 := hh.bound (List.mem_cons_self ..)
  have hdjF : Disjoint (sp - 0x30#64) 6 p0 k0 := by
    have := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    have e : (sp - 0x30#64).toNat = sp.toNat - 0x30 := by
      rw [BitVec.toNat_sub]; simp; omega
    simp only [TOP] at hb0
    unfold AsmVerif.RiscV.Sym.Disjoint; rw [e]; simp at hb0 ⊢; omega
  have hdjT : ∀ {b : Word} {m : Nat}, 0x78040620 ≤ b.toNat → b.toNat + 8 * m ≤ 0x1c00000000 →
      Disjoint (sp - 0x30#64) 6 b m := by
    intro b m h1 h2
    have := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    have e : (sp - 0x30#64).toNat = sp.toNat - 0x30 := by
      rw [BitVec.toNat_sub]; simp; omega
    unfold AsmVerif.RiscV.Sym.Disjoint; rw [e]; simp; omega
  have hd2 := hdjT hT.lo2 hT.hi2
  have hd3 := hdjT hT.lo3 hT.hi3
  have hd4 := hdjT hT.lo4 hT.hi4
  have hd5 := hdjT hT.lo5 hT.hi5
  have hd6 := hdjT hT.lo6 hT.hi6
  clear hdjT
  have hl2 := T.l2
  have hl3 := T.l3
  have hl4 := T.l4
  have hl5 := T.l5
  have hl6 := T.l6
  simp only [reallocSizesFi, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hsz
  rcases hsz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    sym_exec [hA, hcpy, hD]
    all_goals sym_close hk
    all_goals try rw [hx10]
    all_goals first
      | (rw [hpost] at hcarry; exact hcarry.sublist (List.Sublist.cons_cons _ (List.sublist_cons_self _ _)))
      | exact hcarry.sublist (List.Sublist.cons_cons _ (List.sublist_cons_self _ _))
      | exact hcarry
      | (left; rfl)
      | (right; refine ⟨by assumption, by assumption, by assumption, ?_⟩)
    all_goals
      refine Region.of_eq ‹Region post17_0 _ _› ?_
      first
        | rfl
        | (conv => rhs; rw [AsmVerif.RiscV.Sym.List.eq_map_range W hWl]
           rfl)

/-- A byte buffer's capacities: `8 · 2^i` bytes, the doubleword count a size `heap_realloc`
    covers. -/
theorem cap_facts {C : Nat}
    (hC : C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024) :
    C = 8 * (C / 8) ∧ C / 4 = 2 * (C / 8) ∧ (C / 8, C / 4, C / 8) ∈ reallocSizes ∧
      (C / 8 = 1 ∨ C / 8 = 2 ∨ (4 ∣ C / 8 ∧ 4 ≤ C / 8)) := by
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `__rust_realloc(p0, C, 1, 2 C)` at `finish_grow` (`NoteCommitment::derive`). -/
theorem realloc_nc_ok {G : MachineState → Prop} {n : Nat} {P : Prop} : ReallocOrNc G n P C := by
  intro u sp' p0 Cb W L' hC hW hpc hcode hx1 hsp hstk hx10 hx11 hx12 hx13 hWr hlo _ hro hh k
  obtain ⟨e1, e2, hsz, hk0⟩ := cap_facts hC
  have hb := hh.bound (List.mem_cons_self ..)
  simp only [TOP] at hb
  have hokP : RegionOk Ro.layout.textLo Ro.layout.textHi p0 (Cb / 8) :=
    RegionOk.of_nat (hh.aligned (List.mem_cons_self ..)) (by simp only [SP1_MAX_MEMORY]; omega)
      (.inr (by simp only [Ro.layout_textHi]; omega))
  refine heap_realloc u _ sp' p0 1#64 (Cb / 8) (Cb / 4) (Cb / 8) W hpc hcode hx1 (by decide) hsp hstk hx10
    (by rw [hx11, ← e1]) hx12 (by rw [hx13]; congr 1; omega) (.inl rfl) hsz hWr hW hlo hro hh
    (realloc_copy (c := u.code) hcode hk0 hW hokP) ?_
  intro t hpc' hcs hcode' _ hun hro' hh' hres
  obtain ⟨W', hW', hW'l⟩ := Region.exists_junk (t.getReg .x10 + BitVec.ofNat 64 (8 * W.length))
    (Cb / 8 + 1) t
  have hok := regionOk_live hh' (List.mem_cons_self ..) (hres.imp id fun h => h.1) (by omega)
  refine k t _ W' hpc' hcs hcode' hun rfl hW'l hok ?_ ?_ hh'
  · rcases hres with h | ⟨h1, _, _, _⟩
    · omega
    · have := hh'.bound_ne (List.mem_cons_self ..) (fun e => by
        dsimp only at e; rw [e] at h1; simp at h1)
      simp only [TOP] at this
      omega
  · rcases hres with h | ⟨h1, _, _, hR⟩
    · exact .inl h
    · exact .inr ⟨h1, Region.append hR hW'⟩

/-- A live table and the head buffer with one doubleword past it (null or not) do not overlap:
    a block header lies between two live buffers. -/
theorem disjoint_plus1 {x : Word × Nat} {L : List (Word × Nat)} {t : MachineState}
    (h : HeapAt (x :: L) t) {b : Word} {m : Nat} (hm : (b, m) ∈ L) (hb : 0x78040620 ≤ b.toNat)
    (hx : x.1.toNat = 0 ∨ 0x78048980 ≤ x.1.toNat) (hx2 : 8 * x.2 + 8 ≤ 0x78000000) :
    Disjoint b m x.1 (x.2 + 1) := by
  have hbb := h.bound (List.mem_cons_of_mem _ hm)
  simp only [TOP] at hbb
  rcases hx with hx | hx
  · exact ⟨.inr (by omega), by omega, by omega⟩
  · have hbx := h.bound_ne (List.mem_cons_self ..) (fun e => by rw [e] at hx; simp at hx)
    have ha := h.apart hm (fun e => by rw [e] at hx; simp at hx) (fun e => by
      dsimp only at e; rw [e] at hb; simp at hb)
    simp only [TOP] at hbx
    dsimp only at ha
    exact ⟨by omega, by omega, by omega⟩

/-- `__rust_realloc(p0, C, 1, 2 C)` at `finish_grow` (`commit_ivk`), the hasher's tables kept. -/
theorem realloc_fi_ok {G : MachineState → Prop} {n : Nat} {P : Prop} : ReallocOrFi G n P C := by
  intro T hT hb1 u sp' p0 Cb W L' hC hW hpc hcode hx1 hsp hstk hx10 hx11 hx12 hx13 hWr hlo _ hro hh
    r1 r2 r3 r4 r5 r6 k
  obtain ⟨e1, e2, _, hk0⟩ := cap_facts (C := Cb) (by
    rcases hC with h | h | h | h | h | h <;> simp [h])
  have hsz : (Cb / 8, Cb / 4) ∈ reallocSizesFi := by
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hC8 : Cb ≤ 256 := by rcases hC with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hb := hh.bound (List.mem_cons_self ..)
  simp only [TOP] at hb
  have hokP : RegionOk Ro.layout.textLo Ro.layout.textHi p0 (Cb / 8) :=
    RegionOk.of_nat (hh.aligned (List.mem_cons_self ..)) (by simp only [SP1_MAX_MEMORY]; omega)
      (.inr (by simp only [Ro.layout_textHi]; omega))
  refine heap_realloc6 T hT u _ sp' p0 1#64 (Cb / 8) (Cb / 4) W hpc hcode hx1 (by decide) hsp hstk
    hx10 (by rw [hx11, ← e1]) hx12 (by rw [hx13]; congr 1; omega) (.inl rfl) hsz hWr hW hlo hro hh
    r2 r3 r4 r5 r6 (realloc_copy (c := u.code) hcode hk0 hW hokP) ?_
  intro t hpc' hcs hcode' _ hun hro' hh' q2 q3 q4 q5 q6 hres
  obtain ⟨W', hW', hW'l⟩ := Region.exists_junk (t.getReg .x10 + BitVec.ofNat 64 (8 * W.length))
    (Cb / 8 + 1) t
  have hp := hres.imp id fun h => h.1
  have hok := regionOk_live hh' (List.mem_cons_self ..) hp (by omega)
  have hst := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
  have hs60 : (sp' - 0x60#64).toNat = sp'.toNat - 0x60 := by
    have := hstk.lo; rw [BitVec.toNat_sub]; simp; omega
  have q1 : Region T.b1 T.L1 t := by
    refine r1.of_unchanged' hun T.l1 fun r hr => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rw [hb1]
    rcases hr with rfl | rfl | rfl
    · simp only [AsmVerif.RiscV.Sym.Disjoint, hs60]; simp; omega
    · simp [AsmVerif.RiscV.Sym.Disjoint]
    · simp [AsmVerif.RiscV.Sym.Disjoint]
  have d1 : Disjoint T.b1 10 (t.getReg .x10) (Cb / 4 + 1) := by
    rw [hb1]
    have := hh'.bound (List.mem_cons_self ..)
    simp only [TOP] at this
    rcases hp with h | h <;> exact ⟨by simp; omega, by simp, by omega⟩
  refine k t _ W' hpc' hcs hcode' hun rfl hW'l hok ?_ ?_ hh' q1 q2 q3 q4 q5 q6 d1
    (disjoint_plus1 (x := (_, Cb / 4)) hh' (by simp) hT.lo2 hp (by omega))
    (disjoint_plus1 (x := (_, Cb / 4)) hh' (by simp) hT.lo3 hp (by omega))
    (disjoint_plus1 (x := (_, Cb / 4)) hh' (by simp) hT.lo4 hp (by omega))
    (disjoint_plus1 (x := (_, Cb / 4)) hh' (by simp) hT.lo5 hp (by omega))
    (disjoint_plus1 (x := (_, Cb / 4)) hh' (by simp) hT.lo6 hp (by omega))
  · rcases hres with h | ⟨h1, _, _, _⟩
    · omega
    · have := hh'.bound_ne (List.mem_cons_self ..) (fun e => by
        dsimp only at e; rw [e] at h1; simp at h1)
      simp only [TOP] at this
      omega
  · rcases hres with h | ⟨h1, _, _, hR⟩
    · exact .inl h
    · exact .inr ⟨h1, Region.append hR hW'⟩

end Cases.Zip2005.Run
