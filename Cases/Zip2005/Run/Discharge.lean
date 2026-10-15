/-
  Cases.Zip2005.Run.Discharge

  The run's allocator contracts, discharged (milestone M1): each contract the tree states at an
  allocator call site (`__rust_alloc`, `__rust_dealloc`) follows from the phase-D lifts
  `rust_alloc` and `rust_dealloc` under the run's invariant (`Run.HeapAt`).
-/

import Cases.Zip2005.Run.Alloc
import Cases.Zip2005.Run.Dealloc
import Cases.Zip2005.Witness.IoErrorFrom
import Cases.Zip2005.Loaded
import AsmVerif.RiscV.Sym.Load

set_option maxRecDepth 100000

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Sym Cases.Zip2005 Cases.Zip2005.Image
  Cases.Zip2005.Runtime

/-- A live buffer's pointer is a doubleword address: null, or a block's payload, 16 bytes into a
    32-byte-aligned block. -/
theorem HeapAt.aligned {L : List (Word × Nat)} {s : MachineState} (h : HeapAt L s)
    {r : Word × Nat} (hr : r ∈ L) : r.1.toNat % 8 = 0 := by
  obtain ⟨_, _, _, bs, Lf, hrep, _, hL⟩ := h.holds
  rcases hL r hr with ⟨h0, _⟩ | ⟨b, hb, _, _, hba, _⟩
  · rw [h0]; rfl
  · obtain ⟨hA, _, hlt⟩ := (Tlsf.rep_iff.mp hrep).2.blkA hb
    have h32 : b.a.toNat % 32 = 0 := by
      have e := congrArg BitVec.toNat hA
      rw [BitVec.toNat_and] at e
      simp only [BitVec.toNat_ofNat] at e
      rw [show (31 : Nat) % 2 ^ 64 = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod] at e
      simpa using e
    rw [← hba, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    omega

/-- A live buffer does not wrap: it ends by `TOP`, or, null, below the control block. -/
theorem HeapAt.bound {L : List (Word × Nat)} {s : MachineState} (h : HeapAt L s)
    {r : Word × Nat} (hr : r ∈ L) : r.1.toNat + 8 * r.2 ≤ TOP := by
  obtain ⟨_, _, _, bs, Lf, hrep, hsent, hL⟩ := h.holds
  rcases hL r hr with ⟨h0, hk⟩ | ⟨b, hb, _, _, _, hz⟩
  · rw [h0]; simp only [TOP]; simp; omega
  · have := end_le hrep hsent hb; omega

/-- Two live buffers, the head and one of the rest, both non-null, do not overlap. -/
theorem HeapAt.disjoint {x : Word × Nat} {L : List (Word × Nat)} {s : MachineState}
    (h : HeapAt (x :: L) s) {y : Word × Nat} (hy : y ∈ L) (hx0 : x.1 ≠ 0#64)
    (hy0 : y.1 ≠ 0#64) : Disjoint x.1 x.2 y.1 y.2 := by
  have hbx := h.bound (List.mem_cons_self ..)
  have hby := h.bound (List.mem_cons_of_mem _ hy)
  obtain ⟨_, _, hD, bs, Lf, hrep, _, hL⟩ := h.holds
  have hne : x.1 ≠ y.1 := by
    rcases List.rel_of_pairwise_cons hD hy with h | h
    · exact absurd h hx0
    · exact h
  rcases hL x (List.mem_cons_self ..) with ⟨h0, _⟩ | ⟨b, hb, _, _, hba, hbz⟩
  · exact absurd h0 hx0
  rcases hL y (List.mem_cons_of_mem _ hy) with ⟨h0, _⟩ | ⟨c, hc, _, _, hca, hcz⟩
  · exact absurd h0 hy0
  have hsh := (Tlsf.rep_iff.mp hrep).2
  have hbc : b ≠ c := by rintro rfl; exact hne (hba.symm.trans hca)
  have hbl := (hsh.blk hb).2.2.1
  have hcl := (hsh.blk hc).2.2.1
  have hxb : x.1.toNat = b.a.toNat + 16 := by rw [← hba, BitVec.toNat_add]; simp; omega
  have hyc : y.1.toNat = c.a.toNat + 16 := by rw [← hca, BitVec.toNat_add]; simp; omega
  simp only [TOP] at hbx hby
  refine ⟨?_, by omega, by omega⟩
  rcases hsh.disj hb hc hbc with h1 | h1 <;> omega

/-- A live non-null buffer ends at least 32 bytes below `TOP`: its block is not the sentinel,
    which is last. -/
theorem HeapAt.bound_ne {L : List (Word × Nat)} {s : MachineState} (h : HeapAt L s)
    {r : Word × Nat} (hr : r ∈ L) (h0 : r.1 ≠ 0#64) : r.1.toNat + 8 * r.2 + 32 ≤ TOP := by
  obtain ⟨_, _, _, bs, Lf, hrep, hsent, hL⟩ := h.holds
  rcases hL r hr with ⟨e, _⟩ | ⟨b, hb, _, hbl, hba, hbz⟩
  · exact absurd e h0
  have hsh := (Tlsf.rep_iff.mp hrep).2
  have hbs : b ≠ sentinel := fun e => by rw [e] at hbl; simp [sentinel] at hbl
  have hbl40 := (hsh.blk hb).2.2.1
  have hbz32 := Tlsf.Shape.sz_ge (hsh.blk hb).2.2.2.2
  have he := end_le hrep hsent hb
  have hxb : r.1.toNat = b.a.toNat + 16 := by rw [← hba, BitVec.toNat_add]; simp; omega
  rcases hsh.disj hb hsent hbs with h1 | h1 <;> simp [sentinel, TOP] at h1 he ⊢ <;> omega

/-- Two live buffers, the head and one of the rest, both non-null, are a block header apart. -/
theorem HeapAt.apart {x : Word × Nat} {L : List (Word × Nat)} {s : MachineState}
    (h : HeapAt (x :: L) s) {y : Word × Nat} (hy : y ∈ L) (hx0 : x.1 ≠ 0#64)
    (hy0 : y.1 ≠ 0#64) :
    x.1.toNat + 8 * x.2 + 16 ≤ y.1.toNat ∨ y.1.toNat + 8 * y.2 + 16 ≤ x.1.toNat := by
  obtain ⟨_, _, hD, bs, Lf, hrep, _, hL⟩ := h.holds
  have hne : x.1 ≠ y.1 := by
    rcases List.rel_of_pairwise_cons hD hy with h | h
    · exact absurd h hx0
    · exact h
  rcases hL x (List.mem_cons_self ..) with ⟨h0, _⟩ | ⟨b, hb, _, _, hba, hbz⟩
  · exact absurd h0 hx0
  rcases hL y (List.mem_cons_of_mem _ hy) with ⟨h0, _⟩ | ⟨c, hc, _, _, hca, hcz⟩
  · exact absurd h0 hy0
  have hsh := (Tlsf.rep_iff.mp hrep).2
  have hbc : b ≠ c := by rintro rfl; exact hne (hba.symm.trans hca)
  have hbl := (hsh.blk hb).2.2.1
  have hcl := (hsh.blk hc).2.2.1
  have hxb : x.1.toNat = b.a.toNat + 16 := by rw [← hba, BitVec.toNat_add]; simp; omega
  have hyc : y.1.toNat = c.a.toNat + 16 := by rw [← hca, BitVec.toNat_add]; simp; omega
  rcases hsh.disj hb hc hbc with h1 | h1 <;> omega

/-- A region inside `[b, b + 8 n)`, not wrapping, survives a step keeping those bytes. -/
theorem Region.kept {b : Word} {W : List Word} {n : Nat} {u t : MachineState} (hR : Region b W u)
    (hl : W.length ≤ n) (hb : b.toNat + 8 * n ≤ 2 ^ 64)
    (hk : ∀ a, InRegion a b n → t.getMem a = u.getMem a) : Region b W t := by
  intro i hi
  rw [hk]
  · exact hR i hi
  · have : (b + BitVec.ofNat 64 (8 * i)).toNat = b.toNat + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    unfold InRegion; omega

/-- A live buffer's region survives an allocator call (which keeps every live buffer's bytes). -/
theorem Region.kept_live {L : List (Word × Nat)} {b : Word} {W : List Word} {n : Nat}
    {u t : MachineState} (hR : Region b W u) (hW : W.length = n) (hb0 : b ≠ 0#64)
    (hh : HeapAt L u) (hm : (b, n) ∈ L)
    (hk : ∀ r ∈ L, ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) :
    Region b W t :=
  Region.kept hR hW.le (by have := hh.bound hm; simp only [TOP] at this; omega)
    (fun a ha => hk _ hm a hb0 ha)

/-- **`__rust_alloc(8 k, al)`, as the tree's call sites state it**: a block of `k` doublewords
    (null or in the arena), live after the call, its contents junk. -/
theorem alloc_contract {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    {sp' : Word} {L' : List (Word × Nat)} (k : Nat) {sz : Nat} {al : Word}
    (hpc : u.pc = 0x7801bcec#64) (hcode : u.code = C) (hsp : u.getReg .x2 = sp')
    (hstk : StackOk Ro.layout 0x30 sp')
    (hsz : u.getReg .x10 = BitVec.ofNat 64 sz) (hsz1 : sz ≤ 8 * k) (hsz2 : 8 * k ≤ sz + 7)
    (hk8 : 8 * k ≤ 0x78000000)
    (hal : u.getReg .x11 = al) (halp : al &&& (al - 1#64) = 0#64) (hal0 : al ≠ 0#64)
    (hal32 : al < 32#64) (hro : RoImage Ro.layout u) (hh : HeapAt L' u)
    (hk : ∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = u.getReg .x1 &&& ~~~1#64 →
      CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
      Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = ptr → B.length = k → Region ptr B t →
      RegionOk Ro.layout.roBase Ro.layout.textHi ptr k →
      (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 * k ≤ 0x1c00000000 →
      RoImage Ro.layout t → HeapAt ((ptr, k) :: L') t →
      (∀ r ∈ L', ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
      SafeN G n P t) :
    SafeN G n P u := by
  have h1 := hstk.lo
  have h2 : sp'.toNat ≤ 0x78000000 := hstk.hi
  refine rust_alloc hpc hcode (by rw [hsp]; omega) (by rw [hsp]; omega) hsz hsz1 hsz2 (by omega) hal halp hal0
    hal32 hro hh ?_
  intro t ptr hpc' hcs hcode' hpriv hun hx10 hro' hh' hptr hkeep
  rw [hsp] at hun
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk ptr k t
  have hal8 := hh'.aligned (List.mem_cons_self ..)
  refine hk t ptr B hpc' hcs hcode' hpriv hun hx10 hBl hB ?_ ?_ ?_ hro' hh' hkeep
  · refine ⟨hal8, ?_, ?_⟩
    · rcases hptr with h0 | ⟨_, h⟩ <;> simp only [SP1_MAX_MEMORY, TOP] at * <;> omega
    · rcases hptr with h0 | ⟨h, _⟩
      · left; simp only [Ro.layout_roBase]; omega
      · right; simp only [Ro.layout_textHi]; omega
  · rcases hptr with h0 | ⟨h, _⟩
    · exact .inl h0
    · exact .inr (by omega)
  · rcases hptr with h0 | ⟨_, h⟩ <;> simp only [TOP] at * <;> omega

/-- `alloc_contract` at a call with return address `r`, the alignment `1` or `8`. -/
theorem alloc_at {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    {sp' r : Word} {L' : List (Word × Nat)} (k : Nat) {sz : Nat}
    (hpc : u.pc = 0x7801bcec#64) (hcode : u.code = C) (hr : u.getReg .x1 = r)
    (hr1 : r &&& ~~~1#64 = r) (hsp : u.getReg .x2 = sp') (hstk : StackOk Ro.layout 0x30 sp')
    (hsz : u.getReg .x10 = BitVec.ofNat 64 sz) (hsz1 : sz ≤ 8 * k) (hsz2 : 8 * k ≤ sz + 7)
    (hk8 : 8 * k ≤ 0x78000000)
    (hal : u.getReg .x11 = 1#64 ∨ u.getReg .x11 = 8#64) (hro : RoImage Ro.layout u)
    (hh : HeapAt L' u)
    (hk : ∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r → CalleeSaved u t →
      t.code = u.code → t.privateInput = u.privateInput →
      Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = ptr → B.length = k → Region ptr B t →
      RegionOk Ro.layout.roBase Ro.layout.textHi ptr k →
      (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 * k ≤ 0x1c00000000 →
      HeapAt ((ptr, k) :: L') t →
      (∀ r ∈ L', ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
      SafeN G n P t) :
    SafeN G n P u := by
  rcases hal with hal | hal
  · refine alloc_contract k hpc hcode hsp hstk hsz hsz1 hsz2 hk8 hal (by decide) (by decide) (by decide) hro hh ?_
    intro t ptr B hpc' hcs hcode' hpriv hun hx hBl hB hok hlo hhi _ hh' hkeep
    exact hk t ptr B (by rw [hpc', hr, hr1]) hcs hcode' hpriv hun hx hBl hB hok hlo hhi hh' hkeep
  · refine alloc_contract k hpc hcode hsp hstk hsz hsz1 hsz2 hk8 hal (by decide) (by decide) (by decide) hro hh ?_
    intro t ptr B hpc' hcs hcode' hpriv hun hx hBl hB hok hlo hhi _ hh' hkeep
    exact hk t ptr B (by rw [hpc', hr, hr1]) hcs hcode' hpriv hun hx hBl hB hok hlo hhi hh' hkeep

theorem RegionOk.toText {ptr : Word} {k : Nat}
    (h : RegionOk Ro.layout.roBase Ro.layout.textHi ptr k) :
    RegionOk Ro.layout.textLo Ro.layout.textHi ptr k :=
  h.weaken (by simp only [Ro.layout_roBase, Ro.layout_textLo]; omega) (Nat.le_refl _)

/-! ## The tree's `__rust_alloc` contracts -/

theorem halloc_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = C →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r' → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ _ hpc hcode hr hr1 hsp hstk hsz hal hro hh hk =>
    alloc_at 3 hpc hcode hr hr1 hsp hstk hsz (Nat.le_refl _) (by omega) (by decide) (.inr hal) hro hh
      fun t ptr B h1 h2 h3 _ h4 h5 h6 h7 h8 h9 h10 h11 _ => hk t ptr B h1 h2 h3 h4 h5 h6 h7 h8.toText h9 h10 h11

theorem halloc_mp_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = C →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x80#64 →
      u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x80 ≤ 0x1c00000000 → HeapAt ((ptr, 16) :: L') t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ hpc hcode hr hsp hstk hsz hal hro hh hk =>
    alloc_at 16 hpc hcode hr (by decide) hsp hstk hsz (Nat.le_refl _) (by omega) (by decide) (.inr hal) hro hh
      fun t ptr B h1 h2 h3 _ h4 h5 h6 h7 h8 h9 h10 h11 _ => hk t ptr B h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem halloc_c_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = C →
      u.getReg .x1 = 0x78023cf4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x1800#64 →
      u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78023cf4#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 768 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x1800 ≤ 0x1c00000000 → HeapAt ((ptr, 768) :: L') t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ hpc hcode hr hsp hstk hsz hal hro hh hk =>
    alloc_at 768 hpc hcode hr (by decide) hsp hstk hsz (Nat.le_refl _) (by omega) (by decide) (.inr hal) hro hh
      fun t ptr B h1 h2 h3 _ h4 h5 h6 h7 h8 h9 h10 h11 _ => hk t ptr B h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem halloc_nc_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = C →
      u.getReg .x1 = 0x7801e028#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      RoImage Ro.layout u → HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e028#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 → HeapAt ((ptr, 1) :: L') t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ hpc hcode hr hsp hstk hsz hal hro hh hk =>
    alloc_at 1 hpc hcode hr (by decide) hsp hstk hsz (Nat.le_refl _) (by omega) (by decide) (.inl hal) hro hh
      fun t ptr B h1 h2 h3 _ h4 h5 h6 h7 h8 h9 h10 h11 _ => hk t ptr B h1 h2 h3 h4 h5 h6 h7 h8.toText h9 h10 h11

/-- A non-null pointer of the arena, or null, and a live table at or past the control block, do
    not overlap the null pointer's first doubleword. -/
theorem disjoint_live {x : Word × Nat} {L : List (Word × Nat)} {s : MachineState}
    (h : HeapAt (x :: L) s) {y : Word × Nat} (hy : y ∈ L) (hylo : 0x78040620 ≤ y.1.toNat)
    (hx : x.1.toNat = 0 ∨ 0x78048980 ≤ x.1.toNat) (hx1 : 1 ≤ x.2) :
    Disjoint y.1 y.2 x.1 1 := by
  have hby := h.bound (List.mem_cons_of_mem _ hy)
  simp only [TOP] at hby
  rcases hx with hx0 | hx0
  · refine ⟨.inr ?_, by omega, by omega⟩
    omega
  · have hd := h.disjoint hy (by intro e; rw [e] at hx0; simp at hx0)
      (by intro e; rw [e] at hylo; simp at hylo)
    obtain ⟨hd, _, _⟩ := hd
    refine ⟨?_, by omega, by omega⟩
    omega

theorem halloc_fi_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      0x78040620 ≤ iptr.toNat → 0x78040620 ≤ tg0.toNat → 0x78040620 ≤ tg1.toNat → 0x78040620 ≤ tg2.toNat →
      0x78040620 ≤ tg3.toNat → IV.length = 138 → G0.length = 1024 → G1.length = 1024 →
      G2.length = 1024 → G3.length = 516 → ∀ (u : MachineState) (sp : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = C →
      u.getReg .x1 = 0x7801e184#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      RoImage Ro.layout u → HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e184#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
      Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
        Disjoint 0x780488a8#64 10 ptr 1 → Disjoint iptr 138 ptr 1 → Disjoint tg0 1024 ptr 1 → Disjoint tg1 1024 ptr 1 → Disjoint tg2 1024 ptr 1 → Disjoint tg3 516 ptr 1 →
        HeapAt ((ptr, 1) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G n P t) → SafeN G n P u := by
  intro tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx IV G0 G1 G2 G3 l1 l2 l3 l4 l5 e1 e2 e3 e4 e5 u sp L'
    hpc hcode hr hsp hstk hsz hal hS hIV hG0 hG1 hG2 hG3 hro hh hk
  refine alloc_at 1 hpc hcode hr (by decide) hsp hstk hsz (Nat.le_refl _) (by omega) (by decide) (.inl hal) hro hh ?_
  intro t ptr B h1 h2 h3 _ hun h5 h6 h7 h8 hp h10 hh' hkeep
  have hne : ∀ {b : Word}, 0x78040620 ≤ b.toNat → b ≠ 0#64 := fun hb e => by
    rw [e] at hb; simp at hb
  have hS' : Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t := by
    refine hS.of_unchanged hun fun r hr => ?_
    have := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have : (sp - 0x30#64).toNat = sp.toNat - 0x30 := by
        have := hstk.lo; rw [BitVec.toNat_sub]; simp; omega
      simp only [AsmVerif.RiscV.Sym.Disjoint, List.length_cons, List.length_nil, this]; simp; omega
    · simp [AsmVerif.RiscV.Sym.Disjoint]
    · simp [AsmVerif.RiscV.Sym.Disjoint]
  refine hk t ptr B h1 h2 h3 hun h5 h6 h7 h8.toText hp h10 hS'
    (Region.kept_live hIV e1 (hne l1) hh (by simp) hkeep)
    (Region.kept_live hG0 e2 (hne l2) hh (by simp) hkeep)
    (Region.kept_live hG1 e3 (hne l3) hh (by simp) hkeep)
    (Region.kept_live hG2 e4 (hne l4) hh (by simp) hkeep)
    (Region.kept_live hG3 e5 (hne l5) hh (by simp) hkeep) ?_
    (disjoint_live (y := (iptr, 138)) hh' (by simp) l1 hp (Nat.le_refl _))
    (disjoint_live (y := (tg0, 1024)) hh' (by simp) l2 hp (Nat.le_refl _))
    (disjoint_live (y := (tg1, 1024)) hh' (by simp) l3 hp (Nat.le_refl _))
    (disjoint_live (y := (tg2, 1024)) hh' (by simp) l4 hp (Nat.le_refl _))
    (disjoint_live (y := (tg3, 516)) hh' (by simp) l5 hp (Nat.le_refl _)) hh'
  refine ⟨?_, by decide, by omega⟩
  rcases hp with hp | hp <;> simp only [BitVec.toNat_ofNat] <;> omega

/-! ## The tree's `__rust_dealloc` contracts -/

/-- `rust_dealloc` at a call with return address `r`, a heap pointer, alignment `1` or `8`. -/
theorem dealloc_at {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    {sp' r ptr : Word} {k : Nat} {L' : List (Word × Nat)}
    (hpc : u.pc = 0x7801bd08#64) (hcode : u.code = C) (hr : u.getReg .x1 = r)
    (hr1 : r &&& ~~~1#64 = r) (hsp : u.getReg .x2 = sp') (hstk : StackOk Ro.layout 0x20 sp')
    (hp : u.getReg .x10 = ptr) (hal : u.getReg .x12 = 1#64 ∨ u.getReg .x12 = 8#64)
    (hlo : 0x78048980 ≤ ptr.toNat) (hh : HeapAt ((ptr, k) :: L') u)
    (hk : ∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
      Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      HeapAt L' t →
      (∀ r ∈ L', ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
      SafeN G n P t) :
    SafeN G n P u := by
  have h1 := hstk.lo
  have h2 : sp'.toNat ≤ 0x78000000 := hstk.hi
  have hp0 : ptr ≠ 0#64 := fun e => by rw [e] at hlo; simp at hlo
  have hal' : ∃ al, u.getReg .x12 = al ∧ al ≤ 31#64 := by
    rcases hal with h | h <;> exact ⟨_, h, by decide⟩
  obtain ⟨al, hal, hal31⟩ := hal'
  refine rust_dealloc hpc hcode (by rw [hsp]; omega) (by rw [hsp]; omega) hp hp0 hal hal31 hh ?_
  intro t hpc' hcs hcode' hpriv hun hh' hkeep
  rw [hsp] at hun
  exact hk t (by rw [hpc', hr, hr1]) hcs hcode' hpriv hun hh' hkeep

theorem hdealloc_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' r ptr sz : Word) (k : Nat) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = C →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 8#64 → 0x78048980 ≤ ptr.toNat →
      RoImage Ro.layout u → HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → HeapAt L' t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ _ _ _ _ hpc hcode hr hr1 hsp hstk hp _ hal hlo _ hh hk =>
    dealloc_at hpc hcode hr hr1 hsp hstk hp (.inr hal) hlo hh fun t h1 h2 h3 h4 h5 h6 _ => hk t h1 h2 h3 h4 h5 h6

theorem hdealloc_a1_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' r ptr sz : Word) (k : Nat) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = C →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 1#64 → 0x78048980 ≤ ptr.toNat →
      RoImage Ro.layout u → HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → HeapAt L' t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ _ _ _ _ hpc hcode hr hr1 hsp hstk hp _ hal hlo _ hh hk =>
    dealloc_at hpc hcode hr hr1 hsp hstk hp (.inl hal) hlo hh fun t h1 h2 h3 h4 h5 h6 _ => hk t h1 h2 h3 h4 h5 h6

/-- `__rust_dealloc` of a hint-area pointer (a record `read_vec` returned): the shim returns at
    once, memory untouched. -/
theorem hdealloc_hint_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' r ptr : Word) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = C →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → u.getReg .x10 = ptr →
      0x1c00000000 ≤ ptr.toNat → RoImage Ro.layout u → HeapAt L' u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        HeapAt L' t → SafeN G n P t) → SafeN G n P u :=
  fun u _ _ _ _ hpc hcode hr hr1 _ hp hlo _ hh hk =>
    rust_dealloc_hint hpc hcode (by rw [hp]; simpa only [TOP] using hlo) fun t h1 h2 h3 h4 hm =>
      hk t (by rw [h1, hr, hr1]) h2 h3 h4 (fun a _ => by simp only [MachineState.getMem, hm])
        (hh.of_mem_eq hm)

theorem hdealloc_nf_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' ptr : Word) (C' : List Word) (k : Nat) (L' : List (Word × Nat)), C'.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = C → u.getReg .x1 = 0x78020c64#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 → u.getReg .x12 = 8#64 →
      Region ptr C' u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      RoImage Ro.layout u → HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → HeapAt L' t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ _ _ _ _ hpc hcode hr hsp hstk hp _ hal _ hlo _ _ hh hk =>
    dealloc_at hpc hcode hr (by decide) hsp hstk hp (.inr hal) hlo hh fun t h1 h2 h3 _ h5 h6 _ => hk t h1 h2 h3 h5 h6

theorem hdealloc_cm_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (u : MachineState) (sp' ptr cap : Word) (C' : List Word) (k : Nat) (L' : List (Word × Nat)), C'.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = C → u.getReg .x1 = 0x780210f0#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C' u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      RoImage Ro.layout u → HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → HeapAt L' t → SafeN G n P t) → SafeN G n P u :=
  fun _ _ _ _ _ _ _ _ hpc hcode hr hsp hstk hp _ hal _ hlo _ _ hh hk =>
    dealloc_at hpc hcode hr (by decide) hsp hstk hp (.inl hal) hlo hh fun t h1 h2 h3 _ h5 h6 _ => hk t h1 h2 h3 h5 h6

theorem hdealloc_ivk_ok {G : MachineState → Prop} {n : Nat} {P : Prop} :
    ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      0x78040620 ≤ iptr.toNat → 0x78040620 ≤ tg0.toNat → 0x78040620 ≤ tg1.toNat → 0x78040620 ≤ tg2.toNat →
      0x78040620 ≤ tg3.toNat → IV.length = 138 → G0.length = 1024 → G1.length = 1024 →
      G2.length = 1024 → G3.length = 516 → ∀ (u : MachineState) (sp' ptr cap : Word) (C' : List Word) (k : Nat) (L' : List (Word × Nat)), C'.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = C → u.getReg .x1 = 0x780215d8#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C' u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      RoImage Ro.layout u → HeapAt ((ptr, k) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G n P t) → SafeN G n P u := by
  intro tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx IV G0 G1 G2 G3 l1 l2 l3 l4 l5 e1 e2 e3 e4 e5 u sp' ptr
    cap C' k L' _ hpc hcode hr hsp hstk hp _ hal _ hlo _ hS hIV hG0 hG1 hG2 hG3 _ hh hk
  have hne : ∀ {b : Word}, 0x78040620 ≤ b.toNat → b ≠ 0#64 := fun hb e => by
    rw [e] at hb; simp at hb
  have hh0 := hh.sub (List.sublist_cons_self _ _)
  refine dealloc_at hpc hcode hr (by decide) hsp hstk hp (.inl hal) hlo hh ?_
  intro t h1 h2 h3 _ hun hh' hkeep
  have hS' : Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t := by
    refine hS.of_unchanged hun fun r hr => ?_
    have := Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have : (sp' - 0x20#64).toNat = sp'.toNat - 0x20 := by
        have := hstk.lo; rw [BitVec.toNat_sub]; simp; omega
      simp only [AsmVerif.RiscV.Sym.Disjoint, List.length_cons, List.length_nil, this]; simp; omega
    · simp [AsmVerif.RiscV.Sym.Disjoint]
    · simp [AsmVerif.RiscV.Sym.Disjoint]
  exact hk t h1 h2 h3 hun hS'
    (Region.kept_live hIV e1 (hne l1) hh0 (by simp) hkeep)
    (Region.kept_live hG0 e2 (hne l2) hh0 (by simp) hkeep)
    (Region.kept_live hG1 e3 (hne l3) hh0 (by simp) hkeep)
    (Region.kept_live hG2 e4 (hne l4) hh0 (by simp) hkeep)
    (Region.kept_live hG3 e5 (hne l5) hh0 (by simp) hkeep) hh'

/-! ## `From<io::Error>` -/

theorem codeWithin_C {s : MachineState} (hs : s.code = C) :
    CodeWithin Ro.layout.textLo Ro.layout.textHi s :=
  codeWithin_of_image Loaded.codeWF (by decide +kernel) (by decide +kernel) hs

theorem hio_ok {G : MachineState → Prop} {n : Nat} {P : Prop}
    (hhandle_al : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = C →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → HeapAt L' u → SafeN G n P u) :
    ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = C →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        HeapAt L' t → SafeN G n P t) → SafeN G n P u := by
  intro u sp' r' L' hpc hcode hr hr1 hsp hstk hro hh hk
  refine io_error_from_spec u r' sp' hpc
    (codeAt_of_image Loaded.codeWF Layout.code_F_78036184 F_78036184.decode_ok hcode)
    (codeAt_of_image Loaded.codeWF Layout.code_F_7801aed0 F_7801aed0.decode_ok hcode)
    (codeWithin_C hcode) hro hh hr hr1 hsp hstk
    (fun v sp'' L'' h1 h2 => hhandle_al v sp'' L'' h1 (h2.trans hcode)) ?_ hk
  intro v sp'' L'' h1 h2 h3 h4 h5 h6 h7 hro' hh' k
  exact alloc_at 3 h1 (h2.trans hcode) h3 (by decide) h4 h5 h6 (Nat.le_refl _) (by omega) (by decide) (.inr h7) hro' hh'
    fun t ptr B a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 _ =>
      k t ptr B a1 a2 a3 a4 a5 a6 a7 a8 a9.toText a10 a11 a12

end Cases.Zip2005.Run
