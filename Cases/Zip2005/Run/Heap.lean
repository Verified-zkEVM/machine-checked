/-
  Cases.Zip2005.Run.Heap

  The invariant the run keeps of the heap and the owned statics (milestone M1), in the form the
  executor carries (`MachineChecked.RiscV.Sym.Carry`).

  `HeapAt L s`: the public-values hasher is `Some` with its position below 64
  (`Owned.HasherOk`); rlsf's heap is well formed (`Tlsf.Rep`), with its sentinel at
  `7 << 34 - 32`; and each buffer of the live list `L` is null or the payload of a used block,
  from the payload's start. All of this reads only *closed* memory: the hasher's tag and
  position, the allocator's control block, every block's header and back link, and every free
  block. Open memory -- below the control block (the stack, the image, `.data`), the hasher's
  state and buffer, the statics between the hasher and the arena (`FP_TABLES`), memory above
  the arena (the hint area), and the live buffers -- may be written freely
  (`heapAt_of`). So the executor keeps `HeapAt L` through every store and call that stays in
  open memory, and only the allocator's own specifications change it.

  The live list is the run's ghost state: which heap buffers the code still holds. A buffer
  enters it when `__rust_alloc` grants it and leaves when `__rust_dealloc` frees it.
-/

import Cases.Zip2005.HeapEnv
import MachineChecked.RiscV.Sym.Carry
import Cases.Zip2005.Runtime.Tlsf.Init

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 MachineChecked.RiscV.Sym MachineChecked.RiscV.Check Cases.Zip2005 Cases.Zip2005.Runtime

/-- `INNER_HEAP`, the allocator's control block. -/
abbrev HEAP : Word := 0x78040620#64

/-- The arena's first block, `_end`. -/
abbrev BASE : Word := 0x78048980#64

/-- The arena's end, `7 << 34`: `__start` hands `Heap::init` `[_end, 7 << 34)`. -/
def TOP : Nat := 0x1c00000000

/-- The sentinel block `Heap::init` places at the arena's end. -/
def sentinel : Tlsf.Blk := ⟨0x1bffffffe0#64, 0x20#64, true, true⟩

/-- The open ranges: below the control block; the hasher's state and buffer, between its tag
    and its position; the statics after the hasher up to the arena, but for the two hooks
    (`std::alloc::HOOK` at `0x78048920`, the panic hook at `0x78048948`); above the arena. -/
def ranges : List (Nat × Nat) :=
  [(0, 0x78040620), (0x78048838, 0x780488a0), (0x780488a8, 0x78048920), (0x78048928, 0x78048948),
    (0x78048960, 0x78048980), (0x1c00000000, 2 ^ 64)]

/-- The hooks' doublewords: the checker's protected statics (`Contract.env.prot`). -/
def hookKeys : List Word := [0x78048920#64, 0x78048948#64, 0x78048950#64, 0x78048958#64]

/-- A live buffer: null (and small), or the payload of a used block from its start. -/
def LiveOk (bs : List Tlsf.Blk) (r : Word × Nat) : Prop :=
  (r.1 = 0#64 ∧ 8 * r.2 ≤ 0x78040620) ∨
  ∃ b ∈ bs, b.used = true ∧ b.last = false ∧ b.a + 16#64 = r.1 ∧
    r.1.toNat + 8 * r.2 ≤ b.a.toNat + b.sz.toNat

/-- No two live buffers but null ones share a pointer: each names its own block. -/
def Distinct (L : List (Word × Nat)) : Prop := L.Pairwise fun a b => a.1 = 0#64 ∨ a.1 ≠ b.1

/-- The invariant, of a memory: the hooks unset (at their load values), the hasher's, and the
    heap well formed with its sentinel and the live buffers, each its own block's. -/
def Q (L : List (Word × Nat)) (m : Word → Word) : Prop :=
  (∀ k ∈ hookKeys, m k = Contract.env.init k) ∧ Owned.HasherOk m ∧ Distinct L ∧
    ∃ bs Lf, Tlsf.Rep HEAP BASE m bs Lf ∧ sentinel ∈ bs ∧ ∀ r ∈ L, LiveOk bs r

/-- **The run's invariant**, as the executor carries it. -/
abbrev HeapAt (L : List (Word × Nat)) (s : MachineState) : Prop := Carry ranges Q L s

/-! ## Where the blocks lie -/

/-- Every block of a chain ends at or before the end of a last block of it. -/
theorem Chain.le_last {m : Word → Word} :
    ∀ {bs : List Tlsf.Blk} {a p : Word}, Tlsf.Chain m a p bs →
      (∀ b ∈ bs, b.a.toNat + b.sz.toNat < 2 ^ 40) →
      ∀ c ∈ bs, c.last = true → ∀ b ∈ bs, b.a.toNat + b.sz.toNat ≤ c.a.toNat + c.sz.toNat
  | [], _, _, h, _, _, _, _, _, _ => h.elim
  | b0 :: bs, a, p, h, hl, c, hc, hcl, b, hb => by
    have hsort := (Tlsf.Chain.sorted h hl)
    obtain ⟨h1, _, _, _, _, h6⟩ := h
    split at h6
    · rw [h6.1] at hc hb
      simp only [List.mem_singleton] at hc hb
      subst hc hb; exact Nat.le_refl _
    · rename_i hb0
      have hc' : c ∈ bs := by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact absurd hcl (by simpa using hb0)
        · exact hc
      have hl' : ∀ b ∈ bs, b.a.toNat + b.sz.toNat < 2 ^ 40 := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases List.mem_cons.mp hb with rfl | hb
      · have hge := (Tlsf.Chain.sorted h6 hl').2 c hc'
        have hb0l := hl b (List.mem_cons_self ..)
        have he : (b.a + b.sz).toNat = b.a.toNat + b.sz.toNat := by
          rw [BitVec.toNat_add]; omega
        rw [← h1] at hge
        omega
      · exact Chain.le_last h6 hl' c hc' hcl b hb

/-- With the sentinel in the heap, every block ends by `TOP`. -/
theorem end_le {m : Word → Word} {bs : List Tlsf.Blk} {Lf : Word → Word → List Word}
    (h : Tlsf.Rep HEAP BASE m bs Lf) (hs : sentinel ∈ bs) {b : Tlsf.Blk} (hb : b ∈ bs) :
    b.a.toNat + b.sz.toNat ≤ TOP := by
  have := Chain.le_last h.chain h.layout.2.2 sentinel hs rfl b hb
  simpa [sentinel, TOP] using this

/-- Every block starts at or past `BASE`. -/
theorem base_le {m : Word → Word} {bs : List Tlsf.Blk} {Lf : Word → Word → List Word}
    (h : Tlsf.Rep HEAP BASE m bs Lf) {b : Tlsf.Blk} (hb : b ∈ bs) : 0x78048980 ≤ b.a.toNat := by
  have := (Tlsf.rep_iff.mp h).2.blk hb
  simpa using this.2.1

/-- A live buffer's bytes are below the control block, or past `BASE + 16` inside its block. -/
theorem live_range {m : Word → Word} {bs : List Tlsf.Blk} {Lf : Word → Word → List Word}
    (h : Tlsf.Rep HEAP BASE m bs Lf) {r : Word × Nat} (hr : LiveOk bs r) {a : Word}
    (ha : InRegion a r.1 r.2) :
    a.toNat < 0x78040620 ∨ ∃ c ∈ bs, c.used = true ∧ c.a.toNat + 16 ≤ a.toNat ∧
      a.toNat < c.a.toNat + c.sz.toNat := by
  unfold InRegion at ha
  rcases hr with ⟨h0, hk⟩ | ⟨c, hc, hcu, _, hca, hcz⟩
  · left; rw [h0] at ha; simp at ha; omega
  · right
    refine ⟨c, hc, hcu, ?_, by omega⟩
    have hA := (Tlsf.rep_iff.mp h).2.blkA hc
    have hl := (Tlsf.rep_iff.mp h).2.layout.2.2 c hc
    have : (c.a + 16#64).toNat = c.a.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
    rw [← hca, this] at ha; omega

/-! ## The invariant reads closed memory only -/

theorem not_open_lo {L : List (Word × Nat)} {m : Word → Word} {bs : List Tlsf.Blk}
    {Lf : Word → Word → List Word} (h : Tlsf.Rep HEAP BASE m bs Lf) (hL : ∀ r ∈ L, LiveOk bs r)
    {a : Word} (h1 : 0x78040620 ≤ a.toNat) (h2 : a.toNat < 0x78048838) :
    ¬ Open ranges L a := by
  rintro (⟨r, hr, hr1, hr2⟩ | ⟨r, hr, hin⟩)
  · simp only [ranges, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hr1 hr2 <;> omega
  · rcases live_range h (hL r hr) hin with h3 | ⟨c, hc, _, h3, _⟩
    · omega
    · have := base_le h hc; omega

/-- A key of the shape lies in the control block or in a block's first 32 bytes. -/
theorem not_open_key {L : List (Word × Nat)} {m : Word → Word} {bs : List Tlsf.Blk}
    {Lf : Word → Word → List Word} (h : Tlsf.Rep HEAP BASE m bs Lf) (hs : sentinel ∈ bs)
    (hL : ∀ r ∈ L, LiveOk bs r) {a : Word} (hk : Tlsf.Key HEAP bs a) : ¬ Open ranges L a := by
  have hsh := (Tlsf.rep_iff.mp h).2
  rcases hk with hk | ⟨b, hb, hk⟩
  · simp only [Tlsf.InCtl, Tlsf.ctlSize] at hk
    exact not_open_lo h hL (by simp at hk; omega) (by simp at hk; omega)
  · have hA := hsh.blkA hb
    have hbz := Tlsf.Shape.sz_ge (hsh.blk hb).2.2.2.2
    have hend := end_le h hs hb
    have hbase := base_le h hb
    have h8 : ∀ c : Word, c.toNat < 32 → (b.a + c).toNat = b.a.toNat + c.toNat := fun c hc => by
      rw [BitVec.toNat_add]; omega
    -- the key's offset into its block, below 32 and below the block's size
    obtain ⟨d, hd, hdb⟩ : ∃ d : Nat, d < 32 ∧ a.toNat = b.a.toNat + d ∧
        (16 ≤ d → b.used = false) := by
      rcases hk with rfl | rfl | ⟨hu, rfl | rfl⟩
      · exact ⟨0, by omega, by omega, by omega⟩
      · exact ⟨8, by omega, by rw [h8 _ (by decide)]; rfl, by omega⟩
      · exact ⟨16, by omega, by rw [h8 _ (by decide)]; rfl, fun _ => hu⟩
      · exact ⟨24, by omega, by rw [h8 _ (by decide)]; rfl, fun _ => hu⟩
    rintro (⟨r, hr, hr1, hr2⟩ | ⟨r, hr, hin⟩)
    · simp only [ranges, List.mem_cons, List.mem_nil_iff, or_false] at hr
      simp only [TOP] at hend
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hr1 hr2 <;> omega
    · rcases live_range h (hL r hr) hin with h3 | ⟨c, hc, hcu, h3, h4⟩
      · omega
      · by_cases hbc : b = c
        · subst hbc
          have := hdb.2
          by_cases h16 : 16 ≤ d
          · rw [this h16] at hcu; exact absurd hcu (by simp)
          · omega
        · rcases hsh.disj hb hc hbc with h5 | h5 <;> omega

/-- A closed doubleword of the statics: between the control block and the arena, outside every
    open range there. -/
theorem not_open_static {L : List (Word × Nat)} {m : Word → Word} {bs : List Tlsf.Blk}
    {Lf : Word → Word → List Word} (h : Tlsf.Rep HEAP BASE m bs Lf) (hL : ∀ r ∈ L, LiveOk bs r)
    {a : Word} (h1 : 0x78040620 ≤ a.toNat) (h2 : a.toNat < 0x78048980)
    (h3 : ∀ r ∈ ranges, ¬ (r.1 ≤ a.toNat ∧ a.toNat < r.2)) : ¬ Open ranges L a := by
  rintro (⟨r, hr, hr1, hr2⟩ | ⟨r, hr, hin⟩)
  · exact h3 r hr ⟨hr1, hr2⟩
  · rcases live_range h (hL r hr) hin with h4 | ⟨c, hc, _, h4, _⟩
    · omega
    · have := base_le h hc; omega

/-- **The frame**: the invariant reads closed memory only. -/
theorem q_frame {L : List (Word × Nat)} {m m' : Word → Word} (h : Q L m)
    (hm : ∀ a, ¬ Open ranges L a → m' a = m a) : Q L m' := by
  obtain ⟨hhk, ⟨ht, hp⟩, hD, bs, Lf, hrep, hs, hL⟩ := h
  have hcl : ∀ a, 0x78040620 ≤ a.toNat → a.toNat < 0x78048838 → m' a = m a :=
    fun a h1 h2 => hm a (not_open_lo hrep hL h1 h2)
  have hst : ∀ a, 0x78040620 ≤ a.toNat → a.toNat < 0x78048980 →
      (∀ r ∈ ranges, ¬ (r.1 ≤ a.toNat ∧ a.toNat < r.2)) → m' a = m a :=
    fun a h1 h2 h3 => hm a (not_open_static hrep hL h1 h2 h3)
  refine ⟨fun k hk => ?_, ⟨?_, ?_⟩, hD, bs, Lf, ?_, hs, hL⟩
  · simp only [hookKeys, List.mem_cons, List.mem_nil_iff, or_false] at hk
    rw [← hhk k (by simp [hookKeys, hk])]
    rcases hk with rfl | rfl | rfl | rfl <;>
      exact hst _ (by decide) (by decide) (by simp [ranges])
  · rw [Owned.tagKey, hcl _ (by decide) (by decide)]; exact ht
  · rw [Owned.posKey, hst _ (by decide) (by decide) (by simp [ranges])]; exact hp
  · obtain ⟨hl, hsh⟩ := Tlsf.rep_iff.mp hrep
    refine Tlsf.rep_iff.mpr ⟨?_, hsh.congr fun a ha => hm a (not_open_key hrep hs hL ha)⟩
    rw [hcl _ (by decide) (by decide)]; exact hl

/-- The invariant survives dropping and reordering live buffers. -/
theorem q_sub {L L' : List (Word × Nat)} (hs : L'.Subperm L) {m : Word → Word} (h : Q L m) :
    Q L' m := by
  obtain ⟨hk, hh, hD, bs, Lf, hr, hsn, hL⟩ := h
  obtain ⟨l, hp, hsl⟩ := hs
  have hDl : Distinct l := hD.sublist hsl
  have hD' : Distinct L' := (List.Perm.pairwise_iff (fun {a b} h => by
    rcases h with h | h
    · by_cases hb : b.1 = 0#64
      · exact .inl hb
      · exact .inr (fun e => hb (e ▸ h))
    · exact .inr (Ne.symm h)) hp).mp hDl
  exact ⟨hk, hh, hD', bs, Lf, hr, hsn, fun r hr => hL r (hsl.subset (hp.symm.subset hr))⟩

/-- The invariant of a state, from its memory's. -/
theorem heapAt_of {L : List (Word × Nat)} {s : MachineState} (h : Q L s.getMem) : HeapAt L s :=
  Carry.intro h (fun _ _ h hm => q_frame h hm) fun _ hs _ h => q_sub hs h

/-- A shorter live list. -/
theorem HeapAt.sub {L L' : List (Word × Nat)} {s : MachineState} (h : HeapAt L s)
    (hsub : L'.Sublist L) : HeapAt L' s := h.sublist hsub

/-- At `main`'s entry: the hasher set up, the heap one free block, nothing live. -/
theorem mainEntry_heapAt {input : List (BitVec 8)} {t : MachineState}
    (h : Entry.MainEntry input t) : HeapAt [] t :=
  heapAt_of ⟨fun k hk => by
      simp only [hookKeys, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact h.prot (Env.inProt_of_mem Statics.allocHook_prot (by simp [Region.Mem, Region.hi, Statics.allocHook]))
      · exact h.prot (Env.inProt_of_mem Statics.panicHook_prot (by simp [Region.Mem, Region.hi, Statics.panicHook]))
      · exact h.prot (Env.inProt_of_mem Statics.panicHook_prot (by simp [Region.Mem, Region.hi, Statics.panicHook]))
      · exact h.prot (Env.inProt_of_mem Statics.panicHook_prot (by simp [Region.Mem, Region.hi, Statics.panicHook])),
    Owned.inv_iff.mp (Owned.mainEntry_inv h), List.Pairwise.nil, Tlsf.bs0, Tlsf.L0,
    Tlsf.rep_init h.2.2.2.2.2.1, by simp [Tlsf.bs0, sentinel], by simp⟩

/-- The public-values hasher is `Some`: its tag. -/
theorem HeapAt.tag {L : List (Word × Nat)} {s : MachineState} (h : HeapAt L s) :
    s.getMem 0x78048830#64 = 1#64 :=
  h.holds.2.1.1

/-- Its buffer position is below 64. -/
theorem HeapAt.pos {L : List (Word × Nat)} {s : MachineState} (h : HeapAt L s) :
    (s.getMem 0x780488a0#64 &&& 0xff#64).toNat < 64 :=
  h.holds.2.1.2

end Cases.Zip2005.Run
