/-
  Cases.Zip2005.Runtime.Tlsf.Heap

  Facts about the heap model, independent of the code (phase D4).

  `Shape` is `Rep` without the lock, and with a set of *detached* free blocks: blocks the
  chain still marks free but that no free list holds. `alloc` detaches the block it pops,
  then marks it used (or splits it and files the remainder); between the two the heap is a
  `Shape` with that block out.

  The chain tiles the arena: blocks lie in address order, each where the previous one ends,
  all 32-aligned, below `2^40`. So the doublewords the model reads — headers at `+0`/`+8`,
  free-list links at `+0x10`/`+0x18`, the control block's heads and bitmaps — are pairwise
  distinct, and a write to one leaves the others alone.
-/

import Cases.Zip2005.Runtime.Tlsf.Model

namespace Cases.Zip2005.Runtime.Tlsf

/-! ## Memory updates -/

/-- Memory with one doubleword replaced, as `setMem` leaves it. -/
def upd (m : Word → Word) (k v : Word) : Word → Word := fun a => if a = k then v else m a

@[simp] theorem upd_same (m : Word → Word) (k v : Word) : upd m k v k = v := by simp [upd]

theorem upd_ne {m : Word → Word} {k v a : Word} (h : a ≠ k) : upd m k v a = m a := by
  simp [upd, h]

/-- 32-byte alignment: blocks and the arena's base. -/
def A32 (x : Word) : Prop := x &&& 31#64 = 0#64

theorem A32.add {x y : Word} (hx : A32 x) (hy : A32 y) : A32 (x + y) := by
  unfold A32 at *; bv_decide

/-- Doublewords at different offsets of 32-aligned blocks are different. -/
theorem A32.ne_off {x y c d : Word} (hx : A32 x) (hy : A32 y) (hc : c < 32#64) (hd : d < 32#64)
    (hcd : c ≠ d) : x + c ≠ y + d := by
  unfold A32 at *; bv_decide

/-- The same offset of different blocks. -/
theorem ne_add_right {x y c : Word} (h : x ≠ y) : x + c ≠ y + c := fun e =>
  h (by bv_omega)

/-! ## Chain segments -/

/-- Blocks `bs` laid from `a` (with predecessor `p`) up to `a'` (whose predecessor is `p'`),
    none of them the sentinel. -/
def Seg (m : Word → Word) : Word → Word → List Blk → Word → Word → Prop
  | a, p, [], a', p' => a = a' ∧ p = p'
  | a, p, b :: bs, a', p' => b.a = a ∧ m a = b.hdr ∧ m (a + 8#64) = p ∧ b.sz &&& 31#64 = 0#64 ∧
      SizeOk b.sz ∧ b.last = false ∧ Seg m (a + b.sz) a bs a' p'

/-- A chain splits at any point before its end. -/
theorem chain_append {m : Word → Word} {pre post : List Blk} (hpost : post ≠ []) :
    ∀ {a p}, Chain m a p (pre ++ post) ↔ ∃ a' p', Seg m a p pre a' p' ∧ Chain m a' p' post := by
  induction pre with
  | nil =>
    intro a p
    exact ⟨fun h => ⟨a, p, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h1, h2⟩, h⟩ => h1 ▸ h2 ▸ h⟩
  | cons b pre ih =>
    intro a p
    have hne : pre ++ post ≠ [] := by simp [hpost]
    simp only [List.cons_append, Chain, Seg]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      cases hl : b.last
      · rw [hl] at h6
        obtain ⟨a', p', hs, hc⟩ := (ih).mp (by simpa using h6)
        exact ⟨a', p', ⟨h1, h2, h3, h4, h5, rfl, hs⟩, hc⟩
      · rw [hl] at h6; exact absurd h6.1 hne
    · rintro ⟨a', p', ⟨h1, h2, h3, h4, h5, h6, hs⟩, hc⟩
      exact ⟨h1, h2, h3, h4, h5, by rw [h6]; exact (ih).mpr ⟨a', p', hs, hc⟩⟩

/-- A segment depends only on its blocks' headers. -/
theorem Seg.congr {m m' : Word → Word} :
    ∀ {bs a p a' p'}, Seg m a p bs a' p' →
      (∀ b ∈ bs, m' b.a = m b.a ∧ m' (b.a + 8#64) = m (b.a + 8#64)) → Seg m' a p bs a' p'
  | [], _, _, _, _, h, _ => h
  | b :: bs, a, p, a', p', ⟨h1, h2, h3, h4, h5, h6, hs⟩, hm => by
    obtain ⟨e1, e2⟩ := hm b (List.mem_cons_self ..)
    refine ⟨h1, ?_, ?_, h4, h5, h6, hs.congr fun c hc => hm c (List.mem_cons_of_mem _ hc)⟩
    · rw [← h1, e1, h1, h2]
    · rw [← h1, e2, h1, h3]

/-- So does a chain. -/
theorem Chain.congr {m m' : Word → Word} :
    ∀ {bs a p}, Chain m a p bs →
      (∀ b ∈ bs, m' b.a = m b.a ∧ m' (b.a + 8#64) = m (b.a + 8#64)) → Chain m' a p bs
  | [], _, _, h, _ => h
  | b :: bs, a, p, ⟨h1, h2, h3, h4, h5, h6⟩, hm => by
    obtain ⟨e1, e2⟩ := hm b (List.mem_cons_self ..)
    refine ⟨h1, ?_, ?_, h4, h5, ?_⟩
    · rw [← h1, e1, h1, h2]
    · rw [← h1, e2, h1, h3]
    · split
      · rename_i hl; rw [if_pos hl] at h6; exact h6
      · rename_i hl; rw [if_neg hl] at h6
        exact h6.congr fun c hc => hm c (List.mem_cons_of_mem _ hc)

/-! ## The chain tiles the arena -/

/-- Each block of a chain is a granule multiple of a proper size. -/
theorem Chain.sizes {m : Word → Word} :
    ∀ {bs a p}, Chain m a p bs → ∀ b ∈ bs, b.sz &&& 31#64 = 0#64 ∧ SizeOk b.sz
  | [], _, _, h, _, _ => h.elim
  | b :: bs, a, p, ⟨_, _, _, h4, h5, h6⟩, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨h4, h5⟩
    · split at h6
      · rw [h6.1] at hc; simp at hc
      · exact Chain.sizes h6 c hc

/-- In address order, each block ending at or before the next begins, all from `a`. -/
theorem Chain.sorted {m : Word → Word} :
    ∀ {bs a p}, Chain m a p bs → (∀ b ∈ bs, b.a.toNat + b.sz.toNat < 2 ^ 40) →
      bs.Pairwise (fun b c => b.a.toNat + b.sz.toNat ≤ c.a.toNat) ∧ ∀ b ∈ bs, a.toNat ≤ b.a.toNat
  | [], _, _, h, _ => h.elim
  | b :: bs, a, p, ⟨h1, _, _, _, _, h6⟩, hl => by
    subst h1
    have hb := hl b (List.mem_cons_self ..)
    split at h6
    · rw [h6.1]; simp
    · obtain ⟨hp, hge⟩ := Chain.sorted h6 fun c hc => hl c (List.mem_cons_of_mem _ hc)
      have he : (b.a + b.sz).toNat = b.a.toNat + b.sz.toNat := by
        rw [BitVec.toNat_add]; omega
      refine ⟨List.Pairwise.cons (fun c hc => by have := hge c hc; omega) hp, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Nat.le_refl _
      · have := hge c hc; omega

/-- Each block of a chain from an aligned address is aligned. -/
theorem Chain.aligned {m : Word → Word} :
    ∀ {bs a p}, Chain m a p bs → A32 a → ∀ b ∈ bs, A32 b.a
  | [], _, _, h, _, _, _ => h.elim
  | b :: bs, a, p, ⟨h1, _, _, h4, _, h6⟩, ha, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [h1]; exact ha
    · split at h6
      · rw [h6.1] at hc; simp at hc
      · exact Chain.aligned h6 (ha.add h4) c hc

/-- The sentinel is the last block, and only it. -/
theorem Chain.last_used {m : Word → Word} :
    ∀ {bs a p}, Chain m a p bs → ∀ b ∈ bs, b.last = true → b.used = true
  | [], _, _, h, _, _, _ => h.elim
  | b :: bs, a, p, ⟨_, _, _, _, _, h6⟩, c, hc, hl => by
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [if_pos hl] at h6; exact h6.2.2
    · split at h6
      · rw [h6.1] at hc; simp at hc
      · exact Chain.last_used h6 c hc hl

/-- Two members of a list ordered pairwise are ordered one way or the other. -/
theorem pairwise_or {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {x y}, x ∈ l → y ∈ l → x ≠ y → R x y ∨ R y x
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · exact absurd (ex.trans ey.symm) hne
    · subst ex; exact .inl (h.1 y hy')
    · subst ey; exact .inr (h.1 x hx')
    · exact pairwise_or h.2 hx' hy' hne

/-- A free list depends only on its nodes' links. -/
theorem Dll.congr {m m' : Word → Word} :
    ∀ {xs p}, Dll m p xs →
      (∀ x ∈ xs, m' (x + 0x10#64) = m (x + 0x10#64) ∧ m' (x + 0x18#64) = m (x + 0x18#64)) →
      Dll m' p xs
  | [], _, h, _ => h
  | x :: xs, p, ⟨h1, h2, h3⟩, hm => by
    obtain ⟨e1, e2⟩ := hm x (List.mem_cons_self ..)
    exact ⟨e2.trans h1, e1.trans h2, h3.congr fun y hy => hm y (List.mem_cons_of_mem _ hy)⟩

/-! ## The control block -/

/-- The control block's addresses do not wrap. -/
def CtlOk (self : Word) : Prop := self.toNat + ctlSize < 2 ^ 64

theorem headAddr_toNat {self f s : Word} (h : CtlOk self) (hf : f < 64#64) (hs : s < 64#64) :
    (headAddr self f s).toNat = self.toNat + 8 + f.toNat * 512 + s.toNat * 8 := by
  unfold CtlOk ctlSize at h
  unfold headAddr
  rw [BitVec.lt_def] at hf hs
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at *
  omega

theorem slBm_toNat {self f : Word} (h : CtlOk self) (hf : f < 64#64) :
    (slBm self f).toNat = self.toNat + 0x8008 + f.toNat * 8 := by
  unfold CtlOk ctlSize at h
  unfold slBm
  rw [BitVec.lt_def] at hf
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at *
  omega

theorem flBm_toNat {self : Word} (h : CtlOk self) : (flBm self).toNat = self.toNat + 0x8208 := by
  unfold CtlOk ctlSize at h
  unfold flBm
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem headAddr_inj {self f s f' s' : Word} (hf : f < 64#64) (hs : s < 64#64)
    (hf' : f' < 64#64) (hs' : s' < 64#64) (h : headAddr self f s = headAddr self f' s') :
    f = f' ∧ s = s' := by
  unfold headAddr at h; bv_decide

theorem slBm_inj {self f f' : Word} (hf : f < 64#64) (hf' : f' < 64#64)
    (h : slBm self f = slBm self f') : f = f' := by
  unfold slBm at h; bv_decide

theorem headAddr_ne_slBm {self f s f' : Word} (hf : f < 64#64) (hs : s < 64#64)
    (hf' : f' < 64#64) : headAddr self f s ≠ slBm self f' := by
  unfold headAddr slBm; bv_decide

theorem headAddr_ne_flBm {self f s : Word} (hf : f < 64#64) (hs : s < 64#64) :
    headAddr self f s ≠ flBm self := by
  unfold headAddr flBm; bv_decide

theorem slBm_ne_flBm {self f : Word} (hf : f < 64#64) : slBm self f ≠ flBm self := by
  unfold slBm flBm; bv_decide

/-- Inside the control block, past the lock. -/
def InCtl (self a : Word) : Prop := self.toNat + 8 ≤ a.toNat ∧ a.toNat < self.toNat + ctlSize

theorem headAddr_inCtl {self f s : Word} (h : CtlOk self) (hf : f < 64#64) (hs : s < 64#64) :
    InCtl self (headAddr self f s) := by
  rw [InCtl, headAddr_toNat h hf hs]
  rw [BitVec.lt_def] at hf hs
  simp only [BitVec.toNat_ofNat, ctlSize] at *
  omega

theorem slBm_inCtl {self f : Word} (h : CtlOk self) (hf : f < 64#64) : InCtl self (slBm self f) := by
  rw [InCtl, slBm_toNat h hf]
  rw [BitVec.lt_def] at hf
  simp only [BitVec.toNat_ofNat, ctlSize] at *
  omega

theorem flBm_inCtl {self : Word} (h : CtlOk self) : InCtl self (flBm self) := by
  rw [InCtl, flBm_toNat h]; simp only [ctlSize]; omega

/-! ## `Shape`: the heap without its lock, some free blocks detached -/

/-- **The heap, lock aside, with the blocks `out` detached**: free in the chain, filed in no
    list. -/
structure Shape (ctl base : Word) (m : Word → Word) (bs : List Blk)
    (L : Word → Word → List Word) (out : Word → Prop) : Prop where
  chain : Chain m base 0 bs
  layout : ctl.toNat + ctlSize ≤ base.toNat ∧ base &&& 31#64 = 0#64 ∧
    ∀ b ∈ bs, b.a.toNat + b.sz.toNat < 2 ^ 40
  heads : ∀ f s, f < 64#64 → s < 64#64 → m (headAddr ctl f s) = (L f s).headD 0
  links : ∀ f s, Dll m 0 (L f s)
  filed : ∀ b ∈ bs, b.used = false → ¬ out b.a → b.a ∈ L (flOf b.sz) (slOf b.sz)
  members : ∀ f s x, x ∈ L f s → ¬ out x ∧
    ∃ b ∈ bs, b.a = x ∧ b.used = false ∧ flOf b.sz = f ∧ slOf b.sz = s
  range : ∀ f s, (L f s ≠ []) → f < 64#64 ∧ s < 64#64
  nodup : ∀ f s, (L f s).Nodup
  slbm : ∀ f s, f < 64#64 → s < 64#64 →
    (m (slBm ctl f)).getLsbD s.toNat = !(L f s).isEmpty
  flbm : ∀ f, f < 64#64 →
    (m (flBm ctl)).getLsbD f.toNat = !(m (slBm ctl f) == 0)

/-- `Rep` is the lock free and the shape with nothing detached. -/
theorem rep_iff {self base : Word} {m : Word → Word} {bs : List Blk}
    {L : Word → Word → List Word} :
    Rep self base m bs L ↔ m self = 0 ∧ Shape self base m bs L (fun _ => False) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨h1, h2, h3, h4, h5, fun b hb hu _ => h6 b hb hu, fun f s x hx => ⟨id, h7 f s x hx⟩,
      h8, h9, h10, h11⟩
  · rintro ⟨hl, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    exact ⟨hl, h2, h3, h4, h5, fun b hb hu => h6 b hb hu id, fun f s x hx => (h7 f s x hx).2,
      h8, h9, h10, h11⟩

/-- The doublewords the shape reads: the control block past the lock, every header, and the
    links of every free block. -/
def Key (self : Word) (bs : List Blk) (a : Word) : Prop :=
  InCtl self a ∨ ∃ b ∈ bs, a = b.a ∨ a = b.a + 8#64 ∨
    (b.used = false ∧ (a = b.a + 0x10#64 ∨ a = b.a + 0x18#64))

namespace Shape

variable {self base : Word} {m : Word → Word} {bs : List Blk} {L : Word → Word → List Word}
  {out : Word → Prop}

theorem ctlOk (h : Shape self base m bs L out) : CtlOk self := by
  have := base.isLt; have := h.layout.1; unfold CtlOk; omega

/-- **Frame.** The shape survives any change away from its keys. -/
theorem congr (h : Shape self base m bs L out) {m' : Word → Word}
    (hm : ∀ a, Key self bs a → m' a = m a) : Shape self base m' bs L out := by
  have hc := h.ctlOk
  refine ⟨h.chain.congr fun b hb => ⟨hm _ (.inr ⟨b, hb, .inl rfl⟩),
      hm _ (.inr ⟨b, hb, .inr (.inl rfl)⟩)⟩, h.layout,
    fun f s hf hs => (hm _ (.inl (headAddr_inCtl hc hf hs))).trans (h.heads f s hf hs),
    fun f s => (h.links f s).congr fun x hx => ?_, h.filed, h.members, h.range, h.nodup,
    fun f s hf hs => by rw [hm _ (.inl (slBm_inCtl hc hf))]; exact h.slbm f s hf hs,
    fun f hf => by
      rw [hm _ (.inl (flBm_inCtl hc)), hm _ (.inl (slBm_inCtl hc hf))]; exact h.flbm f hf⟩
  obtain ⟨_, b, hb, rfl, hu, _⟩ := h.members f s x hx
  exact ⟨hm _ (.inr ⟨b, hb, .inr (.inr ⟨hu, .inl rfl⟩)⟩),
    hm _ (.inr ⟨b, hb, .inr (.inr ⟨hu, .inr rfl⟩)⟩)⟩

/-- Where a block lies. -/
theorem blk (h : Shape self base m bs L out) {b : Blk} (hb : b ∈ bs) :
    A32 b.a ∧ base.toNat ≤ b.a.toNat ∧ b.a.toNat + b.sz.toNat < 2 ^ 40 ∧
      b.sz &&& 31#64 = 0#64 ∧ SizeOk b.sz :=
  ⟨h.chain.aligned h.layout.2.1 b hb, (h.chain.sorted h.layout.2.2).2 b hb, h.layout.2.2 b hb,
    h.chain.sizes b hb⟩

theorem sz_ge {s : Word} (h : SizeOk s) : 32 ≤ s.toNat := by
  have := h.1; rw [BitVec.le_def] at this; simpa using this

/-- Different blocks do not overlap. -/
theorem disj (h : Shape self base m bs L out) {b c : Blk} (hb : b ∈ bs) (hc : c ∈ bs)
    (hne : b ≠ c) :
    b.a.toNat + b.sz.toNat ≤ c.a.toNat ∨ c.a.toNat + c.sz.toNat ≤ b.a.toNat :=
  pairwise_or (h.chain.sorted h.layout.2.2).1 hb hc hne

/-- A block is determined by its address. -/
theorem uniq (h : Shape self base m bs L out) {b c : Blk} (hb : b ∈ bs) (hc : c ∈ bs)
    (he : b.a = c.a) : b = c := by
  refine Classical.byContradiction fun hne => ?_
  have := sz_ge (h.blk hb).2.2.2.2
  have := sz_ge (h.blk hc).2.2.2.2
  rcases h.disj hb hc hne with h1 | h1 <;> rw [he] at h1 <;> omega

/-- A node of a free list: a free block of its class. -/
theorem node (h : Shape self base m bs L out) {f s x : Word} (hx : x ∈ L f s) :
    ∃ b ∈ bs, b.a = x ∧ b.used = false ∧ flOf b.sz = f ∧ slOf b.sz = s :=
  (h.members f s x hx).2

/-- A node is filed in one list. -/
theorem class_uniq (h : Shape self base m bs L out) {f s f' s' x : Word} (hx : x ∈ L f s)
    (hx' : x ∈ L f' s') : f = f' ∧ s = s' := by
  obtain ⟨b, hb, rfl, _, rfl, rfl⟩ := h.node hx
  obtain ⟨c, hc, he, _, rfl, rfl⟩ := h.node hx'
  rw [h.uniq hb hc he.symm]; exact ⟨rfl, rfl⟩

theorem node_ne_zero (h : Shape self base m bs L out) {f s x : Word} (hx : x ∈ L f s) :
    x ≠ 0#64 := by
  obtain ⟨b, hb, rfl, _⟩ := h.node hx
  have h1 := (h.blk hb).2.1
  have := h.layout.1
  intro he; rw [he] at h1; simp [ctlSize] at *; omega

/-- A doubleword within 32 bytes of a block lies past the control block. -/
theorem arena_ne_ctl (h : Shape self base m bs L out) {z c k : Word} (hz : base.toNat ≤ z.toNat)
    (hz' : z.toNat < 2 ^ 40) (hc : c < 32#64) (hk : k.toNat < self.toNat + ctlSize) :
    z + c ≠ k := by
  intro he
  have := h.layout.1
  rw [BitVec.lt_def] at hc
  have : (z + c).toNat = z.toNat + c.toNat := by
    rw [BitVec.toNat_add]; simp at hc; omega
  rw [he] at this; omega

end Shape

/-! ## Popping a free list -/

theorem key_eq {x y c d : Word} (hx : A32 x) (hy : A32 y) (hc : c < 32#64) (hd : d < 32#64)
    (h : x + c = y + d) : x = y ∧ c = d := by
  unfold A32 at *; bv_decide

/-- Doublewords of 32-aligned blocks differ unless block and offset agree. -/
theorem key_ne {x y c d : Word} (hx : A32 x) (hy : A32 y) (hc : c < 32#64) (hd : d < 32#64)
    (h : x ≠ y ∨ c ≠ d) : x + c ≠ y + d := fun e => by
  have := key_eq hx hy hc hd e
  rcases h with h | h
  · exact h this.1
  · exact h this.2

theorem key_ne0 {x y d : Word} (hx : A32 x) (hy : A32 y) (hd : d < 32#64)
    (h : x ≠ y ∨ 0#64 ≠ d) : x ≠ y + d := by
  have := key_ne hx hy (by decide) hd h; simpa using this

theorem getLsbD_clr (x : Word) {k i : Nat} (hk : k < 64) :
    (x &&& ~~~(1#64 <<< k)).getLsbD i = (x.getLsbD i && !decide (i = k)) := by
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  by_cases hi : i < 64 <;> by_cases hik : i = k <;> simp_all <;> omega

theorem getLsbD_set (x : Word) {k i : Nat} (hk : k < 64) :
    (x ||| (1#64 <<< k)).getLsbD i = (x.getLsbD i || decide (i = k)) := by
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases hi : i < 64 <;> by_cases hik : i = k <;> simp_all <;> omega

theorem lt64 {f : Word} (h : f < 64#64) : f.toNat < 64 := by
  rw [BitVec.lt_def] at h; simpa using h

/-- Free lists with one replaced. -/
def Lset (L : Word → Word → List Word) (f s : Word) (l : List Word) : Word → Word → List Word :=
  fun f' s' => if f' = f ∧ s' = s then l else L f' s'

/-- Memory after `alloc` unlinks the head of list `(f, s)`, whose successor is `nx`: the head
    moves on; the successor's back link is cleared, or, if the list empties, its bit in the
    second-level bitmap and, if that empties, its first-level bit. -/
def popMem (self : Word) (m : Word → Word) (f s nx : Word) : Word → Word :=
  if nx = 0#64 then
    let t := m (slBm self f) &&& ~~~(1#64 <<< s.toNat)
    let m1 := upd (upd m (headAddr self f s) 0#64) (slBm self f) t
    if t = 0#64 then upd m1 (flBm self) (m (flBm self) &&& ~~~(1#64 <<< f.toNat)) else m1
  else upd (upd m (headAddr self f s) nx) (nx + 0x18#64) 0#64

namespace Shape

variable {self base : Word} {m : Word → Word} {bs : List Blk} {L : Word → Word → List Word}
  {out : Word → Prop}

theorem nodeA (h : Shape self base m bs L out) {f s z : Word} (hz : z ∈ L f s) :
    A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40 := by
  obtain ⟨b, hb, rfl, _⟩ := h.node hz
  obtain ⟨h1, h2, h3, _⟩ := h.blk hb
  exact ⟨h1, h2, by omega⟩

theorem blkA (h : Shape self base m bs L out) {b : Blk} (hb : b ∈ bs) :
    A32 b.a ∧ base.toNat ≤ b.a.toNat ∧ b.a.toNat < 2 ^ 40 := by
  obtain ⟨h1, h2, h3, _⟩ := h.blk hb
  exact ⟨h1, h2, by omega⟩

/-- An arena doubleword is not a control-block one. -/
theorem ne_ctl (h : Shape self base m bs L out) {z c k : Word}
    (hz : A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) (hc : c < 32#64) (hk : InCtl self k) :
    z + c ≠ k := h.arena_ne_ctl hz.2.1 hz.2.2 hc hk.2

theorem ne_ctl0 (h : Shape self base m bs L out) {z k : Word}
    (hz : A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) (hk : InCtl self k) : z ≠ k := by
  have := h.ne_ctl hz (c := 0#64) (by decide) hk; simpa using this

/-- Popping a list whose head has a successor `y`. -/
theorem pop_cons (h : Shape self base m bs L out) {f s x y : Word} {ys : List Word}
    (hf : f < 64#64) (hs : s < 64#64) (hL : L f s = x :: y :: ys) :
    Shape self base (upd (upd m (headAddr self f s) y) (y + 0x18#64) 0#64) bs
      (Lset L f s (y :: ys)) (fun a => out a ∨ a = x) := by
  have hc := h.ctlOk
  have hH := headAddr_inCtl hc hf hs
  have hx : x ∈ L f s := by rw [hL]; exact List.mem_cons_self ..
  have hy : y ∈ L f s := by rw [hL]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hnd : (x :: y :: ys).Nodup := hL ▸ h.nodup f s
  have hdll : Dll m 0 (x :: y :: ys) := hL ▸ h.links f s
  have hyA := h.nodeA hy
  -- What the two writes leave alone.
  have keep : ∀ a, a ≠ headAddr self f s → a ≠ y + 0x18#64 →
      upd (upd m (headAddr self f s) y) (y + 0x18#64) 0#64 a = m a := fun a h1 h2 => by
    rw [upd_ne h2, upd_ne h1]
  -- Arena doublewords away from `y`'s back link are kept.
  have keepA : ∀ z c, (A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) → c < 32#64 →
      (z ≠ y ∨ c ≠ 0x18#64) → upd (upd m (headAddr self f s) y) (y + 0x18#64) 0#64 (z + c) =
        m (z + c) := fun z c hz hc hne =>
    keep _ (h.ne_ctl hz hc hH) (key_ne hz.1 hyA.1 hc (by decide) hne)
  have keepC : ∀ k, InCtl self k → k ≠ headAddr self f s →
      upd (upd m (headAddr self f s) y) (y + 0x18#64) 0#64 k = m k := fun k hk hne =>
    keep _ hne (fun e => h.ne_ctl hyA (by decide) hk e.symm)
  have hcl : ∀ {f' s'}, ¬ (f' = f ∧ s' = s) → ∀ z ∈ L f' s', z ≠ y := by
    rintro f' s' hne z hz rfl
    exact hne (h.class_uniq hz hy) |>.elim
  refine ⟨h.chain.congr fun b hb => ⟨?_, keepA _ _ (h.blkA hb) (by decide) (.inr (by decide))⟩,
    h.layout, fun f' s' hf' hs' => ?_, fun f' s' => ?_, fun b hb hu hno => ?_,
    fun f' s' z hz => ?_, fun f' s' hne => ?_, fun f' s' => ?_, fun f' s' hf' hs' => ?_,
    fun f' hf' => ?_⟩
  · have := keepA _ 0#64 (h.blkA hb) (by decide) (.inr (by decide)); simpa using this
  · unfold Lset
    by_cases he : f' = f ∧ s' = s
    · rw [if_pos he, he.1, he.2, upd_ne (fun e => h.ne_ctl hyA (by decide) hH e.symm), upd_same]
      rfl
    · rw [if_neg he, keepC _ (headAddr_inCtl hc hf' hs')
        (fun e => he (headAddr_inj hf' hs' hf hs e)), h.heads f' s' hf' hs']
  · unfold Lset
    by_cases he : f' = f ∧ s' = s
    · rw [if_pos he]
      obtain ⟨_, _, hd⟩ := hdll
      obtain ⟨_, h2, hd⟩ := hd
      refine ⟨upd_same .., ?_, hd.congr fun z hz => ?_⟩
      · rw [keepA _ _ hyA (by decide) (.inr (by decide))]; exact h2
      · have hzy : z ≠ y := fun e => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (e ▸ hz)
        have hzL : z ∈ L f s := by
          rw [hL]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)
        exact ⟨keepA _ _ (h.nodeA hzL) (by decide) (.inl hzy),
          keepA _ _ (h.nodeA hzL) (by decide) (.inl hzy)⟩
    · rw [if_neg he]
      exact (h.links f' s').congr fun z hz =>
        ⟨keepA _ _ (h.nodeA hz) (by decide) (.inl (hcl he z hz)),
          keepA _ _ (h.nodeA hz) (by decide) (.inl (hcl he z hz))⟩
  · have hf0 := h.filed b hb hu (fun ho => hno (.inl ho))
    unfold Lset
    split
    · rename_i he
      rw [he.1, he.2, hL] at hf0
      rcases List.mem_cons.mp hf0 with e | e
      · exact (hno (.inr e)).elim
      · exact e
    · exact hf0
  · unfold Lset at hz
    split at hz
    · rename_i he
      rw [he.1, he.2]
      have hzL : z ∈ L f s := by rw [hL]; exact List.mem_cons_of_mem _ hz
      obtain ⟨ho, hb⟩ := h.members f s z hzL
      refine ⟨fun e => e.elim ho fun e => ?_, hb⟩
      subst e; exact (List.nodup_cons.mp hnd).1 hz
    · rename_i he
      obtain ⟨ho, hb⟩ := h.members f' s' z hz
      refine ⟨fun e => e.elim ho fun e => ?_, hb⟩
      subst e; exact he (h.class_uniq hz hx)
  · unfold Lset at hne
    split at hne
    · rename_i he; rw [he.1, he.2]; exact ⟨hf, hs⟩
    · exact h.range f' s' hne
  · unfold Lset
    split
    · exact (List.nodup_cons.mp hnd).2
    · exact h.nodup f' s'
  · have hSL := slBm_inCtl hc hf'
    rw [keepC _ hSL (fun e => headAddr_ne_slBm hf hs hf' e.symm), h.slbm f' s' hf' hs']
    unfold Lset
    split
    · rename_i he; rw [he.1, he.2, hL]; rfl
    · rfl
  · rw [keepC _ (flBm_inCtl hc) (fun e => headAddr_ne_flBm hf hs e.symm),
      keepC _ (slBm_inCtl hc hf') (fun e => headAddr_ne_slBm hf hs hf' e.symm)]
    exact h.flbm f' hf'

/-- Popping a list's only node: its bitmap bits clear. -/
theorem pop_nil (h : Shape self base m bs L out) {f s x : Word}
    (hf : f < 64#64) (hs : s < 64#64) (hL : L f s = [x]) :
    Shape self base (popMem self m f s 0#64) bs (Lset L f s []) (fun a => out a ∨ a = x) := by
  have hc := h.ctlOk
  have hH := headAddr_inCtl hc hf hs
  have hSL := slBm_inCtl hc hf
  have hFL := flBm_inCtl hc
  have hx : x ∈ L f s := by rw [hL]; exact List.mem_singleton_self _
  have hf6 := lt64 hf
  have hs6 := lt64 hs
  -- The four facts about the new memory.
  generalize ht : m (slBm self f) &&& ~~~(1#64 <<< s.toNat) = t
  have e1 : ∀ a, a ≠ headAddr self f s → a ≠ slBm self f → a ≠ flBm self →
      popMem self m f s 0#64 a = m a := fun a h1 h2 h3 => by
    unfold popMem; simp only [if_true, ht]; split <;> simp [upd, h1, h2, h3]
  have e2 : popMem self m f s 0#64 (headAddr self f s) = 0#64 := by
    unfold popMem; simp only [if_true, ht]
    have := headAddr_ne_slBm (self := self) hf hs hf; have := headAddr_ne_flBm (self := self) hf hs
    split <;> simp [upd, *]
  have e3 : popMem self m f s 0#64 (slBm self f) = t := by
    unfold popMem; simp only [if_true, ht]
    have := slBm_ne_flBm (self := self) hf
    split <;> simp [upd, *]
  have e4 : popMem self m f s 0#64 (flBm self) =
      if t = 0#64 then m (flBm self) &&& ~~~(1#64 <<< f.toNat) else m (flBm self) := by
    unfold popMem; simp only [if_true, ht]
    have := (slBm_ne_flBm (self := self) hf).symm
    have := (headAddr_ne_flBm (self := self) hf hs).symm
    split <;> simp [upd, *]
  generalize popMem self m f s 0#64 = m1 at *
  have keepA : ∀ z c, (A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) → c < 32#64 →
      m1 (z + c) = m (z + c) := fun z c hz hc =>
    e1 _ (h.ne_ctl hz hc hH) (h.ne_ctl hz hc hSL) (h.ne_ctl hz hc hFL)
  -- The old bit of `(f, s)` was set.
  have hbit : (m (slBm self f)).getLsbD s.toNat = true := by
    rw [h.slbm f s hf hs, hL]; rfl
  refine ⟨h.chain.congr fun b hb => ⟨?_, keepA _ _ (h.blkA hb) (by decide)⟩,
    h.layout, fun f' s' hf' hs' => ?_, fun f' s' => ?_, fun b hb hu hno => ?_,
    fun f' s' z hz => ?_, fun f' s' hne => ?_, fun f' s' => ?_, fun f' s' hf' hs' => ?_,
    fun f' hf' => ?_⟩
  · have := keepA _ 0#64 (h.blkA hb) (by decide); simpa using this
  · unfold Lset
    by_cases he : f' = f ∧ s' = s
    · rw [if_pos he, he.1, he.2, e2]; rfl
    · rw [if_neg he, e1 _ (fun e => he (headAddr_inj hf' hs' hf hs e))
        (headAddr_ne_slBm hf' hs' hf) (headAddr_ne_flBm hf' hs'), h.heads f' s' hf' hs']
  · unfold Lset
    split
    · trivial
    · exact (h.links f' s').congr fun z hz =>
        ⟨keepA _ _ (h.nodeA hz) (by decide), keepA _ _ (h.nodeA hz) (by decide)⟩
  · have hf0 := h.filed b hb hu (fun ho => hno (.inl ho))
    unfold Lset
    split
    · rename_i he
      rw [he.1, he.2, hL] at hf0
      exact (hno (.inr (List.mem_singleton.mp hf0))).elim
    · exact hf0
  · unfold Lset at hz
    split at hz
    · simp at hz
    · rename_i he
      obtain ⟨ho, hb⟩ := h.members f' s' z hz
      refine ⟨fun e => e.elim ho fun e => ?_, hb⟩
      subst e; exact he (h.class_uniq hz hx)
  · unfold Lset at hne
    split at hne
    · simp at hne
    · exact h.range f' s' hne
  · unfold Lset
    split
    · exact List.nodup_nil
    · exact h.nodup f' s'
  · have hs'6 := lt64 hs'
    unfold Lset
    by_cases he : f' = f
    · subst he
      rw [e3, ← ht, getLsbD_clr _ hs6]
      by_cases hss : s' = s
      · subst hss; simp
      · have : s'.toNat ≠ s.toNat := fun e => hss (BitVec.eq_of_toNat_eq e)
        rw [if_neg (fun e => hss e.2), h.slbm f' s' hf' hs']; simp [this]
    · rw [if_neg (fun e => he e.1), e1 _ (fun e => headAddr_ne_slBm hf hs hf' e.symm)
        (fun e => he (slBm_inj hf' hf e)) (slBm_ne_flBm hf'), h.slbm f' s' hf' hs']
  · have hf'6 := lt64 hf'
    rw [e4]
    by_cases he : f' = f
    · subst he
      rw [e3]
      by_cases ht0 : t = 0#64
      · rw [if_pos ht0, getLsbD_clr _ hf6, ht0]; simp
      · rw [if_neg ht0, h.flbm f' hf']
        have : m (slBm self f') ≠ 0#64 := fun e => by rw [e] at hbit; simp at hbit
        simp only [Bool.not_eq_eq_eq_not, Bool.not_not]
        rw [beq_false_of_ne (b := 0) this, beq_false_of_ne (b := 0) ht0]
    · have hne : f'.toNat ≠ f.toNat := fun e => he (BitVec.eq_of_toNat_eq e)
      rw [e1 _ (fun e => headAddr_ne_slBm hf hs hf' e.symm)
        (fun e => he (slBm_inj hf' hf e)) (slBm_ne_flBm hf')]
      split
      · rw [getLsbD_clr _ hf6, h.flbm f' hf']; simp [hne]
      · exact h.flbm f' hf'

/-- **Popping the head of a free list** detaches it. -/
theorem pop (h : Shape self base m bs L out) {f s x : Word} {xs : List Word}
    (hf : f < 64#64) (hs : s < 64#64) (hL : L f s = x :: xs) :
    Shape self base (popMem self m f s (xs.headD 0#64)) bs (Lset L f s xs)
      (fun a => out a ∨ a = x) := by
  cases xs with
  | nil => exact h.pop_nil hf hs hL
  | cons y ys =>
    have hy : y ∈ L f s := by rw [hL]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have := h.pop_cons hf hs hL
    change Shape self base (popMem self m f s y) bs _ _
    unfold popMem
    rw [if_neg (h.node_ne_zero hy)]
    exact this

end Shape

end Cases.Zip2005.Runtime.Tlsf
