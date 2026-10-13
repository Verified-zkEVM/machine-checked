/-
  Cases.Zip2005.HeapEnv

  The heap-owning `Env` (phase E).

  `Owned.env` owns the hasher's tag and position. This `Env` also owns the allocator: rlsf's
  control block `[0x78040620, 0x78048830)` and the arena `[0x78048980, 2^40)` (the arena is
  `[_end, 7 << 34)`; the region is widened to the `2^40` bound `Tlsf.Shape.layout` gives
  every block, so every key `Rep` reads is owned). Its invariant adds `HeapOk`: the heap is
  well formed (`Tlsf.Rep`, for some block list and free lists).

  Owning the heap is what lets the checker compose functions that allocate: no footprint may
  name the heap, every interface's precondition asks for `HeapOk` and its postcondition gives
  it back, and the allocator's own doublewords -- which no footprint could describe -- are
  the owned memory that only the allocator's interfaces change.

  Everything proved so far lifts: the checked table from the plain `Env`
  (`Iface.HoldsN.lift`), and the hand proofs against `Owned.env` by `toHeap` (a function
  entered under this `Env`'s precondition writes no heap key, so `Rep` survives it).
-/

import Cases.Zip2005.Owned
import Cases.Zip2005.Runtime.Realloc

namespace Cases.Zip2005.HeapEnv

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check Cases.Zip2005
  Cases.Zip2005.Runtime

/-- `INNER_HEAP`, the control block's address. -/
def HEAP : Word := Runtime.Realloc.HEAP

/-- The arena's first block: `_end`. -/
def BASE : Word := 0x78048980#64

/-- The control block, as an owned region. -/
def ctl : Word × Nat := (0x78040620#64, Tlsf.ctlSize)

/-- The arena, as an owned region, up to every block's bound. -/
def arena : Word × Nat := (0x78048980#64, 2 ^ 40 - 0x78048980)

/-- The heap is well formed. -/
def HeapOk (m : Word → Word) : Prop := ∃ bs L, Tlsf.Rep HEAP BASE m bs L

noncomputable def env : Env :=
  { Owned.env with
    own := [(Owned.tagKey, 8), (Owned.posKey, 8), ctl, arena]
    inv := fun m => Owned.HasherOk m ∧ HeapOk m }

theorem env_wf : env.wf = true := by decide +kernel

theorem env_inv (m : Word → Word) : env.inv m = (Owned.HasherOk m ∧ HeapOk m) := rfl

theorem env_plain : env.plain = Contract.env := rfl

theorem env_cfi : env.cfi = Owned.env.cfi := rfl

theorem env_stackTop : env.stackTop = Owned.env.stackTop := rfl

theorem env_prot : env.prot = Owned.env.prot := rfl

theorem env_init : env.init = Owned.env.init := rfl

theorem tag_own : env.InOwn Owned.tagKey := ⟨(Owned.tagKey, 8), by simp [env], Or.inl (by decide)⟩
theorem pos_own : env.InOwn Owned.posKey := ⟨(Owned.posKey, 8), by simp [env], Or.inl (by decide)⟩

/-- A doubleword of the control block is owned. -/
theorem ctl_own {a : Word} (h1 : HEAP.toNat ≤ a.toNat) (h2 : a.toNat < HEAP.toNat + Tlsf.ctlSize) :
    env.InOwn a := by
  refine ⟨ctl, by simp [env], Or.inl ?_⟩
  have hH : HEAP.toNat = 0x78040620 := rfl
  have hle : 0x78040620#64 ≤ a := by rw [BitVec.le_def]; simpa [hH] using h1
  simp only [ctl, Tlsf.ctlSize] at *
  rw [BitVec.toNat_sub_of_le hle]
  simp; omega

/-- A doubleword of the arena is owned. -/
theorem arena_own {a : Word} (h1 : BASE.toNat ≤ a.toNat) (h2 : a.toNat < 2 ^ 40) : env.InOwn a := by
  refine ⟨arena, by simp [env], Or.inl ?_⟩
  have hB : BASE.toNat = 0x78048980 := rfl
  have hle : 0x78048980#64 ≤ a := by rw [BitVec.le_def]; simpa [hB] using h1
  simp only [arena]
  rw [BitVec.toNat_sub_of_le hle]
  simp; omega

/-- Every key the heap's shape reads lies in the control block or the arena. -/
theorem key_range {m : Word → Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {out : Word → Prop} (h : Tlsf.Shape HEAP BASE m bs L out) {a : Word}
    (hk : Tlsf.Key HEAP bs a) :
    (HEAP.toNat ≤ a.toNat ∧ a.toNat < HEAP.toNat + Tlsf.ctlSize) ∨
    (BASE.toNat ≤ a.toNat ∧ a.toNat < 2 ^ 40) := by
  rcases hk with hk | ⟨b, hb, hk⟩
  · exact Or.inl ⟨by have := hk.1; omega, hk.2⟩
  · have hA := h.blkA hb
    have hbnd := (h.blk hb).2.2.1
    have hsz := Tlsf.Shape.sz_ge (h.blk hb).2.2.2.2
    have h8 : ∀ c : Word, c.toNat < 32 → (b.a + c).toNat = b.a.toNat + c.toNat := fun c hc => by
      rw [BitVec.toNat_add]; omega
    have e8 : (b.a + 8#64).toNat = b.a.toNat + 8 := by rw [h8 _ (by decide)]; rfl
    have e16 : (b.a + 0x10#64).toNat = b.a.toNat + 16 := by rw [h8 _ (by decide)]; rfl
    have e24 : (b.a + 0x18#64).toNat = b.a.toNat + 24 := by rw [h8 _ (by decide)]; rfl
    have hB : BASE.toNat = 0x78048980 := rfl
    right
    rcases hk with rfl | rfl | ⟨_, rfl | rfl⟩ <;> omega

/-- Every key the heap's shape reads is owned. -/
theorem key_own {m : Word → Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {out : Word → Prop} (h : Tlsf.Shape HEAP BASE m bs L out) {a : Word}
    (hk : Tlsf.Key HEAP bs a) : env.InOwn a := by
  rcases key_range h hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ctl_own h1 h2
  · exact arena_own h1 h2

theorem heap_aligned : Aligned HEAP := by unfold Aligned HEAP Runtime.Realloc.HEAP; decide

theorem heap_own : env.InOwn HEAP := ctl_own (Nat.le_refl _) (by simp [Tlsf.ctlSize])

/-- An aligned doubleword hits an aligned one only when they coincide. -/
theorem hits8_aligned {a b : Word} (ha : Aligned a) (hb : Aligned b) (h : Hits b 8 a) : a = b := by
  unfold Hits Aligned at *
  have key : ∀ x y : BitVec 64, x &&& 7#64 = 0#64 → y &&& 7#64 = 0#64 → x - y < 8#64 → x = y := by
    intro x y; bv_decide
  rcases h with h | ⟨_, h⟩
  · exact key a b ha hb (by rw [BitVec.lt_def]; simpa using h)
  · exact (key b a hb ha (by rw [BitVec.lt_def]; simpa using h)).symm

/-- No aligned heap key is one of the hasher's owned doublewords. -/
theorem key_not_hasher {a : Word} (ha : Aligned a)
    (hr : a.toNat < HEAP.toNat + Tlsf.ctlSize ∨ BASE.toNat ≤ a.toNat) : ¬ Owned.env.InOwn a := by
  rintro ⟨R, hR, hh⟩
  simp only [Owned.env, List.mem_cons, List.mem_nil_iff, or_false] at hR
  have hH : HEAP.toNat = 0x78040620 := rfl
  have hB : BASE.toNat = 0x78048980 := rfl
  simp only [Tlsf.ctlSize] at hr
  rcases hR with rfl | rfl
  · have := hits8_aligned ha (by unfold Aligned Owned.tagKey; decide) hh
    subst this; simp only [Owned.tagKey, BitVec.toNat_ofNat] at hr; omega
  · have := hits8_aligned ha (by unfold Aligned Owned.posKey; decide) hh
    subst this; simp only [Owned.posKey, BitVec.toNat_ofNat] at hr; omega

/-- `ownPart` is transparent to the heap's shape: its keys are owned, and aligned ones are
    all it reads. -/
theorem heapOk_ownPart {m : Word → Word} : HeapOk (env.ownPart m) ↔ HeapOk m := by
  have hown : ∀ a, Aligned a → env.InOwn a → env.ownPart m a = m a := fun a ha ho => by
    simp only [Env.ownPart]; rw [if_pos ⟨ha, ho⟩]
  constructor
  · rintro ⟨bs, L, h⟩
    obtain ⟨hl, hs⟩ := Tlsf.rep_iff.mp h
    refine ⟨bs, L, Tlsf.rep_iff.mpr ⟨?_, Runtime.Realloc.congrA hs heap_aligned fun a hk hal =>
      (hown a hal (key_own hs hk)).symm⟩⟩
    rw [← hl, hown _ heap_aligned heap_own]
  · rintro ⟨bs, L, h⟩
    obtain ⟨hl, hs⟩ := Tlsf.rep_iff.mp h
    refine ⟨bs, L, Tlsf.rep_iff.mpr ⟨?_, Runtime.Realloc.congrA hs heap_aligned fun a hk hal =>
      hown a hal (key_own hs hk)⟩⟩
    rw [hown _ heap_aligned heap_own]; exact hl

/-- The invariant of a memory, through the owned keys. -/
theorem inv_iff {m : Word → Word} : env.Inv m ↔ Owned.HasherOk m ∧ HeapOk m := by
  have ht : env.ownPart m Owned.tagKey = m Owned.tagKey := by
    simp only [Env.ownPart]; rw [if_pos ⟨by unfold Aligned; decide, tag_own⟩]
  have hp : env.ownPart m Owned.posKey = m Owned.posKey := by
    simp only [Env.ownPart]; rw [if_pos ⟨by unfold Aligned; decide, pos_own⟩]
  unfold Env.Inv
  rw [env_inv, heapOk_ownPart]
  simp only [Owned.HasherOk, ht, hp]

/-! ## Lifting -/

/-- **The checked table, with the heap owned.** -/
theorem tbl_holds : ∀ g ∈ Contract.tbl, g.Holds env Image.Layout.image.codeAt :=
  fun g hg n => Iface.HoldsN.lift_trivial env_wf rfl (by rw [env_plain]; exact Contract.all g hg n)

/-- An owned key of `Owned.env` is one of this `Env`. -/
theorem inOwn_of_owned {a : Word} (h : Owned.env.InOwn a) : env.InOwn a := by
  obtain ⟨R, hR, hh⟩ := h
  simp only [Owned.env, List.mem_cons, List.mem_nil_iff, or_false] at hR
  exact ⟨R, by simp only [env, List.mem_cons]; rcases hR with rfl | rfl <;> simp, hh⟩

/-- A precondition for this `Env` is one for `Owned.env`. -/
theorem Pre.toOwned {C : Word → Option Instr} {σ : Iface} {s : MachineState}
    (hpre : Pre env C σ s) : Pre Owned.env C σ s :=
  ⟨hpre.1, hpre.2.1, hpre.2.2.1, hpre.2.2.2.1, hpre.2.2.2.2.1,
    fun it hit a ha hh => ⟨(hpre.2.2.2.2.2.1 it hit a ha hh).1,
      (hpre.2.2.2.2.2.1 it hit a ha hh).2.1, fun ho => (hpre.2.2.2.2.2.1 it hit a ha hh).2.2 (inOwn_of_owned ho)⟩,
    hpre.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.1,
    fun c hc => let h := hpre.2.2.2.2.2.2.2.2.1 c hc; ⟨h.1, h.2.1, fun ho => h.2.2.1 (inOwn_of_owned ho), h.2.2.2⟩,
    (Owned.inv_iff).mpr (inv_iff.mp hpre.2.2.2.2.2.2.2.2.2.1).1,
    fun e he => let h := hpre.2.2.2.2.2.2.2.2.2.2.1 e he;
      ⟨h.1, h.2.1, fun a hs => ⟨(h.2.2 a hs).1, fun ho => (h.2.2 a hs).2 (inOwn_of_owned ho)⟩⟩,
    hpre.2.2.2.2.2.2.2.2.2.2.2⟩

/-- A return under `Owned.env` is one under this `Env`: the function wrote no heap key (its
    window and footprint avoid every owned key), so the heap is as it was. -/
theorem Post.toHeap {C : Word → Option Instr} {σ : Iface} {s t : MachineState}
    (hpre : Pre env C σ s) (h : Post Owned.env σ s t) : Post env σ s t := by
  refine ⟨h.1, h.2.1, h.2.2.1,
    fun a ha hnw ho hns => h.2.2.2.1 a ha hnw (fun ho' => ho (inOwn_of_owned ho')) hns,
    h.2.2.2.2.1, inv_iff.mpr ⟨(Owned.inv_iff).mp h.2.2.2.2.2.1, ?_⟩, h.2.2.2.2.2.2⟩
  obtain ⟨bs, L, hrep⟩ := (inv_iff.mp hpre.2.2.2.2.2.2.2.2.2.1).2
  obtain ⟨hl, hs⟩ := Tlsf.rep_iff.mp hrep
  have hkeep : ∀ a, Aligned a → env.InOwn a → ¬ Owned.env.InOwn a → t.getMem a = s.getMem a :=
    fun a ha ho hno => h.2.2.2.1 a ha (Pre.not_written_own env_wf hpre ha ho) hno
      (StrHit.trivial rfl)
  refine ⟨bs, L, Tlsf.rep_iff.mpr ⟨?_, Runtime.Realloc.congrA hs heap_aligned fun a hk hal => ?_⟩⟩
  · rw [hkeep _ heap_aligned heap_own (key_not_hasher heap_aligned (Or.inl (by simp [Tlsf.ctlSize])))]
    exact hl
  · refine hkeep a hal (key_own hs hk) (key_not_hasher hal ?_)
    rcases key_range hs hk with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Or.inl h2
    · exact Or.inr h1

/-- **Lifting.** An interface proved against `Owned.env` holds with the heap owned too. -/
theorem Iface.HoldsN.toHeap {C : Word → Option Instr} {σ : Iface} {n : Nat}
    (h : σ.HoldsN Owned.env C n) : σ.HoldsN env C n :=
  fun G hG P s hpc hpre hk =>
    h G (fun x hx => by simpa [Env.Cfi, env] using hG x hx) P s hpc (Pre.toOwned hpre)
      (fun t ht => hk t (Post.toHeap hpre ht))

end Cases.Zip2005.HeapEnv
