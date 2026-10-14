/-
  Cases.Zip2005.Runtime.Realloc

  `__rust_realloc` (`0x7801bd38`), end to end (phase D4).

  The shim `alloc`s the new size; on null it returns null. Otherwise it copies the smaller of
  the two sizes with `memcpy`, and, the old pointer being in the heap, `dealloc`s the old
  block, then returns the new pointer. Each call is a proved specification: `Alloc.spec`,
  `Memcpy.holds` (the `Iface` contract, with the owned statics' invariant), `Dealloc.spec`.
  Between them, `RS` keeps the frame (the saved registers and `s0`–`s2`), and the heap is
  carried across the copy by the aligned-store frame `congrA`: the copy writes only the new
  block past its header, which no key of the heap reaches.

  `spec`: from `Rep`, the de Bruijn table, and a pointer `alloc` granted for a used block `b`,
  `realloc` returns with the callee-saved registers, code, owned invariant and protected
  memory kept, `Rep` re-established, memory below the heap (off the stack window and the owned
  statics) and every other live byte unchanged, and either null with every used block kept,
  or a new block granted for the new size and alignment with `b` freed (`Done`).
-/

import Cases.Zip2005.Runtime.Dealloc.Spec
import Cases.Zip2005.Runtime.Memcpy

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Realloc

open RiscvZkvm.Rv64
open AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check AsmVerif.RiscV.Exec
  Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7801bd38.base, prog := F_7801bd38.prog }

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 29) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn] at h)

/-- The heap: `INNER_HEAP`, at the start of `.bss`. -/
def HEAP : Word := 0x78040620#64

/-- A byte of a used block past its header: memory the program owns. -/
def Live (bs : List Tlsf.Blk) (a : Word) : Prop :=
  ∃ c ∈ bs, c.used = true ∧ c.a.toNat + 16 ≤ a.toNat ∧ a.toNat < c.a.toNat + c.sz.toNat

/-- Every key of the shape lies past the lock. -/
theorem key_gt {self base : Word} {m : Word → Word} {bs : List Tlsf.Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Tlsf.Shape self base m bs L out)
    {a : Word} (ha : Tlsf.Key self bs a) : self.toNat < a.toNat := by
  have hl := h.layout.1
  simp only [Tlsf.ctlSize] at hl
  rcases ha with ha | ⟨b, hb, ha⟩
  · have := ha.1; omega
  · have hA := h.blkA hb
    have h8 : ∀ c : Word, c.toNat < 32 → (b.a + c).toNat = b.a.toNat + c.toNat := fun c hc => by
      rw [BitVec.toNat_add]; omega
    rcases ha with ha | ha | ⟨_, ha | ha⟩
    · rw [ha]; omega
    · have := h8 8#64 (by decide); rw [← ha] at this; simp at this; omega
    · have := h8 0x10#64 (by decide); rw [← ha] at this; simp at this; omega
    · have := h8 0x18#64 (by decide); rw [← ha] at this; simp at this; omega

/-- The heap is what memory holds at and past its lock. -/
theorem rep_congr {self base : Word} {m m' : Word → Word} {bs : List Tlsf.Blk}
    {L : Word → Word → List Word} (h : Tlsf.Rep self base m bs L)
    (hm : ∀ a, self.toNat ≤ a.toNat → m' a = m a) : Tlsf.Rep self base m' bs L := by
  obtain ⟨hl, hs⟩ := Tlsf.rep_iff.mp h
  exact Tlsf.rep_iff.mpr ⟨by rw [hm _ (Nat.le_refl _)]; exact hl,
    hs.congr fun a ha => hm a (Nat.le_of_lt (key_gt hs ha))⟩

/-- The de Bruijn table is what memory holds in `.rodata`. -/
theorem ro_congr {m m' : Word → Word} (h : Alloc.RoOk m)
    (hm : ∀ a, 0x78000000 ≤ a.toNat → a.toNat < 0x78002000 → m' a = m a) : Alloc.RoOk m' := by
  refine ⟨by rw [hm _ (by decide) (by decide)]; exact h.1, fun j hj => ?_⟩
  have : ∀ j : BitVec 64, j < 8#64 → 0x78001540#64 + j <<< 3 < 0x78002000#64 ∧
      0x78000000#64 ≤ 0x78001540#64 + j <<< 3 := by intro j h; bv_decide
  obtain ⟨h1, h2⟩ := this j hj
  rw [BitVec.lt_def] at h1; rw [BitVec.le_def] at h2
  rw [hm _ (by simpa using h2) (by simpa using h1)]; exact h.2 j hj

theorem al_add {x c : Word} (hx : Aligned x) (hc : c &&& 7#64 = 0#64) : Aligned (x + c) := by
  unfold Aligned at *
  have : ∀ x c : BitVec 64, x &&& 7#64 = 0#64 → c &&& 7#64 = 0#64 → (x + c) &&& 7#64 = 0#64 := by
    intro x c; bv_decide
  exact this x c hx hc

theorem al_a32 {x : Word} (h : Tlsf.A32 x) : Aligned x := by
  unfold Aligned Tlsf.A32 at *
  have : ∀ x : BitVec 64, x &&& 31#64 = 0#64 → x &&& 7#64 = 0#64 := by intro x; bv_decide
  exact this x h

/-- **Frame, for aligned stores.** The shape reads only aligned doublewords (with an aligned
    control block), so it survives any change to the others. -/
theorem congrA {self base : Word} {m m' : Word → Word} {bs : List Tlsf.Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Tlsf.Shape self base m bs L out)
    (hself : Aligned self) (hm : ∀ a, Tlsf.Key self bs a → Aligned a → m' a = m a) :
    Tlsf.Shape self base m' bs L out := by
  have hc := h.ctlOk
  have aH : ∀ f s : Word, Aligned (Tlsf.headAddr self f s) := fun f s => by
    unfold Tlsf.headAddr Aligned at *
    have : ∀ x f s : BitVec 64, x &&& 7#64 = 0#64 →
        (x + 8#64 + f * 0x200#64 + s * 8#64) &&& 7#64 = 0#64 := by intro x f s; bv_decide
    exact this _ f s hself
  have aS : ∀ f : Word, Aligned (Tlsf.slBm self f) := fun f => by
    unfold Tlsf.slBm Aligned at *
    have : ∀ x f : BitVec 64, x &&& 7#64 = 0#64 → (x + 0x8008#64 + f * 8#64) &&& 7#64 = 0#64 := by
      intro x f; bv_decide
    exact this _ f hself
  have aF : Aligned (Tlsf.flBm self) := al_add hself (by decide)
  have aB : ∀ b ∈ bs, ∀ c : Word, c &&& 7#64 = 0#64 → Aligned (b.a + c) := fun b hb c hc' =>
    al_add (al_a32 (h.blkA hb).1) hc'
  refine ⟨h.chain.congr fun b hb => ⟨hm _ (.inr ⟨b, hb, .inl rfl⟩) (al_a32 (h.blkA hb).1),
      hm _ (.inr ⟨b, hb, .inr (.inl rfl)⟩) (aB b hb _ (by decide))⟩, h.layout,
    fun f s hf hs => (hm _ (.inl (Tlsf.headAddr_inCtl hc hf hs)) (aH f s)).trans (h.heads f s hf hs),
    fun f s => (h.links f s).congr fun x hx => ?_, h.filed, h.members, h.range, h.nodup,
    fun f s hf hs => by rw [hm _ (.inl (Tlsf.slBm_inCtl hc hf)) (aS f)]; exact h.slbm f s hf hs,
    fun f hf => by
      rw [hm _ (.inl (Tlsf.flBm_inCtl hc)) aF, hm _ (.inl (Tlsf.slBm_inCtl hc hf)) (aS f)]
      exact h.flbm f hf⟩
  obtain ⟨_, b, hb, rfl, hu, _⟩ := h.members f s x hx
  exact ⟨hm _ (.inr ⟨b, hb, .inr (.inr ⟨hu, .inl rfl⟩)⟩) (aB b hb _ (by decide)),
    hm _ (.inr ⟨b, hb, .inr (.inr ⟨hu, .inr rfl⟩)⟩) (aB b hb _ (by decide))⟩

theorem rep_congrA {self base : Word} {m m' : Word → Word} {bs : List Tlsf.Blk}
    {L : Word → Word → List Word} (h : Tlsf.Rep self base m bs L) (hself : Aligned self)
    (hm : ∀ a, Aligned a → self.toNat ≤ a.toNat → m' a = m a) : Tlsf.Rep self base m' bs L := by
  obtain ⟨hl, hs⟩ := Tlsf.rep_iff.mp h
  exact Tlsf.rep_iff.mpr ⟨by rw [hm _ hself (Nat.le_refl _)]; exact hl,
    congrA hs hself fun a ha hal => hm a hal (Nat.le_of_lt (key_gt hs ha))⟩

/-- A live byte is none of the allocator's own. -/
theorem notMine_live {self base : Word} {m : Word → Word} {bs : List Tlsf.Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Tlsf.Shape self base m bs L out)
    {a : Word} (ha : Live bs a) : ¬ Alloc.Mine self bs a := by
  obtain ⟨c, hc, hcu, h1, h2⟩ := ha
  have hl := h.layout.1
  simp only [Tlsf.ctlSize] at hl
  have hcA := h.blkA hc
  rintro (hm | ⟨d, hd, hm | ⟨hdu, hm1, hm2⟩⟩)
  · simp only [Tlsf.ctlSize] at hm; omega
  · have hdA := h.blkA hd
    have : (d.a + 8#64).toNat = d.a.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    subst hm
    by_cases hcd : c = d
    · subst hcd; omega
    · have := Tlsf.Shape.sz_ge (h.blk hd).2.2.2.2
      rcases h.disj hc hd hcd with h3 | h3 <;> omega
  · by_cases hcd : c = d
    · subst hcd; rw [hcu] at hdu; exact absurd hdu (by simp)
    · rcases h.disj hc hd hcd with h3 | h3 <;> omega

/-- Below the heap is none of the allocator's own. -/
theorem notMine_low {self base : Word} {m : Word → Word} {bs : List Tlsf.Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Tlsf.Shape self base m bs L out)
    {a : Word} (ha : a.toNat < self.toNat) : ¬ Alloc.Mine self bs a := by
  have hl := h.layout.1
  simp only [Tlsf.ctlSize] at hl
  rintro (hm | ⟨d, hd, hm | ⟨-, hm1, -⟩⟩)
  · simp only [Tlsf.ctlSize] at hm; omega
  · have hdA := h.blkA hd
    have : (d.a + 8#64).toNat = d.a.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    subst hm; omega
  · have hdA := h.blkA hd; omega

/-- The callee-saved registers `realloc` neither saves nor uses. -/
def untouched : List Reg := [.x3, .x4, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- Inside `realloc`, after its prologue: the frame holds the saved registers and `s0`, `s1`,
    `s2` the old size, the alignment and the pointer. -/
structure RS (s0 y : MachineState) : Prop where
  code : y.code = C
  sp : y.getReg .x2 = s0.getReg .x2 + 0xffffffffffffffd0#64
  old : y.getReg .x8 = s0.getReg .x11
  align : y.getReg .x9 = s0.getReg .x12
  ptr : y.getReg .x18 = s0.getReg .x10
  regs : ∀ r ∈ untouched, y.getReg r = s0.getReg r
  fra : y.getMem (s0.getReg .x2 + 0xfffffffffffffff8#64) = s0.getReg .x1
  fs0 : y.getMem (s0.getReg .x2 + 0xfffffffffffffff0#64) = s0.getReg .x8
  fs1 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe8#64) = s0.getReg .x9
  fs2 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe0#64) = s0.getReg .x18
  fs3 : y.getMem (s0.getReg .x2 + 0xffffffffffffffd8#64) = s0.getReg .x19
  fs4 : y.getMem (s0.getReg .x2 + 0xffffffffffffffd0#64) = s0.getReg .x20

namespace RS

variable {s0 y : MachineState}

theorem setPC (h : RS s0 y) (v : Word) : RS s0 (y.setPC v) :=
  ⟨by simp [h.code], by simp [h.sp], by simp [h.old], by simp [h.align], by simp [h.ptr],
    fun r hr => by simp [h.regs r hr], by simp [h.fra], by simp [h.fs0], by simp [h.fs1],
    by simp [h.fs2], by simp [h.fs3], by simp [h.fs4]⟩

theorem setReg (h : RS s0 y) {r : Reg} (hr : r ∉ untouched) (h2 : r ≠ .x2) (h8 : r ≠ .x8)
    (h9 : r ≠ .x9) (h18 : r ≠ .x18) (v : Word) : RS s0 (y.setReg r v) := by
  refine ⟨by simp [h.code], ?_, ?_, ?_, ?_, fun r' hr' => ?_, by simp [h.fra], by simp [h.fs0],
    by simp [h.fs1], by simp [h.fs2], by simp [h.fs3], by simp [h.fs4]⟩
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h2]; exact h.sp
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h8]; exact h.old
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h9]; exact h.align
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h18]; exact h.ptr
  · have : r ≠ r' := fun e => hr (e ▸ hr')
    rw [MachineState.getReg_setReg_ne _ _ _ _ this]; exact h.regs r' hr'

end RS

/-- `RS` through register writes and `pc` updates. -/
macro "rst" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine RS.setPC ?_ _ |
    with_reducible refine RS.setReg ?_ (by decide) (by decide) (by decide) (by decide) (by decide) _))

/-- The epilogue at `0x7801bdc8`: return `s3`. -/
theorem exit {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    (hs : RS s0 y) (hpc : y.pc = 0x7801bdc8#64)
    (hk : ∀ t, t.pc = s0.getReg .x1 &&& ~~~1#64 → (∀ q ∈ savedRegs, t.getReg q = s0.getReg q) →
      t.code = y.code → t.getMem = y.getMem → t.getReg .x10 = y.getReg .x19 → SafeN G n P t) :
    SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  iterate 9 xstep code
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, hs.sp]
  xa
  simp only [hs.fra, hs.fs0, hs.fs1, hs.fs2, hs.fs3, hs.fs4]
  refine hk _ (by simp) (fun q hq => ?_) (by simp) (by funext a; simp) (by xregs)
  simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> xregs <;> first | rfl | (rw [hs.sp]; bv_omega) |
      (refine hs.regs _ ?_; simp [untouched])

/-- The last of the frame slots, as numbers. -/
theorem slot_lt {sp a c : Word} (hsp : 0x60 ≤ sp.toNat) (hc : 2 ^ 64 - 0x30 ≤ c.toNat)
    (ha : sp.toNat ≤ a.toNat ∨ a.toNat + 0x30 ≤ sp.toNat - 0x30) : sp + c ≠ a := by
  intro e
  have h1 := congrArg BitVec.toNat e
  have h2 := c.isLt
  rw [BitVec.toNat_add] at h1
  omega

/-- After the copy, at `0x7801bda0`: free the old block (it is in the heap), and return. -/
theorem afterCopy {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {base : Word} {bs1 : List Tlsf.Blk} {L1 : Word → Word → List Word} {b : Tlsf.Blk}
    (hs : RS s0 y) (hpc : y.pc = 0x7801bda0#64)
    (hrep : Tlsf.Rep HEAP base y.getMem bs1 L1) (hbin : b ∈ bs1) (hbu : b.used = true)
    (hbl : b.last = false)
    (hsmall : s0.getReg .x12 ≤ 31#64 → s0.getReg .x10 = b.a + 16#64)
    (hbig : ¬ s0.getReg .x12 ≤ 31#64 →
      y.getMem (s0.getReg .x10 + 0xfffffffffffffff8#64) = b.a ∧
      b.a.toNat ≤ (s0.getReg .x10 + 0xfffffffffffffff8#64).toNat ∧
      (s0.getReg .x10 + 0xfffffffffffffff8#64).toNat < b.a.toNat + b.sz.toNat)
    (hptr : ¬ 6#64 < s0.getReg .x10 >>> 34)
    (hsp : 0x60 ≤ (s0.getReg .x2).toNat) (hstk : (s0.getReg .x2).toNat ≤ 0x78000000)
    (hk : ∀ t, t.pc = s0.getReg .x1 &&& ~~~1#64 → (∀ q ∈ savedRegs, t.getReg q = s0.getReg q) →
      t.code = C → t.getReg .x10 = y.getReg .x19 →
      (∃ bs' L', Tlsf.Rep HEAP base t.getMem bs' L' ∧
        (∀ c ∈ bs1, c.used = true → c ≠ b → c ∈ bs') ∧
        ∀ a, ¬ Alloc.Mine HEAP bs1 a → ¬ (b.a.toNat ≤ a.toNat ∧ a.toNat < b.a.toNat + b.sz.toNat) →
          ¬ Dealloc.InFrame (s0.getReg .x2 + 0xffffffffffffffd0#64) a → t.getMem a = y.getMem a) →
      SafeN G n P t) :
    SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  iterate 2 xstep code
  xstep code
  · exfalso; apply hptr; rw [hs.ptr] at hb; simpa [BitVec.ult_iff_lt] using hb
  iterate 7 xstep code
  xag
  refine Dealloc.spec (bs := bs1) (L := L1) (b := b) (base := base) rfl (by simp [hcode])
    (by xregs; exact (congrArg (fun m => Tlsf.Rep HEAP base m bs1 L1) (funext fun a => by simp)).mpr hrep)
    hbin hbu hbl (by xregs; rw [hs.align, hs.ptr]; exact hsmall)
    (by
      xregs
      rw [hs.align, hs.ptr]
      simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
      exact hbig)
    (by xregs; rw [hs.sp, BitVec.toNat_add]; simp; omega)
    (by xregs; rw [hs.sp, BitVec.toNat_add]; simp; omega) ?_
  intro t hd
  obtain ⟨M', hout, bs', L', hrep', hused, hfr⟩ := hd
  have om := hout.mem
  have op := hout.pc
  have osv := hout.saved
  have oc := hout.code
  clear hout
  simp only [getReg_setReg, MachineState.getReg_setPC, reduceCtorEq, ne_eq, not_false_eq_true,
    and_true, if_true, if_false, MachineState.getMem_setReg, MachineState.getMem_setPC]
    at om op osv oc hrep' hfr
  rw [show (2013529632#64 : Word) = HEAP from rfl] at hrep' hfr
  rw [hs.sp] at om
  have oc' : t.code = C := by rw [oc]; simp [hs.code]
  have osv' : ∀ q ∈ savedRegs, q ≠ .x1 → q ≠ .x10 → q ≠ .x11 → q ≠ .x12 → q ≠ .x13 →
      t.getReg q = y.getReg q := fun q hq h1 h2 h3 h4 h5 => by
    rw [osv q hq]; simp [h1, h2, h3, h4, h5]
  -- Back in `realloc`, at `0x7801bdc8`.
  have hsp3 : (s0.getReg .x2 + 0xffffffffffffffd0#64).toNat = (s0.getReg .x2).toNat - 0x30 := by
    rw [BitVec.toNat_add]; simp; omega
  have offD : ∀ a, (s0.getReg .x2).toNat - 0x30 ≤ a.toNat →
      ¬ Dealloc.InFrame (s0.getReg .x2 + 0xffffffffffffffd0#64) a := fun a ha h => by
    unfold Dealloc.InFrame at h; omega
  have hsh1 := (Tlsf.rep_iff.mp hrep).2
  -- The frame slots survive the call.
  have hslot : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat →
      t.getMem (s0.getReg .x2 + c) = y.getMem (s0.getReg .x2 + c) := by
    intro c hc
    have h1 : (s0.getReg .x2 + c).toNat + 0x30 ≥ (s0.getReg .x2).toNat ∧
        (s0.getReg .x2 + c).toNat < (s0.getReg .x2).toNat := by
      have := c.isLt; rw [BitVec.toNat_add]; omega
    have hH : HEAP.toNat = 2013529632 := rfl
    have hbA := (hsh1.blkA hbin).2.1
    have hlay := hsh1.layout.1
    simp only [Tlsf.ctlSize] at hlay
    rw [om _ (offD _ (by omega)), hfr _ (notMine_low hsh1 (by omega)) (fun h => by omega)]
  have ht : RS s0 t := by
    refine ⟨oc', ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [osv' .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.sp
    · rw [osv' .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.old
    · rw [osv' .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.align
    · rw [osv' .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hs.ptr
    · simp only [untouched, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [osv' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
         exact hs.regs _ (by simp [untouched]))
    · rw [hslot _ (by decide)]; exact hs.fra
    · rw [hslot _ (by decide)]; exact hs.fs0
    · rw [hslot _ (by decide)]; exact hs.fs1
    · rw [hslot _ (by decide)]; exact hs.fs2
    · rw [hslot _ (by decide)]; exact hs.fs3
    · rw [hslot _ (by decide)]; exact hs.fs4
  refine exit ht (by rw [op]; simp) fun t' hpc' hsav' hcode' hmem' hres' => ?_
  refine hk t' hpc' hsav' (by rw [hcode', ht.code])
    (by rw [hres', osv' .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    ⟨bs', L', rep_congr hrep' fun a ha => by
      rw [hmem', om _ (offD _ (by have : HEAP.toNat = 2013529632 := rfl; omega))], hused,
      fun a ha hb' hfa => ?_⟩
  rw [hmem', om _ hfa, hfr a ha hb']

/-- Where a block's keys sit: its header, and for a free block its links. -/
theorem key_blk {d : Tlsf.Blk} (hd : d.a.toNat < 2 ^ 40) {a : Word}
    (ha : a = d.a ∨ a = d.a + 8#64 ∨ (d.used = false ∧ (a = d.a + 0x10#64 ∨ a = d.a + 0x18#64))) :
    d.a.toNat ≤ a.toNat ∧ a.toNat ≤ d.a.toNat + 24 ∧ (d.used = true → a.toNat ≤ d.a.toNat + 8) := by
  have h8 : ∀ c : Word, c.toNat < 32 → (d.a + c).toNat = d.a.toNat + c.toNat := fun c hc => by
    rw [BitVec.toNat_add]; omega
  rcases ha with rfl | rfl | ⟨hu, rfl | rfl⟩
  · exact ⟨Nat.le_refl _, by omega, fun _ => by omega⟩
  · have : (d.a + 8#64).toNat = d.a.toNat + 8 := by rw [h8 _ (by decide)]; rfl
    rw [this]
    exact ⟨by omega, by omega, fun _ => by omega⟩
  · have : (d.a + 0x10#64).toNat = d.a.toNat + 16 := by rw [h8 _ (by decide)]; rfl
    rw [this]
    exact ⟨by omega, by omega, fun h => by simp [hu] at h⟩
  · have : (d.a + 0x18#64).toNat = d.a.toNat + 24 := by rw [h8 _ (by decide)]; rfl
    rw [this]
    exact ⟨by omega, by omega, fun h => by simp [hu] at h⟩

/-- A 32-aligned word, as a number. -/
theorem a32_mod {x : Word} (h : x &&& 31#64 = 0#64) : x.toNat % 32 = 0 := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and] at this
  simpa [Nat.and_two_pow_sub_one_eq_mod _ 5] using this

/-- What `realloc`'s caller gets back: the return, with the callee-saved registers and the
    code as they were; the owned statics' invariant and the protected memory kept; the heap well
    formed again; below the arena, off the control block, the stack window and the owned
    statics, nothing changed;
    every other live byte kept; and either null, with every used block kept, or a new block
    granted for the new size, with the old one freed. -/
def Done (env : Env) (s0 : MachineState) (base : Word) (bs : List Tlsf.Blk) (b : Tlsf.Blk)
    (t : MachineState) : Prop :=
  t.pc = s0.getReg .x1 &&& ~~~1#64 ∧ (∀ q ∈ savedRegs, t.getReg q = s0.getReg q) ∧
  t.code = s0.code ∧ env.Inv t.getMem ∧
  (∀ a, Aligned a → env.InProt a → t.getMem a = s0.getMem a) ∧
  ∃ bs' L', Tlsf.Rep HEAP base t.getMem bs' L' ∧
  (∀ a, Aligned a → a.toNat < base.toNat →
    ¬ (HEAP.toNat ≤ a.toNat ∧ a.toNat < HEAP.toNat + Tlsf.ctlSize) → ¬ env.InOwn a →
    (a.toNat + 0x60 < (s0.getReg .x2).toNat ∨ (s0.getReg .x2).toNat ≤ a.toNat) →
    t.getMem a = s0.getMem a) ∧
  (∀ a, Aligned a → Live bs a → ¬ (b.a.toNat ≤ a.toNat ∧ a.toNat < b.a.toNat + b.sz.toNat) →
    t.getMem a = s0.getMem a) ∧
  ((t.getReg .x10 = 0#64 ∧ ∀ c ∈ bs, c.used = true → c ∈ bs') ∨
   (∃ b' ∈ bs', b'.used = true ∧ b'.last = false ∧
    (∃ S, (⟨b'.a, S, false, false⟩ : Tlsf.Blk) ∈ bs ∧ b'.sz ≤ S) ∧
    b'.a + 16#64 ≤ t.getReg .x10 ∧ t.getReg .x10 ≤ t.getReg .x10 + s0.getReg .x13 ∧
    t.getReg .x10 + s0.getReg .x13 ≤ b'.a + b'.sz ∧
    t.getReg .x10 &&& (s0.getReg .x12 - 1#64) = 0#64 ∧
    (s0.getReg .x12 < 32#64 → t.getReg .x10 = b'.a + 16#64) ∧
    (32#64 ≤ s0.getReg .x12 → t.getMem (t.getReg .x10 + 0xfffffffffffffff8#64) = b'.a) ∧
    ∀ c ∈ bs, c.used = true → c ≠ b → c ∈ bs'))

/-- The prologue's stores are its frame's. -/
theorem prologue_mem {s0 : MachineState} (hsp : 0x60 ≤ (s0.getReg .x2).toNat) {a : Word}
    (ha : a.toNat + 0x30 ≤ (s0.getReg .x2).toNat - 0x30 ∨ (s0.getReg .x2).toNat ≤ a.toNat ∨
      a.toNat + 0x60 < (s0.getReg .x2).toNat)
    {c : Word} (hc : 2 ^ 64 - 0x30 ≤ c.toNat) : a ≠ s0.getReg .x2 + c := fun e =>
  slot_lt hsp hc (by omega) e.symm

/-- **`__rust_realloc` (`0x7801bd38`)**: `alloc` the new size, copy, `dealloc` the old block. -/
theorem spec (env : Env) (hok : env.Ok) (hinit : env.init = Layout.image.memAt)
    (hprot : (0x78000190#64, 0x157a8) ∈ env.prot)
    {G : MachineState → Prop} (hG : ∀ x, G x → env.Cfi x) {P : Prop} {n : Nat}
    {s0 : MachineState} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {b : Tlsf.Blk}
    (hpc : s0.pc = 0x7801bd38#64) (hcode : s0.code = C)
    (hrep : Tlsf.Rep HEAP base s0.getMem bs L) (hro : Alloc.RoOk s0.getMem)
    (hbs : b ∈ bs) (hbu : b.used = true) (hbl : b.last = false)
    (hsmall : s0.getReg .x12 ≤ 31#64 → s0.getReg .x10 = b.a + 16#64)
    (hbig : ¬ s0.getReg .x12 ≤ 31#64 →
      s0.getMem (s0.getReg .x10 + 0xfffffffffffffff8#64) = b.a ∧
      b.a.toNat + 16 ≤ (s0.getReg .x10 + 0xfffffffffffffff8#64).toNat ∧
      (s0.getReg .x10 + 0xfffffffffffffff8#64).toNat < b.a.toNat + b.sz.toNat ∧
      Aligned (s0.getReg .x10 + 0xfffffffffffffff8#64))
    (hptr : ¬ 6#64 < s0.getReg .x10 >>> 34)
    (hp : s0.getReg .x12 &&& (s0.getReg .x12 - 1#64) = 0#64) (hp0 : s0.getReg .x12 ≠ 0#64)
    (hsp : 0x60 ≤ (s0.getReg .x2).toNat) (hstk : (s0.getReg .x2).toNat ≤ 0x78000000)
    (hal : Aligned (s0.getReg .x2)) (hst : (s0.getReg .x2).toNat ≤ env.stackTop)
    (hprotM : ∀ a, Aligned a → env.InProt a → s0.getMem a = env.init a)
    (hInv : env.Inv s0.getMem)
    (hEnvC : ∀ a, HEAP.toNat ≤ a.toNat → a.toNat < HEAP.toNat + Tlsf.ctlSize →
      ¬ env.InProt a ∧ ¬ env.InOwn a)
    (hEnvA : ∀ a, base.toNat ≤ a.toNat → ¬ env.InProt a ∧ ¬ env.InOwn a)
    (hPO : ∀ a, env.InProt a → ¬ env.InOwn a)
    (hEnvS : ∀ a, env.InOwn a ∨ env.InProt a → (s0.getReg .x2).toNat ≤ a.toNat)
    (hk : ∀ t, Done env s0 base bs b t → SafeN G n P t) : SafeN G n P s0 := by
  have hsh0 := (Tlsf.rep_iff.mp hrep).2
  have hlay := hsh0.layout.1
  simp only [Tlsf.ctlSize] at hlay
  have hH : HEAP.toNat = 2013529632 := rfl
  -- What the allocator owns is the control block and the arena.
  have hNM : ∀ a, a.toNat < base.toNat → ¬ (HEAP.toNat ≤ a.toNat ∧ a.toNat < HEAP.toNat + 0x8210) →
      ¬ Alloc.Mine HEAP bs a := by
    intro a h1 h2
    rintro (hm | ⟨d, hd, hm | ⟨-, hm1, -⟩⟩)
    · simp only [Tlsf.ctlSize] at hm; exact h2 hm
    · have hdA := hsh0.blkA hd
      have : (d.a + 8#64).toNat = d.a.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
      subst hm; omega
    · have hdA := hsh0.blkA hd; omega
  have hEN : ∀ a, env.InOwn a ∨ env.InProt a → ¬ Alloc.Mine HEAP bs a := by
    intro a ha
    refine hNM a ?_ ?_
    · refine Classical.byContradiction fun h => ?_
      have := hEnvA a (by omega)
      rcases ha with ha | ha
      · exact this.2 ha
      · exact this.1 ha
    · intro h
      have := hEnvC a h.1 (by simp only [Tlsf.ctlSize]; omega)
      rcases ha with ha | ha
      · exact this.2 ha
      · exact this.1 ha
  have hbA := hsh0.blkA hbs
  rw [← setPC_self hpc]
  iterate 17 xstep code
  xag
  -- The prologue's frame.
  have hpm : ∀ a, (a.toNat + 0x30 ≤ (s0.getReg .x2).toNat - 0x30 ∨ (s0.getReg .x2).toNat ≤ a.toNat ∨
      a.toNat + 0x60 < (s0.getReg .x2).toNat) → ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat →
      a ≠ s0.getReg .x2 + c := fun a ha c hc => prologue_mem hsp ha hc
  refine Alloc.spec (bs := bs) (L := L) (base := base) rfl (by simp [hcode])
    (by
      xregs
      refine rep_congr (self := HEAP) hrep fun a ha => ?_
      have hn := hpm a (.inr (.inl (by omega)))
      simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
        hn 0xfffffffffffffff8#64 (by decide), hn 0xfffffffffffffff0#64 (by decide),
        hn 0xffffffffffffffe8#64 (by decide), hn 0xffffffffffffffe0#64 (by decide),
        hn 0xffffffffffffffd8#64 (by decide), hn 0xffffffffffffffd0#64 (by decide), if_false])
    (by
      refine ro_congr hro fun a h1 h2 => ?_
      have hn := hpm a (.inr (.inl (by omega)))
      simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
        hn 0xfffffffffffffff8#64 (by decide), hn 0xfffffffffffffff0#64 (by decide),
        hn 0xffffffffffffffe8#64 (by decide), hn 0xffffffffffffffe0#64 (by decide),
        hn 0xffffffffffffffd8#64 (by decide), hn 0xffffffffffffffd0#64 (by decide), if_false])
    (by xregs; rw [BitVec.toNat_add]; simp; omega) (by xregs; rw [BitVec.toNat_add]; simp; omega)
    (by xregs; decide) (by xregs; exact hp) (by xregs; exact hp0) ?_
  intro t1 hd1
  obtain ⟨M1, r, hout1, bs1, L1, hrep1, hused1, hfr1, hgr⟩ := hd1
  have om := hout1.mem
  have op := hout1.pc
  have osv := hout1.saved
  have oc := hout1.code
  have ores := hout1.res
  clear hout1
  simp only [getReg_setReg, MachineState.getReg_setPC, reduceCtorEq, ne_eq, not_false_eq_true,
    and_true, if_true, if_false, MachineState.getMem_setReg, MachineState.getMem_setPC,
    AsmVerif.RiscV.Frame.getReg_setMem] at om op osv oc hrep1 hfr1 hgr
  rw [show (2013529632#64 : Word) = HEAP from rfl] at hrep1 hfr1
  have hsp1 : (s0.getReg .x2 + 0xffffffffffffffd0#64).toNat = (s0.getReg .x2).toNat - 0x30 := by
    rw [BitVec.toNat_add]; simp; omega
  -- Memory after `alloc`, away from its frame and the allocator's own doublewords.
  have hA : ∀ a, ¬ Alloc.Mine HEAP bs a →
      ((s0.getReg .x2).toNat ≤ a.toNat ∨ a.toNat + 0x60 < (s0.getReg .x2).toNat) →
      t1.getMem a = s0.getMem a := by
    intro a h2 h3
    have hn := hpm a (.inr h3)
    rw [om _ (fun h => by unfold Alloc.InFrame at h; rw [hsp1] at h; omega), hfr1 _ h2]
    simp only [getMem_setMem, MachineState.getMem_setReg, hn 0xfffffffffffffff8#64 (by decide),
      hn 0xfffffffffffffff0#64 (by decide), hn 0xffffffffffffffe8#64 (by decide),
      hn 0xffffffffffffffe0#64 (by decide), hn 0xffffffffffffffd8#64 (by decide),
      hn 0xffffffffffffffd0#64 (by decide), if_false]
  -- The frame slots after the call.
  have hslot : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → t1.getMem (s0.getReg .x2 + c) =
      (((((((s0.setReg .x2 (s0.getReg .x2 + 0xffffffffffffffd0#64)).setMem
        (s0.getReg .x2 + 0xfffffffffffffff8#64) (s0.getReg .x1)).setMem
        (s0.getReg .x2 + 0xfffffffffffffff0#64) (s0.getReg .x8)).setMem
        (s0.getReg .x2 + 0xffffffffffffffe8#64) (s0.getReg .x9)).setMem
        (s0.getReg .x2 + 0xffffffffffffffe0#64) (s0.getReg .x18)).setMem
        (s0.getReg .x2 + 0xffffffffffffffd8#64) (s0.getReg .x19)).setMem
        (s0.getReg .x2 + 0xffffffffffffffd0#64) (s0.getReg .x20)).getMem (s0.getReg .x2 + c) := by
    intro c hc
    have h1 : (s0.getReg .x2 + c).toNat + 0x30 = (s0.getReg .x2).toNat + (c.toNat + 0x30 - 2 ^ 64) := by
      have := c.isLt; rw [BitVec.toNat_add]; omega
    rw [om _ (fun h => by unfold Alloc.InFrame at h; rw [hsp1] at h; have := c.isLt; omega),
      hfr1 _ (notMine_low hsh0 (by have := c.isLt; omega))]
  have ht1 : RS s0 t1 := by
    refine ⟨by rw [oc]; simp [hcode], ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [osv .x2 (by decide)]; xregs
    · rw [osv .x8 (by decide)]; xregs
    · rw [osv .x9 (by decide)]; xregs
    · rw [osv .x18 (by decide)]; xregs
    · simp only [untouched, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [osv _ (by decide)]; xregs)
    all_goals (rw [hslot _ (by decide)]; simp)
  have hpc1 : t1.pc = 0x7801bd7c#64 := by rw [op]; simp
  have hcode1 := ht1.code
  rw [← setPC_self hpc1]
  iterate 2 xstep code
  · -- `alloc` failed: return null.
    have hr0 : r = 0#64 := by rw [← ores]; simpa using hb
    refine exit (by rst) rfl fun t hpct hsvt hct hmt hrt => hk t ⟨hpct, hsvt, ?_, ?_, ?_, ?_⟩
    · rw [hct]; simp [ht1.code, hcode]
    · refine Env.Inv_congr (fun a _ ho => ?_) hInv
      rw [hmt]; simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
      exact hA a (hEN a (.inl ho)) (.inl (hEnvS a (.inl ho)))
    · intro a _ hp'
      rw [hmt]; simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
      exact hA a (hEN a (.inr hp')) (.inl (hEnvS a (.inr hp')))
    · refine ⟨bs1, L1, rep_congr hrep1 fun a ha => ?_, fun a _ h1 hc _ h2 => ?_,
        fun a _ hl hnb => ?_, .inl ⟨by rw [hrt]; xregs; rw [ores, hr0], hused1⟩⟩
      · rw [hmt]; simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
        exact om _ (fun h => by unfold Alloc.InFrame at h; rw [hsp1] at h; omega)
      · rw [hmt]; simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
        exact hA a (hNM a h1 (by simpa only [Tlsf.ctlSize] using hc)) (by omega)
      · rw [hmt]; simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
        obtain ⟨c, hc, hcu, h1, h2⟩ := hl
        have := (hsh0.blkA hc).2.1
        exact hA a (notMine_live hsh0 ⟨c, hc, hcu, h1, h2⟩) (.inl (by omega))
  -- `alloc` granted a block.
  have hr0 : r ≠ 0#64 := by rw [← ores]; simpa using hb
  obtain ⟨b', hb'1, hb'u, hb'l, ⟨S, hF, hb'S⟩, g1, g2, g3, g4, g5, g6⟩ :=
    hgr.resolve_left hr0
  have hsh1 := (Tlsf.rep_iff.mp hrep1).2
  have hb'A := hsh1.blkA hb'1
  have hb'40 := hsh1.layout.2.2 b' hb'1
  have hFA := hsh0.blkA hF
  have hr16 : b'.a.toNat + 16 ≤ r.toNat := by
    have := g1; rw [BitVec.le_def, BitVec.toNat_add] at this; simp at this; omega
  have hrn : r.toNat + (s0.getReg .x13).toNat ≤ b'.a.toNat + b'.sz.toNat := by
    have h2 := g2; have h3 := g3
    rw [BitVec.le_def, BitVec.toNat_add] at h2 h3
    rw [BitVec.toNat_add] at h3
    have := (s0.getReg .x13).isLt; have := r.isLt
    omega
  -- The copy, from `0x7801bd8c`, with `s4` the smaller size.
  have cpy : ∀ y, RS s0 y → y.pc = 0x7801bd8c#64 → y.getReg .x19 = r →
      (y.getReg .x20).toNat ≤ (s0.getReg .x13).toNat → y.getMem = t1.getMem →
      SafeN G n P y := by
    intro y hy hpcy q19 q20 qm
    have hcy := hy.code
    rw [← setPC_self hpcy]
    iterate 5 xstep code
    -- What the copy may write: the new block, past its header.
    have hhit : ∀ a, Hits r (y.getReg .x20).toNat a → r.toNat < a.toNat + 8 ∧
        a.toNat < b'.a.toNat + b'.sz.toNat := by
      intro a ha
      have := a.isLt; have := r.isLt
      rcases ha with ha | ⟨h0, ha⟩
      · rw [BitVec.toNat_sub] at ha
        have : r.toNat ≤ a.toNat := by
          refine Classical.byContradiction fun h => ?_
          rw [Nat.mod_eq_of_lt (by omega)] at ha; omega
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at ha
        omega
      · rw [BitVec.toNat_sub] at ha
        have : a.toNat ≤ r.toNat := by
          refine Classical.byContradiction fun h => ?_
          rw [Nat.mod_eq_of_lt (by omega)] at ha; omega
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at ha
        omega
    have hymem : ∀ v a, (((((y.setReg .x10 (y.getReg .x19)).setReg .x11 (y.getReg .x18)).setReg .x12
        (y.getReg .x20)).setReg .x1 0x7801bda0#64).setPC v).getMem a = t1.getMem a :=
      fun v a => by simp [qm]
    refine Memcpy.holds env hok hinit hprot n G hG P _ rfl
      ⟨by simp [hcy], Nat.zero_le _, ?_, ?_, fun a _ hp' => ?_, fun it hit a _ hh => ?_,
        by simp [Memcpy.iface], by simp [Memcpy.iface], by simp [Memcpy.iface],
        Env.Inv_congr (fun a _ ho => ?_) hInv, by simp [StrsPre, Memcpy.iface],
        by simp [Memcpy.iface]⟩ ?_
    · xregs; rw [hy.sp, BitVec.toNat_add]; simp; omega
    · xregs; rw [hy.sp]; exact al_add hal (by decide)
    · rw [hymem _ a, hA a (hEN a (.inr hp')) (.inl (hEnvS a (.inr hp')))]; exact hprotM a ‹_› hp'
    · simp only [Memcpy.iface, List.mem_singleton] at hit
      subst hit
      simp only [Item.Hits, AVal.eval, Len.eval, regsOf] at hh
      have e10 : ∀ v, ((((((y.setReg .x10 (y.getReg .x19)).setReg .x11 (y.getReg .x18)).setReg .x12
          (y.getReg .x20)).setReg .x1 0x7801bda0#64).setPC v).getReg .x10) = r := fun v => by
        xregs; exact q19
      have e12 : ∀ v, ((((((y.setReg .x10 (y.getReg .x19)).setReg .x11 (y.getReg .x18)).setReg .x12
          (y.getReg .x20)).setReg .x1 0x7801bda0#64).setPC v).getReg .x12) = y.getReg .x20 :=
        fun v => by xregs
      rw [e10, e12, show r + (0 : Word) = r from BitVec.add_zero r] at hh
      have := hhit a hh
      have hE := hEnvA a (by omega)
      refine ⟨fun hw => ?_, hE.1, hE.2⟩
      simp [InWin, Hits, Memcpy.iface] at hw
    · rw [hymem _ a, hA a (hEN a (.inl ho)) (.inl (hEnvS a (.inl ho)))]
    intro t ht
    obtain ⟨-, hpcm, hsvm, hmm, hcm, hinvm, -⟩ := ht
    -- What the copy leaves: everything aligned, not owned, outside the new block's tail.
    have hwr : ∀ a, Aligned a → ¬ env.InOwn a →
        ¬ (r.toNat < a.toNat + 8 ∧ a.toNat < b'.a.toNat + b'.sz.toNat) → t.getMem a = t1.getMem a := by
      intro a hal' ho hn
      rw [hmm a hal' (fun hw => ?_) ho (by simp [StrHit, Memcpy.iface]), hymem _ a]
      rcases hw with hw | ⟨it, hit, hh⟩
      · simp [InWin, Hits, Memcpy.iface] at hw
      · simp only [Memcpy.iface, List.mem_singleton] at hit
        subst hit
        simp only [Item.Hits, AVal.eval, Len.eval, regsOf] at hh
        have e10 : ∀ v, ((((((y.setReg .x10 (y.getReg .x19)).setReg .x11 (y.getReg .x18)).setReg .x12
            (y.getReg .x20)).setReg .x1 0x7801bda0#64).setPC v).getReg .x10) = r := fun v => by
          xregs; exact q19
        have e12 : ∀ v, ((((((y.setReg .x10 (y.getReg .x19)).setReg .x11 (y.getReg .x18)).setReg .x12
            (y.getReg .x20)).setReg .x1 0x7801bda0#64).setPC v).getReg .x12) = y.getReg .x20 :=
          fun v => by xregs
        rw [e10, e12, show r + (0 : Word) = r from BitVec.add_zero r] at hh
        exact hn (hhit a hh)
    have hsv : ∀ q ∈ savedRegs, q ≠ .x1 → q ≠ .x10 → q ≠ .x11 → q ≠ .x12 →
        t.getReg q = y.getReg q := fun q hq h1 h2 h3 h4 => by
      rw [hsvm q hq]; simp only [getReg_setReg, MachineState.getReg_setPC, h1, h2, h3, h4, false_and,
        if_false]
    have hlowS : ∀ a, a.toNat < (s0.getReg .x2).toNat → ¬ env.InOwn a := fun a ha ho => by
      have := hEnvS a (.inl ho); omega
    have hbase : (s0.getReg .x2).toNat < base.toNat := by omega
    have hslot2 : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → c &&& 7#64 = 0#64 →
        t.getMem (s0.getReg .x2 + c) = y.getMem (s0.getReg .x2 + c) := by
      intro c hc hc7
      have h1 : (s0.getReg .x2 + c).toNat < (s0.getReg .x2).toNat := by
        have := c.isLt; rw [BitVec.toNat_add]; omega
      rw [qm, hwr _ (al_add hal hc7) (hlowS _ h1) (by omega)]
    have htm : RS s0 t := by
      refine ⟨by rw [hcm]; simp [hcy], ?_, ?_, ?_, ?_, fun r' hr' => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsv .x2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hy.sp
      · rw [hsv .x8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hy.old
      · rw [hsv .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hy.align
      · rw [hsv .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hy.ptr
      · simp only [untouched, List.mem_cons, List.mem_nil_iff, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (rw [hsv _ (by decide) (by decide) (by decide) (by decide) (by decide)]
           exact hy.regs _ (by simp [untouched]))
      · rw [hslot2 _ (by decide) (by decide)]; exact hy.fra
      · rw [hslot2 _ (by decide) (by decide)]; exact hy.fs0
      · rw [hslot2 _ (by decide) (by decide)]; exact hy.fs1
      · rw [hslot2 _ (by decide) (by decide)]; exact hy.fs2
      · rw [hslot2 _ (by decide) (by decide)]; exact hy.fs3
      · rw [hslot2 _ (by decide) (by decide)]; exact hy.fs4
    -- The old and the new block are different blocks.
    have hbm1 : b ∈ bs1 := hused1 b hbs hbu
    have hbF : b.a ≠ b'.a := fun e => by
      have := hsh0.uniq hbs hF e
      rw [this] at hbu; exact absurd hbu (by simp)
    have hbb' : b ≠ b' := fun e => hbF (by rw [e])
    have hdisj := hsh1.disj hbm1 hb'1 hbb'
    have hbA1 := hsh1.blkA hbm1
    -- The heap after the copy.
    have hHal : Aligned HEAP := by unfold Aligned HEAP; decide
    have hbase1 := hbA1.2.1
    have hb'base := hb'A.2.1
    have hlay1 := hsh1.layout.1
    simp only [Tlsf.ctlSize] at hlay1
    have hrep2 : Tlsf.Rep HEAP base t.getMem bs1 L1 := by
      obtain ⟨hl1, hs1⟩ := Tlsf.rep_iff.mp hrep1
      refine Tlsf.rep_iff.mpr ⟨?_, congrA hs1 hHal fun a hk hal' => ?_⟩
      · rw [hwr _ hHal (fun ho => (hEnvC HEAP (Nat.le_refl _) (by simp [Tlsf.ctlSize, hH])).2 ho)
          (by rw [hH]; omega), om _ (fun h => by unfold Alloc.InFrame at h; rw [hsp1] at h; omega)]
        exact hl1
      · have hgt := key_gt hs1 hk
        have hkey : (a.toNat < HEAP.toNat + 0x8210) ∨ (base.toNat ≤ a.toNat ∧
            ¬ (r.toNat < a.toNat + 8 ∧ a.toNat < b'.a.toNat + b'.sz.toNat)) := by
          rcases hk with hk | ⟨d, hd, hk⟩
          · left; have := hk.2; simp only [Tlsf.ctlSize] at this; exact this
          · right
            have hdA := hsh1.blkA hd
            obtain ⟨k1, k2, k3⟩ := key_blk hdA.2.2 hk
            have hdsz := Tlsf.Shape.sz_ge (hsh1.blk hd).2.2.2.2
            refine ⟨by omega, ?_⟩
            by_cases hdb : d = b'
            · subst hdb; have := k3 hb'u; omega
            · rcases hsh1.disj hd hb'1 hdb with h | h <;> omega
        rw [hwr _ hal' ?_ ?_, om _ (fun h => by unfold Alloc.InFrame at h; rw [hsp1] at h; omega)]
        · intro ho
          rcases hkey with hk | hk
          · exact (hEnvC a (by omega) (by simp only [Tlsf.ctlSize]; omega)).2 ho
          · exact (hEnvA a hk.1).2 ho
        · rcases hkey with hk | hk
          · intro h; omega
          · exact hk.2
    -- With an alignment of 32 or more, the result is 32-aligned.
    have hr32 : 32#64 ≤ s0.getReg .x12 → r &&& 31#64 = 0#64 := by
      intro h32
      have : ∀ r al : BitVec 64, al &&& (al - 1#64) = 0#64 → 32#64 ≤ al →
          r &&& (al - 1#64) = 0#64 → r &&& 31#64 = 0#64 := by intro r al; bv_decide
      exact this r _ hp h32 g4
    -- The old block's back pointer is still there.
    have hbig2 : ¬ s0.getReg .x12 ≤ 31#64 →
        t.getMem (s0.getReg .x10 + 0xfffffffffffffff8#64) = b.a ∧
        b.a.toNat ≤ (s0.getReg .x10 + 0xfffffffffffffff8#64).toNat ∧
        (s0.getReg .x10 + 0xfffffffffffffff8#64).toNat < b.a.toNat + b.sz.toNat := by
      intro h31
      obtain ⟨e1, e2, e3, e4⟩ := hbig h31
      refine ⟨?_, by omega, e3⟩
      rw [hwr _ e4 (hEnvA _ (by omega)).2 (fun h => by rcases hdisj with h' | h' <;> omega),
        hA _ (notMine_live hsh0 ⟨b, hbs, hbu, e2, e3⟩) (.inl (by omega))]
      exact e1
    have hNM1 : ∀ a, a.toNat < base.toNat →
        ¬ (HEAP.toNat ≤ a.toNat ∧ a.toNat < HEAP.toNat + 0x8210) → ¬ Alloc.Mine HEAP bs1 a := by
      intro a h1 h2
      rintro (hm | ⟨d, hd, hm | ⟨-, hm1, -⟩⟩)
      · simp only [Tlsf.ctlSize] at hm; exact h2 hm
      · have hdA := hsh1.blkA hd
        have : (d.a + 8#64).toNat = d.a.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
        subst hm; omega
      · have hdA := hsh1.blkA hd; omega
    have hEN1 : ∀ a, env.InOwn a ∨ env.InProt a → ¬ Alloc.Mine HEAP bs1 a := by
      intro a ha
      refine hNM1 a ?_ ?_
      · refine Classical.byContradiction fun h => ?_
        have := hEnvA a (by omega)
        rcases ha with ha | ha
        · exact this.2 ha
        · exact this.1 ha
      · intro h
        have := hEnvC a h.1 (by simp only [Tlsf.ctlSize]; omega)
        rcases ha with ha | ha
        · exact this.2 ha
        · exact this.1 ha
    have hpct : t.pc = 0x7801bda0#64 := by rw [hpcm]; xregs; decide
    have hrx : t.getReg .x19 = r := by
      rw [hsv .x19 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q19
    refine afterCopy htm hpct hrep2 hbm1 hbu hbl hsmall hbig2 hptr hsp hstk
      fun t' hpc' hsv' hc' hr' ⟨bs', L', hrep', hkeep, hfr⟩ =>
        hk t' ⟨hpc', hsv', by rw [hc', hcode], ?_, ?_, bs', L', hrep', ?_, ?_, .inr ?_⟩
    · refine Env.Inv_congr (fun a _ ho => ?_) hinvm
      have := hEnvS a (.inl ho)
      exact hfr a (hEN1 a (.inl ho)) (fun h => (hEnvA a (by omega)).2 ho)
        (fun h => by unfold Dealloc.InFrame at h; rw [hsp1] at h; omega)
    · intro a hal' hp'
      have := hEnvS a (.inr hp')
      rw [hfr a (hEN1 a (.inr hp')) (fun h => (hEnvA a (by omega)).1 hp')
          (fun h => by unfold Dealloc.InFrame at h; rw [hsp1] at h; omega),
        hwr a hal' (hPO a hp') (fun h => (hEnvA a (by omega)).1 hp'),
        hA a (hEN a (.inr hp')) (.inl this)]
    · intro a hal' h1 hc hno h2
      simp only [Tlsf.ctlSize] at hc
      have hr16' := hr16
      rw [hfr a (hNM1 a h1 hc) (fun h => by omega)
          (fun h => by unfold Dealloc.InFrame at h; rw [hsp1] at h; omega),
        hwr a hal' hno (fun h => by omega), hA a (hNM a h1 hc) h2.symm]
    · intro a hal' hl hnb
      obtain ⟨c, hc, hcu, h1, h2⟩ := hl
      have hc1 := hused1 c hc hcu
      have hcbase := (hsh0.blkA hc).2.1
      have hcb' : c ≠ b' := fun e => by
        have := hsh0.uniq hc hF (by rw [e])
        rw [this] at hcu; exact absurd hcu (by simp)
      have hd := hsh1.disj hc1 hb'1 hcb'
      rw [hfr a (notMine_live hsh1 ⟨c, hc1, hcu, h1, h2⟩) hnb
          (fun h => by unfold Dealloc.InFrame at h; rw [hsp1] at h; omega),
        hwr a hal' (hEnvA a (by omega)).2 (fun h => by omega),
        hA a (notMine_live hsh0 ⟨c, hc, hcu, h1, h2⟩) (.inl (by omega))]
    · have hb'2 := hkeep b' hb'1 hb'u (Ne.symm hbb')
      rw [hr', hrx]
      refine ⟨b', hb'2, hb'u, hb'l, ⟨S, hF, hb'S⟩, g1, g2, g3, g4, g5, fun h32 => ?_,
        fun c hc hcu hcb => hkeep c (hused1 c hc hcu) hcu hcb⟩
      have h31 := hr32 h32
      have hal8 : Aligned (r + 0xfffffffffffffff8#64) := by
        unfold Aligned
        have : ∀ r : BitVec 64, r &&& 31#64 = 0#64 → (r + 0xfffffffffffffff8#64) &&& 7#64 = 0#64 := by
          intro r; bv_decide
        exact this r h31
      have e1 := a32_mod h31
      have e2 := a32_mod hb'A.1
      have hm8 : (r + 0xfffffffffffffff8#64).toNat = r.toNat - 8 := by
        rw [BitVec.toNat_add]; simp; omega
      rw [hfr _ (notMine_live hsh1 ⟨b', hb'1, hb'u, by omega, by omega⟩)
          (fun h => by rcases hdisj with h' | h' <;> omega)
          (fun h => by unfold Dealloc.InFrame at h; rw [hsp1] at h; omega),
        hwr _ hal8 (hEnvA _ (by omega)).2 (fun h => by omega),
        om _ (fun h => by unfold Alloc.InFrame at h; rw [hsp1] at h; omega)]
      exact g6 h32
  have hx20 : t1.getReg .x20 = s0.getReg .x13 := by rw [osv .x20 (by decide)]; xregs
  have hx8 : t1.getReg .x8 = s0.getReg .x11 := ht1.old
  xstep code
  · refine cpy _ (by rst) rfl (by xregs; exact ores) (by xregs; rw [hx20]; exact Nat.le_refl _)
      (by funext a; simp)
  · xstep code
    refine cpy _ (by rst) rfl (by xregs; exact ores) ?_ (by funext a; simp)
    xregs
    rw [hx8]
    rw [hx20, hx8] at hb
    simpa [BitVec.ult_iff_lt, BitVec.not_lt, BitVec.le_def] using hb

end Cases.Zip2005.Runtime.Realloc