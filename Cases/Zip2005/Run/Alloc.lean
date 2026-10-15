/-
  Cases.Zip2005.Run.Alloc

  `__rust_alloc` (`0x7801bcec`) under the run's invariant (milestone M1).

  The shim passes `INNER_HEAP`, the alignment and the size to rlsf's `alloc` (`0x7801c18c`),
  whose phase-D specification `Alloc.spec` this lifts: from `HeapAt L` and the read-only image,
  the call returns with the callee-saved registers, the code and the private input kept,
  nothing changed outside its frame, the control block and the arena, the read-only image
  kept, every live buffer's bytes kept, and `HeapAt ((ptr, k) :: L)`: the result is null or a
  used block's payload of `k` doublewords.
-/

import Cases.Zip2005.Run.Ro
import Cases.Zip2005.Runtime.Alloc.Spec
import Cases.Zip2005.Image.F_7801bcec

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Sym AsmVerif.RiscV.Frame AsmVerif.RiscV.Check
  AsmVerif.RiscV.Exec Cases.Zip2005 Cases.Zip2005.Image Cases.Zip2005.Runtime

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def allocFn : AsmVerif.RiscV.Frame.Fn := { base := F_7801bcec.base, prog := F_7801bcec.prog }

theorem allocFn_code : AsmVerif.RiscV.Check.CodeAt allocFn C :=
  codeAt_of_image (k := 27) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [allocFn] at h)

/-- The allocator's own doublewords lie in the control block or the arena. -/
theorem mine_range {bs : List Tlsf.Blk} {m : Word → Word} {Lf : Word → Word → List Word}
    (h : Tlsf.Rep HEAP BASE m bs Lf) (hs : sentinel ∈ bs) {a : Word} (ha : Alloc.Mine HEAP bs a) :
    (0x78040620 ≤ a.toNat ∧ a.toNat < 0x78048830) ∨ (0x78048980 ≤ a.toNat ∧ a.toNat < TOP) := by
  rcases ha with ha | ⟨b, hb, ha | ⟨_, h1, h2⟩⟩
  · left; simp only [Tlsf.ctlSize] at ha; simpa using ha
  · right
    have hA := (Tlsf.rep_iff.mp h).2.blkA hb
    have hz := Tlsf.Shape.sz_ge ((Tlsf.rep_iff.mp h).2.blk hb).2.2.2.2
    have he := end_le h hs hb
    have hl := base_le h hb
    have : (b.a + 8#64).toNat = b.a.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    subst ha; omega
  · right
    have he := end_le h hs hb
    have hl := base_le h hb
    omega

/-- A live buffer's byte, not null, is none of the allocator's own. -/
theorem notMine_of_live {bs : List Tlsf.Blk} {m : Word → Word} {Lf : Word → Word → List Word}
    (h : Tlsf.Rep HEAP BASE m bs Lf) {r : Word × Nat} (hr : LiveOk bs r) {a : Word}
    (ha : InRegion a r.1 r.2) (hlo : 0x78040620 ≤ a.toNat) : ¬ Alloc.Mine HEAP bs a := by
  rcases live_range h hr ha with h1 | ⟨c, hc, hcu, h1, h2⟩
  · omega
  · exact Realloc.notMine_live (Tlsf.rep_iff.mp h).2 ⟨c, hc, hcu, h1, h2⟩

/-- A used, non-final block of `bs` is one of `bs'` when `alloc` keeps every used block. -/
theorem liveOk_keep {bs bs' : List Tlsf.Blk} (hk : ∀ b ∈ bs, b.used = true → b ∈ bs')
    {r : Word × Nat} (h : LiveOk bs r) : LiveOk bs' r := by
  rcases h with h | ⟨b, hb, hu, hl, ha, hz⟩
  · exact .inl h
  · exact .inr ⟨b, hk b hb hu, hu, hl, ha, hz⟩

/-- **rlsf's `alloc` (`0x7801c18c`) on `INNER_HEAP`**, the call `__rust_alloc` tails into and
    `__rust_realloc` makes: as `rust_alloc`, from the inner entry. -/
theorem heap_alloc {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    {L : List (Word × Nat)} {k sz : Nat} {al : Word}
    (hpc : u.pc = 0x7801c18c#64) (hcode : u.code = C)
    (hsp : 0x30 ≤ (u.getReg .x2).toNat) (hstk : (u.getReg .x2).toNat ≤ 0x78000000)
    (hx10 : u.getReg .x10 = HEAP) (hsz : u.getReg .x12 = BitVec.ofNat 64 sz)
    (hsz1 : sz ≤ 8 * k) (hsz2 : 8 * k ≤ sz + 7) (hk8 : 8 * k ≤ 0x78040620)
    (hal : u.getReg .x11 = al) (halp : al &&& (al - 1#64) = 0#64) (hal0 : al ≠ 0#64)
    (hal32 : al < 32#64)
    (hro : RoImage Ro.layout u) (hh : HeapAt L u)
    (hk : ∀ (t : MachineState) (ptr : Word), t.pc = u.getReg .x1 &&& ~~~1#64 →
      CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
      Unchanged [(u.getReg .x2 - 0x30#64, 6), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = ptr → RoImage Ro.layout t → HeapAt ((ptr, k) :: L) t →
      (ptr.toNat = 0 ∨ (0x78048990 ≤ ptr.toNat ∧ ptr.toNat + 8 * k ≤ TOP)) →
      (∀ r ∈ L, ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
      SafeN G n P t) :
    SafeN G n P u := by
  obtain ⟨hhk, hhash, hD, bs, Lf, hrep, hsent, hL⟩ := hh.holds
  refine Alloc.spec (bs := bs) (L := Lf) (base := BASE) hpc hcode ?_
    ?_ hsp hstk (by rw [hx10]; decide) (by rw [hal]; exact halp)
    (by rw [hal]; exact hal0) ?_
  · rw [hx10]; exact hrep
  · exact roOk hro
  intro t hd
  obtain ⟨M', r, hout, bs', Lf', hrep', hused, hfr, hgr⟩ := hd
  rw [hx10] at hrep' hfr
  rw [hal, hsz] at hgr
  have hsp30 : (u.getReg .x2 - 0x30#64).toNat = (u.getReg .x2).toNat - 0x30 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hsp)]; rfl
  -- memory off the frame and the allocator's own doublewords is `u`'s
  have hoff : ∀ a, ((u.getReg .x2).toNat ≤ a.toNat ∨ a.toNat < (u.getReg .x2).toNat - 0x30) →
      ¬ Alloc.Mine HEAP bs a → t.getMem a = u.getMem a := by
    intro a h1 h2
    rw [hout.mem a (by unfold Alloc.InFrame; omega), hfr a h2]
  have hsent' : sentinel ∈ bs' := hused _ hsent rfl
  -- closed statics above the control block are no allocator doubleword
  have hstat : ∀ a, 0x78048830 ≤ a.toNat → a.toNat < 0x78048980 → t.getMem a = u.getMem a := by
    intro a h1 h2
    refine hoff a (.inl (by omega)) fun hm => ?_
    rcases mine_range hrep hsent hm with h | h <;> omega
  refine hk t r hout.pc hout.saved
    (by rw [hout.code]) hout.priv ?_ hout.res ?_ ?_ ?_ ?_
  · -- the frame
    intro a ha
    have h1 := ha _ (List.mem_cons_self ..)
    have h2 := ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h3 := ha _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only [InRegion, hsp30, not_and, Nat.not_lt] at h1 h2 h3
    refine hoff a (by omega) fun hm => ?_
    rcases mine_range hrep hsent hm with h | h
    · simp at h2; omega
    · simp [TOP] at h3 h; omega
  · -- the read-only image
    refine hro.of_unchanged (W := [(u.getReg .x2 - 0x30#64, 6), (0x78040620#64, 4162),
      (0x78048980#64, 14780690128)]) ?_ ?_
    · intro a ha
      have h1 := ha _ (List.mem_cons_self ..)
      have h2 := ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have h3 := ha _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      simp only [InRegion, hsp30, not_and, Nat.not_lt] at h1 h2 h3
      refine hoff a (by omega) fun hm => ?_
      rcases mine_range hrep hsent hm with h | h
      · simp at h2; omega
      · simp [TOP] at h3 h; omega
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · simp [hsp30, Ro.layout]; omega
      · simp [Ro.layout]
      · simp [Ro.layout]
  · -- the invariant, with the new buffer live
    refine heapAt_of ⟨fun c hc => ?_, ?_, List.Pairwise.cons ?_ hD, bs', Lf', ?_, hsent', ?_⟩
    · simp only [hookKeys, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rw [← hhk c (by simp [hookKeys, hc])]
      rcases hc with rfl | rfl | rfl | rfl <;> exact hstat _ (by decide) (by decide)
    · rw [Owned.HasherOk, hstat _ (by decide) (by decide), hstat _ (by decide) (by decide)]
      exact hhash
    · -- the new pointer is no live one: its block was free
      intro q hq
      rcases hgr with h0 | ⟨b, hb, hbu, hbl, ⟨S, hS, _⟩, h1, h2, h3, _, h5, _⟩
      · exact .inl h0
      · right
        rcases hL q hq with ⟨h0, _⟩ | ⟨c, hc, hcu, _, hca, _⟩
        · rw [h0, h5 hal32]; intro e
          have hbA := (Tlsf.rep_iff.mp hrep').2.blkA hb
          have hl := (Tlsf.rep_iff.mp hrep').2.layout.2.2 b hb
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_add] at this; simp at this; omega
        · rw [h5 hal32, ← hca]; intro e
          have hsh := (Tlsf.rep_iff.mp hrep).2
          have hcl := hsh.layout.2.2 c hc
          have hSl := hsh.layout.2.2 _ hS
          have hab : b.a = c.a := by
            have := congrArg BitVec.toNat e
            rw [BitVec.toNat_add, BitVec.toNat_add] at this
            simp at this
            exact BitVec.eq_of_toNat_eq (by omega)
          have := hsh.uniq hS hc (by simpa using hab)
          rw [← this] at hcu; exact absurd hcu (by simp)
    · exact Realloc.rep_congr hrep' fun a ha => hout.mem a (by
        unfold Alloc.InFrame; simp at ha; omega)
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rcases hgr with h0 | ⟨b, hb, hbu, hbl, _, h1, h2, h3, _, h5, _⟩
        · exact .inl ⟨h0, hk8⟩
        · refine .inr ⟨b, hb, hbu, hbl, (h5 hal32).symm, ?_⟩
          have hbA := (Tlsf.rep_iff.mp hrep').2.blkA hb
          have hl := (Tlsf.rep_iff.mp hrep').2.layout.2.2 b hb
          rw [BitVec.le_def] at h2 h3
          have e8 : (BitVec.ofNat 64 sz).toNat = sz := by simp; omega
          rw [BitVec.toNat_add, BitVec.toNat_add, e8] at h3
          rw [BitVec.toNat_add, e8] at h2
          have : b.a.toNat + b.sz.toNat < 2 ^ 64 := by omega
          rw [Nat.mod_eq_of_lt this] at h3
          have : r.toNat + sz < 2 ^ 64 := by
            by_contra hc
            rw [Nat.mod_eq_sub_mod (by omega)] at h2
            have := r.isLt
            rw [Nat.mod_eq_of_lt (by omega)] at h2
            omega
          rw [Nat.mod_eq_of_lt this] at h3
          -- the block is a granule multiple past its header: the size rounded to doublewords fits
          have hbz := Realloc.a32_mod ((Tlsf.rep_iff.mp hrep').2.blk hb).2.2.2.1
          have hr : r.toNat = b.a.toNat + 16 := by rw [h5 hal32, BitVec.toNat_add]; simp; omega
          dsimp only
          omega
      · exact liveOk_keep (fun b hb hu => hused b hb hu) (hL q hq)
  · -- where the result lies
    rcases hgr with h0 | ⟨b, hb, hbu, hbl, _, h1, h2, h3, _, h5, _⟩
    · exact .inl (by rw [h0]; rfl)
    · right
      have hbA := (Tlsf.rep_iff.mp hrep').2.blkA hb
      have hl := (Tlsf.rep_iff.mp hrep').2.layout.2.2 b hb
      have he := end_le hrep' hsent' hb
      have hbl' := base_le hrep' hb
      have hr16 := h5 hal32
      rw [BitVec.le_def] at h2 h3
      have e8 : (BitVec.ofNat 64 sz).toNat = sz := by simp; omega
      rw [BitVec.toNat_add, BitVec.toNat_add, e8] at h3
      rw [BitVec.toNat_add, e8] at h2
      have hr : r.toNat = b.a.toNat + 16 := by rw [hr16, BitVec.toNat_add]; simp; omega
      have hbz := Realloc.a32_mod ((Tlsf.rep_iff.mp hrep').2.blk hb).2.2.2.1
      have : b.a.toNat + b.sz.toNat < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)] at h3
      simp only [TOP] at he ⊢
      omega
  · -- live buffers kept
    intro q hq a hq0 ha
    rcases hL q hq with ⟨h0, _⟩ | hlive
    · exact absurd h0 hq0
    · have hlo : 0x78040620 ≤ a.toNat := by
        rcases live_range hrep (hL q hq) ha with h | ⟨c, hc, _, h1, _⟩
        · rcases hlive with ⟨c, hc, _, _, hca, _⟩
          have hcA := (Tlsf.rep_iff.mp hrep).2.blkA hc
          have hcl := base_le hrep hc
          have hlc := (Tlsf.rep_iff.mp hrep).2.layout.2.2 c hc
          have : (c.a + 16#64).toNat = c.a.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
          unfold InRegion at ha; rw [← hca, this] at ha; omega
        · have := base_le hrep hc; omega
      exact hoff a (.inl (by omega)) (notMine_of_live hrep (hL q hq) ha hlo)

/-- **`__rust_alloc(8 k, align)`**, for an alignment below 32. -/
theorem rust_alloc {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    {L : List (Word × Nat)} {k sz : Nat} {al : Word}
    (hpc : u.pc = 0x7801bcec#64) (hcode : u.code = C)
    (hsp : 0x30 ≤ (u.getReg .x2).toNat) (hstk : (u.getReg .x2).toNat ≤ 0x78000000)
    (hsz : u.getReg .x10 = BitVec.ofNat 64 sz) (hsz1 : sz ≤ 8 * k) (hsz2 : 8 * k ≤ sz + 7)
    (hk8 : 8 * k ≤ 0x78040620)
    (hal : u.getReg .x11 = al) (halp : al &&& (al - 1#64) = 0#64) (hal0 : al ≠ 0#64)
    (hal32 : al < 32#64)
    (hro : RoImage Ro.layout u) (hh : HeapAt L u)
    (hk : ∀ (t : MachineState) (ptr : Word), t.pc = u.getReg .x1 &&& ~~~1#64 →
      CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
      Unchanged [(u.getReg .x2 - 0x30#64, 6), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = ptr → RoImage Ro.layout t → HeapAt ((ptr, k) :: L) t →
      (ptr.toNat = 0 ∨ (0x78048990 ≤ ptr.toNat ∧ ptr.toNat + 8 * k ≤ TOP)) →
      (∀ r ∈ L, ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
      SafeN G n P t) :
    SafeN G n P u := by
  rw [← setPC_self hpc]
  iterate 7 xstep allocFn_code
  xag
  set y := (((((u.setReg Reg.x12 2013529632#64).setReg Reg.x13 (u.getReg Reg.x10)).setReg Reg.x10
    2013529632#64).setReg Reg.x12 (u.getReg Reg.x10)).setReg Reg.x6 2013379840#64).setPC
      2013381004#64 with hy
  have ym : ∀ a, y.getMem a = u.getMem a := fun a => by
    simp [hy, MachineState.getMem_setReg, MachineState.getMem_setPC]
  have y1 : y.getReg .x1 = u.getReg .x1 := by simp only [hy]; xregs
  have y2 : y.getReg .x2 = u.getReg .x2 := by simp only [hy]; xregs
  have y10 : y.getReg .x10 = HEAP := by simp only [hy]; xregs
  have y11 : y.getReg .x11 = al := by simp only [hy]; xregs; exact hal
  have y12 : y.getReg .x12 = BitVec.ofNat 64 sz := by simp only [hy]; xregs; exact hsz
  have ysv : ∀ q ∈ savedRegs, y.getReg q = u.getReg q := by
    intro q hq
    simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> (simp only [hy]; xregs)
  have ymem : y.getMem = u.getMem := funext ym
  have yeq : y.mem = u.mem := by rw [hy]; rfl
  refine heap_alloc (u := y) (by simp [hy]) (by simp [hy, hcode]) (by rw [y2]; exact hsp)
    (by rw [y2]; exact hstk) y10 y12 hsz1 hsz2 hk8 y11 halp hal0 hal32 (hro.of_mem_eq yeq)
    (hh.of_mem_eq yeq) ?_
  intro t ptr hpc' hcs hcode' hpriv hun hx hro' hh' hptr hkeep
  rw [y2] at hun
  refine hk t ptr (by rw [hpc', y1]) (fun q hq => by rw [hcs q hq, ysv q hq])
    (by rw [hcode']; simp [hy]) (by rw [hpriv]; simp [hy]) (fun a ha => (hun a ha).trans (ym a))
    hx hro' hh' hptr fun r hr a h0 ha => (hkeep r hr a h0 ha).trans (ym a)

end Cases.Zip2005.Run
