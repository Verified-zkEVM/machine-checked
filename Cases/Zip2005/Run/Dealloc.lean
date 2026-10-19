/-
  Cases.Zip2005.Run.Dealloc

  `__rust_dealloc` (`0x7801bd08`) under the run's invariant (milestone M1).

  The shim returns at once for a pointer at or above `7 << 34` (the hint area, which no
  allocator owns), and otherwise passes `INNER_HEAP`, the pointer, the alignment and the size
  to rlsf's `dealloc` (`0x7801c620`), whose phase-D specification `Dealloc.spec` this lifts:
  the freed buffer, the head of the live list, leaves it; every other live buffer's bytes are
  kept.
-/

import Cases.Zip2005.Run.Alloc
import Cases.Zip2005.Runtime.Dealloc.Spec
import Cases.Zip2005.Image.F_7801bd08

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.RiscV.Frame MachineChecked.RiscV.Check
  MachineChecked.RiscV.Exec Cases.Zip2005 Cases.Zip2005.Image Cases.Zip2005.Runtime

def deallocFn : MachineChecked.RiscV.Frame.Fn := { base := F_7801bd08.base, prog := F_7801bd08.prog }

theorem deallocFn_code : MachineChecked.RiscV.Check.CodeAt deallocFn C :=
  codeAt_of_image (k := 28) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [deallocFn] at h)

/-- **`__rust_dealloc` of a hint-area pointer** returns at once. -/
theorem rust_dealloc_hint {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    (hpc : u.pc = 0x7801bd08#64) (hcode : u.code = C)
    (hptr : TOP ≤ (u.getReg .x10).toNat)
    (hk : ∀ t : MachineState, t.pc = u.getReg .x1 &&& ~~~1#64 → CalleeSaved u t →
      t.code = u.code → t.privateInput = u.privateInput → t.mem = u.mem → SafeN G n P t) :
    SafeN G n P u := by
  rw [← setPC_self hpc]
  iterate 4 xstep deallocFn_code
  · exfalso
    simp only [TOP] at hptr
    apply hb
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ushiftRight]
    simp; omega
  xstep deallocFn_code
  refine hk _ (by simp) ?_ (by simp) (by simp) rfl
  intro r hr
  simp only [calleeSavedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> xregs

/-- **rlsf's `dealloc` (`0x7801c620`) on `INNER_HEAP`**, of the live list's head: the call
    `__rust_dealloc` and `__rust_realloc` make. -/
theorem heap_dealloc {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    {L : List (Word × Nat)} {k : Nat} {ptr al : Word}
    (hpc : u.pc = 0x7801c620#64) (hcode : u.code = C)
    (hsp : 0x20 ≤ (u.getReg .x2).toNat) (hstk : (u.getReg .x2).toNat ≤ 0x78000000)
    (hx10 : u.getReg .x10 = HEAP) (hp : u.getReg .x11 = ptr) (hp0 : ptr ≠ 0#64) (hal : u.getReg .x12 = al) (hal32 : al ≤ 31#64)
    (hh : HeapAt ((ptr, k) :: L) u)
    (hk : ∀ t : MachineState, t.pc = u.getReg .x1 &&& ~~~1#64 → CalleeSaved u t →
      t.code = u.code → t.privateInput = u.privateInput →
      Unchanged [(u.getReg .x2 - 0x20#64, 4), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] u t → HeapAt L t →
      (∀ r ∈ L, ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
      SafeN G n P t) :
    SafeN G n P u := by
  obtain ⟨hhk, hhash, hD, bs, Lf, hrep, hsent, hL⟩ := hh.holds
  obtain ⟨b, hbm, hbu, hbl, hba, hbz⟩ : ∃ b ∈ bs, b.used = true ∧ b.last = false ∧
      b.a + 16#64 = ptr ∧ ptr.toNat + 8 * k ≤ b.a.toNat + b.sz.toNat := by
    rcases hL _ (List.mem_cons_self ..) with ⟨h0, _⟩ | h
    · exact absurd h0 hp0
    · exact h
  have hsh := (Tlsf.rep_iff.mp hrep).2
  have hbA := hsh.blkA hbm
  have hbe := end_le hrep hsent hbm
  have hbb := base_le hrep hbm
  have hbz32 := Tlsf.Shape.sz_ge (hsh.blk hbm).2.2.2.2
  have hpt : ptr.toNat = b.a.toNat + 16 := by rw [← hba, BitVec.toNat_add]; simp; omega
  refine Dealloc.spec (bs := bs) (L := Lf) (b := b) (base := BASE) hpc
    (by rw [hcode]) (by rw [hx10]; exact hrep) hbm hbu hbl
    (fun _ => by rw [hp, hba]) (fun h => absurd (hal ▸ hal32) h) hsp
    (by rw [hx10]; simp; omega) ?_
  intro t hd
  obtain ⟨M', hout, bs', Lf', hrep', hkeep, hfr⟩ := hd
  rw [hx10] at hrep' hfr
  have hsp20 : (u.getReg .x2 - 0x20#64).toNat = (u.getReg .x2).toNat - 0x20 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using hsp)]; rfl
  -- memory off the frame, the allocator's own doublewords and `b` is `u`'s
  have hoff : ∀ a, ((u.getReg .x2).toNat ≤ a.toNat ∨ a.toNat < (u.getReg .x2).toNat - 0x20) →
      ¬ Alloc.Mine HEAP bs a → ¬ (b.a.toNat ≤ a.toNat ∧ a.toNat < b.a.toNat + b.sz.toNat) →
      t.getMem a = u.getMem a := by
    intro a h1 h2 h3
    rw [hout.mem a (by unfold Dealloc.InFrame; omega), hfr a h2 h3]
  have hsent' : sentinel ∈ bs' :=
    hkeep _ hsent rfl (fun e => by rw [← e] at hbl; exact absurd hbl (by simp [sentinel]))
  have hstat : ∀ a, 0x78048830 ≤ a.toNat → a.toNat < 0x78048980 → t.getMem a = u.getMem a := by
    intro a h1 h2
    refine hoff a (.inl (by omega)) (fun hm => ?_) (by omega)
    rcases mine_range hrep hsent hm with h | h <;> omega
  -- a live buffer of the tail is in another block than `b`
  have hother : ∀ r ∈ L, ∀ c ∈ bs, c.used = true → c.a + 16#64 = r.1 → c ≠ b := by
    intro r hr c _ _ hca e
    subst e
    rcases List.rel_of_pairwise_cons hD hr with h | h
    · exact hp0 h
    · exact h (by rw [← hba, hca])
  refine hk t hout.pc hout.saved hout.code hout.priv ?_ ?_ ?_
  · -- the frame
    intro a ha
    have h1 := ha _ (List.mem_cons_self ..)
    have h2 := ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h3 := ha _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only [InRegion, hsp20, not_and, Nat.not_lt] at h1 h2 h3
    simp [TOP] at hbe
    refine hoff a (by omega) (fun hm => ?_) (by simp at h3; omega)
    rcases mine_range hrep hsent hm with h | h
    · simp at h2; omega
    · simp [TOP] at h3 h; omega
  · -- the invariant, the head freed
    refine heapAt_of ⟨fun c hc => ?_, ?_, hD.of_cons, bs', Lf', ?_, hsent', ?_⟩
    · simp only [hookKeys, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rw [← hhk c (by simp [hookKeys, hc])]
      rcases hc with rfl | rfl | rfl | rfl <;> exact hstat _ (by decide) (by decide)
    · rw [Owned.HasherOk, hstat _ (by decide) (by decide), hstat _ (by decide) (by decide)]
      exact hhash
    · exact Realloc.rep_congr hrep' fun a ha => hout.mem a (by
        unfold Dealloc.InFrame; simp at ha; omega)
    · intro r hr
      rcases hL r (List.mem_cons_of_mem _ hr) with h | ⟨c, hc, hcu, hcl, hca, hcz⟩
      · exact .inl h
      · exact .inr ⟨c, hkeep c hc hcu (hother r hr c hc hcu hca), hcu, hcl, hca, hcz⟩
  · -- live buffers kept
    intro r hr a hr0 ha
    rcases hL r (List.mem_cons_of_mem _ hr) with ⟨h0, _⟩ | ⟨c, hc, hcu, hcl, hca, hcz⟩
    · exact absurd h0 hr0
    · have hcA := hsh.blkA hc
      have hcb := base_le hrep hc
      have hlc := hsh.layout.2.2 c hc
      have e16 : (c.a + 16#64).toNat = c.a.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
      have ha' := ha
      unfold InRegion at ha'; rw [← hca, e16] at ha'
      rw [← hca, e16] at hcz
      have hne := hother r hr c hc hcu hca
      refine hoff a (.inl (by omega)) (notMine_of_live hrep (hL r (List.mem_cons_of_mem _ hr)) ha
        (by omega)) ?_
      rcases hsh.disj hc hbm hne with h | h <;> omega

/-- **`__rust_dealloc` of the live list's head**, a heap buffer, with an alignment below 32. -/
theorem rust_dealloc {G : MachineState → Prop} {n : Nat} {P : Prop} {u : MachineState}
    {L : List (Word × Nat)} {k : Nat} {ptr al : Word}
    (hpc : u.pc = 0x7801bd08#64) (hcode : u.code = C)
    (hsp : 0x20 ≤ (u.getReg .x2).toNat) (hstk : (u.getReg .x2).toNat ≤ 0x78000000)
    (hp : u.getReg .x10 = ptr) (hp0 : ptr ≠ 0#64) (hal : u.getReg .x12 = al) (hal32 : al ≤ 31#64)
    (hh : HeapAt ((ptr, k) :: L) u)
    (hk : ∀ t : MachineState, t.pc = u.getReg .x1 &&& ~~~1#64 → CalleeSaved u t →
      t.code = u.code → t.privateInput = u.privateInput →
      Unchanged [(u.getReg .x2 - 0x20#64, 4), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] u t → HeapAt L t →
      (∀ r ∈ L, ∀ a, r.1 ≠ 0#64 → InRegion a r.1 r.2 → t.getMem a = u.getMem a) →
      SafeN G n P t) :
    SafeN G n P u := by
  obtain ⟨hhk, hhash, hD, bs, Lf, hrep, hsent, hL⟩ := hh.holds
  obtain ⟨b, hbm, hbu, hbl, hba, hbz⟩ : ∃ b ∈ bs, b.used = true ∧ b.last = false ∧
      b.a + 16#64 = ptr ∧ ptr.toNat + 8 * k ≤ b.a.toNat + b.sz.toNat := by
    rcases hL _ (List.mem_cons_self ..) with ⟨h0, _⟩ | h
    · exact absurd h0 hp0
    · exact h
  have hsh := (Tlsf.rep_iff.mp hrep).2
  have hbA := hsh.blkA hbm
  have hbe := end_le hrep hsent hbm
  have hbb := base_le hrep hbm
  have hbz32 := Tlsf.Shape.sz_ge (hsh.blk hbm).2.2.2.2
  have hpt : ptr.toNat = b.a.toNat + 16 := by rw [← hba, BitVec.toNat_add]; simp; omega
  rw [← setPC_self hpc]
  iterate 4 xstep deallocFn_code
  swap
  · exfalso
    apply hb
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ushiftRight]
    rw [hp, show (34#6 : BitVec 6).toNat = 34 from rfl, show (6#64 : Word).toNat = 6 from rfl]
    simp only [TOP] at hbe; omega
  iterate 7 xstep deallocFn_code
  xag
  -- the state at `dealloc`'s entry, by what the proof needs of it
  have yeq : ∀ y : MachineState, y.getMem = u.getMem → y.mem = u.mem := fun y h => by
    funext a; exact congrFun h a
  suffices main : ∀ y : MachineState, y.pc = 0x7801c620#64 → y.code = u.code → y.getMem = u.getMem →
      y.privateInput = u.privateInput → y.getReg .x1 = u.getReg .x1 → y.getReg .x2 = u.getReg .x2 →
      y.getReg .x10 = HEAP → y.getReg .x11 = ptr → y.getReg .x12 = al →
      (∀ q ∈ savedRegs, y.getReg q = u.getReg q) → SafeN G n P y by
    refine main _ (by simp) (by simp) (funext fun a => by simp [MachineState.getMem_setReg,
      MachineState.getMem_setPC]) (by simp) (by xregs) (by xregs) (by xregs) (by xregs; exact hp)
      (by xregs; exact hal) ?_
    intro q hq
    simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> xregs
  intro y ypc yc ym yp y1 y2 y10 y11 y12 ysv
  refine heap_dealloc (u := y) ypc (by rw [yc, hcode]) (by rw [y2]; exact hsp) (by rw [y2]; exact hstk)
    y10 y11 hp0 y12 hal32 (hh.of_mem_eq (yeq y ym)) ?_
  intro t hpc' hcs hcode' hpriv hun hh' hkeep
  rw [y2] at hun
  refine hk t (by rw [hpc', y1]) (fun q hq => by rw [hcs q hq, ysv q hq]) (by rw [hcode', yc])
    (by rw [hpriv, yp]) (fun a ha => (hun a ha).trans (congrFun ym a)) hh'
    fun r hr a h0 ha => (hkeep r hr a h0 ha).trans (congrFun ym a)

end Cases.Zip2005.Run
