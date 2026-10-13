/-
  Cases.Zip2005.Runtime.Dealloc.Exec

  rlsf's `dealloc` (`GlobalAlloc::dealloc` for the TLSF heap, `0x7801c620`), run by the
  symbolic executor (phase D4).

  `St` is what holds inside `dealloc` after its prologue: the frame holds the saved registers,
  `s0` the heap, and memory off the frame is a model `M`. The segments:

  * `entry` (`0x7801c620`): take the lock, find the block (`blkOf`: below the pointer, or the
    address stored below it for a large alignment).
  * `nextSeg` (`0x7801c66c`): if the next block is free, unlink it from its list
    (`Tlsf.unlinkMem`; at its head, `popTail` after the class arithmetic `clsN`, `headN`).
  * `prevSeg` (`0x7801c7e0`): the same for the previous block (`clsP`, `headP`), which then
    starts the merged block.
  * `relSeg` (`0x7801c818`): the merged block's header, its list and links, the bitmaps
    (`clsF` for its class), the next block's back link, and `fin`: release the lock and
    return — all of it `relMem`, in the code's order.
-/

import Cases.Zip2005.Runtime.Alloc.Exec
import Cases.Zip2005.Runtime.Tlsf.Free

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Dealloc

open RiscvZkvm.Rv64
open AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check AsmVerif.RiscV.Exec
  Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7801c620.base, prog := F_7801c620.prog }

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 43) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn] at h)

/-- `dealloc`'s frame: the 32 bytes below the entry stack pointer. -/
def InFrame (sp a : Word) : Prop := sp.toNat - 0x20 ≤ a.toNat ∧ a.toNat < sp.toNat

/-- The callee-saved registers `dealloc` does not save. -/
def untouched : List Reg :=
  [.x3, .x4, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- Inside `dealloc`, after its prologue: the frame holds the saved registers, `s0` the heap,
    and memory off the frame is `M`. -/
structure St (s0 : MachineState) (M : Word → Word) (y : MachineState) : Prop where
  code0 : s0.code = C
  code : y.code = C
  sp : y.getReg .x2 = s0.getReg .x2 + 0xffffffffffffffe0#64
  self : y.getReg .x8 = s0.getReg .x10
  regs : ∀ r ∈ untouched, y.getReg r = s0.getReg r
  fra : y.getMem (s0.getReg .x2 + 0xfffffffffffffff8#64) = s0.getReg .x1
  fs0 : y.getMem (s0.getReg .x2 + 0xfffffffffffffff0#64) = s0.getReg .x8
  fs1 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe8#64) = s0.getReg .x9
  fs2 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe0#64) = s0.getReg .x18
  mem : ∀ a, ¬ InFrame (s0.getReg .x2) a → y.getMem a = M a

/-- What the caller gets back: `ret` to `ra`, the callee-saved registers and the code as they
    were, and memory off the frame `M'`. -/
structure Out (s0 : MachineState) (M' : Word → Word) (t : MachineState) : Prop where
  pc : t.pc = s0.getReg .x1 &&& ~~~1#64
  saved : ∀ q ∈ savedRegs, t.getReg q = s0.getReg q
  code : t.code = s0.code
  mem : ∀ a, ¬ InFrame (s0.getReg .x2) a → t.getMem a = M' a

theorem off_eq_iff (x c d : Word) : (x + c = x + d) ↔ c = d := by
  constructor
  · intro h; bv_omega
  · rintro rfl; rfl

theorem slot_ne {sp a c : Word} (ha : ¬ InFrame sp a) (hsp : 0x20 ≤ sp.toNat)
    (hc : 2 ^ 64 - 0x20 ≤ c.toNat) : sp + c ≠ a := by
  intro h
  apply ha
  subst h
  have := c.isLt
  unfold InFrame
  rw [BitVec.toNat_add]
  omega

theorem off_frame {sp a : Word} (h : sp.toNat ≤ a.toNat) : ¬ InFrame sp a := fun h' => by
  unfold InFrame at h'; omega

namespace St

variable {s0 y : MachineState} {M : Word → Word}

theorem setPC (h : St s0 M y) (v : Word) : St s0 M (y.setPC v) :=
  ⟨h.code0, by simp [h.code], by simp [h.sp], by simp [h.self],
    fun r hr => by simp [h.regs r hr], by simp [h.fra], by simp [h.fs0], by simp [h.fs1],
    by simp [h.fs2], fun a ha => by simp [h.mem a ha]⟩

theorem setReg (h : St s0 M y) {r : Reg} (hr : r ∉ untouched) (h2 : r ≠ .x2) (h8 : r ≠ .x8)
    (v : Word) : St s0 M (y.setReg r v) := by
  refine ⟨h.code0, by simp [h.code], ?_, ?_, fun r' hr' => ?_, by simp [h.fra],
    by simp [h.fs0], by simp [h.fs1], by simp [h.fs2], fun a ha => by simp [h.mem a ha]⟩
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h2]; exact h.sp
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h8]; exact h.self
  · have : r ≠ r' := fun e => hr (e ▸ hr')
    rw [MachineState.getReg_setReg_ne _ _ _ _ this]; exact h.regs r' hr'

/-- A store off the frame. -/
theorem setMem (h : St s0 M y) {k : Word} (hk : ¬ InFrame (s0.getReg .x2) k)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (v : Word) : St s0 (Tlsf.upd M k v) (y.setMem k v) := by
  have hne : ∀ c : Word, 2 ^ 64 - 0x20 ≤ c.toNat → s0.getReg .x2 + c ≠ k :=
    fun c hc => slot_ne hk hsp hc
  refine ⟨h.code0, by simp [h.code], by simp [getReg_setMem, h.sp], by simp [getReg_setMem, h.self],
    fun r hr => by simp [getReg_setMem, h.regs r hr], ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fra
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs0
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs1
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs2
  · rw [getMem_setMem]
    by_cases e : a = k
    · rw [if_pos e, e, Tlsf.upd_same]
    · rw [if_neg e, Tlsf.upd_ne e]; exact h.mem a ha

end St

/-- `St` through register writes and `pc` updates, down to a hypothesis. -/
macro "dst" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine St.setPC ?_ _ |
    with_reducible refine St.setReg ?_ (by decide) (by decide) (by decide) _))

/-- The same, through stores off the frame (`hsp` in scope). -/
macro "dstm" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine St.setPC ?_ _ |
    with_reducible refine St.setReg ?_ (by decide) (by decide) (by decide) _ |
    (refine St.setMem ?_ (by assumption) (by assumption) _)))

/-- Where the freed block's header is: below the pointer, or, for a large alignment, at the
    address stored just below it. -/
def blkOf (M : Word → Word) (ptr align : Word) : Word :=
  if align ≤ 31#64 then ptr + 0xfffffffffffffff0#64 else M (ptr + 0xfffffffffffffff8#64)

/-- The prologue and the lock, `0x7801c620`–`0x7801c668`: save the registers, take the lock,
    and find the block. -/
theorem entry {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 : MachineState}
    (hpc : s0.pc = 0x7801c620#64) (hcode : s0.code = C)
    (hlock : s0.getMem (s0.getReg .x10) = 0#64)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hself : ¬ InFrame (s0.getReg .x2) (s0.getReg .x10))
    (hpoff : ¬ s0.getReg .x12 ≤ 31#64 →
      ¬ InFrame (s0.getReg .x2) (s0.getReg .x11 + 0xfffffffffffffff8#64))
    (hk : ∀ y, St s0 (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) y →
      y.pc = 0x7801c66c#64 →
      y.getReg .x9 = blkOf (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64)
        (s0.getReg .x11) (s0.getReg .x12) → SafeN G n P y) :
    SafeN G n P s0 := by
  have rest : ∀ y, St s0 s0.getMem y → y.pc = 0x7801c648#64 → y.getReg .x9 = s0.getReg .x11 →
      y.getReg .x18 = s0.getReg .x12 → SafeN G n P y := by
    intro y hs hpcy r9 r18
    have hcy := hs.code
    rw [← setPC_self hpcy]
    xstep code
    simp only [MachineState.getMem_setPC, hs.self, hs.mem _ hself, hlock]
    xstep code
    · exfalso; simp at hb
    iterate 3 xstep code
    simp only [hs.self]
    have hs1 := St.setMem hs hself hsp 0xffffffffffffffff#64
    xstep code
    · xstep code
      refine hk _ (by dstm) rfl ?_
      xregs
      rw [r18] at hb
      have hb' : s0.getReg .x12 ≤ 31#64 := by simpa [BitVec.ult_iff_lt, BitVec.not_lt] using hb
      unfold blkOf; rw [if_pos hb', r9]
    · iterate 2 xstep code
      refine hk _ (by dstm) rfl ?_
      xregs
      rw [r18] at hb
      have hb' : ¬ s0.getReg .x12 ≤ 31#64 := by simpa [BitVec.ult_iff_lt, BitVec.not_le] using hb
      unfold blkOf; rw [if_neg hb', r9]
      simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem]
      unfold Tlsf.upd
      split
      · rfl
      · exact hs.mem _ (hpoff hb')
  rw [← setPC_self hpc]
  iterate 10 xstep code
  xstep Entry.dumpF_code
  refine rest _ ?_ rfl (by xregs) (by xregs)
  xag
  have hn : ∀ c : Word, 2 ^ 64 - 0x20 ≤ c.toNat → ∀ a, ¬ InFrame (s0.getReg .x2) a →
      a ≠ s0.getReg .x2 + c := fun c hc a ha e => slot_ne ha hsp hc e.symm
  refine ⟨hcode, by simp [hcode], by xregs, by xregs, fun r hr => ?_, ?_, ?_, ?_, ?_,
    fun a ha => ?_⟩
  · simp only [untouched, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> xregs
  all_goals simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
    off_eq_iff, BitVec.reduceEq, if_true, if_false]
  simp only [hn 0xfffffffffffffff8#64 (by decide) a ha, hn 0xfffffffffffffff0#64 (by decide) a ha,
    hn 0xffffffffffffffe8#64 (by decide) a ha, hn 0xffffffffffffffe0#64 (by decide) a ha, if_false]

/-- The next block's class, `0x7801c6b0`–`0x7801c780`: registers only. -/
theorem clsN {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {R : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c6b0#64)
    (r13 : y.getReg .x13 = R) (hR : R ≠ 0#64)
    (hk : ∀ y', St s0 M y' → y'.pc = 0x7801c784#64 → y'.getReg .x14 = Tlsf.flOf R →
      y'.getReg .x13 = Tlsf.slOf R → (∀ q ∈ [Reg.x9, .x10, .x11, .x12], y'.getReg q = y.getReg q) →
      SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  xstep code
  · exfalso; rw [r13] at hb; exact hR (by simpa using hb)
  iterate 51 xstep code
  refine hk _ ?_ rfl ?_ ?_ ?_
  · dst
  · xregs
    simp only [r13, Tlsf.flOf, Tlsf.clz]
    xag
    bv_decide
  · xregs
    simp only [r13, Alloc.shr_mod, Alloc.shl_mod', Tlsf.slOf, Tlsf.rotr, Tlsf.subw, Tlsf.clz]
    xag
    bv_decide
  · intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> xregs

/-- The list's head moves on to `nx`; if the list empties, its bit clears, and the class's if
    that empties: `unlinkMem` with no predecessor. -/
def popTail (self : Word) (m : Word → Word) (f s nx : Word) : Word → Word :=
  let m2 := Tlsf.upd m (Tlsf.headAddr self f s) nx
  if nx = 0#64 then
    let t := m2 (Tlsf.slBm self f) &&& ~~~(1#64 <<< s.toNat)
    let m3 := Tlsf.upd m2 (Tlsf.slBm self f) t
    if t = 0#64 then
      Tlsf.upd m3 (Tlsf.flBm self) (m3 (Tlsf.flBm self) &&& ~~~(1#64 <<< f.toNat))
    else m3
  else m2

theorem unlinkMem_eq (self : Word) (m : Word → Word) (f s x : Word) :
    Tlsf.unlinkMem self m f s x =
      let nx := m (x + 0x10#64)
      let pv := m (x + 0x18#64)
      let m1 := if nx = 0#64 then m else Tlsf.upd m (nx + 0x18#64) pv
      if pv = 0#64 then popTail self m1 f s nx else Tlsf.upd m1 (pv + 0x10#64) nx := rfl

/-- The control block's doublewords are off the frame. -/
theorem offC {sp self k : Word} (h : sp.toNat ≤ self.toNat) (hk : Tlsf.InCtl self k) :
    ¬ InFrame sp k := off_frame (by have := hk.1; omega)

/-- The list update after the next block's class, `0x7801c784`–`0x7801c7dc`. -/
theorem headN {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {f s nx : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c784#64)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (hc : Tlsf.CtlOk (s0.getReg .x10)) (hf : f < 64#64) (hs' : s < 64#64)
    (r14 : y.getReg .x14 = f) (r13 : y.getReg .x13 = s) (r12 : y.getReg .x12 = nx)
    (hk : ∀ y', St s0 (popTail (s0.getReg .x10) M f s nx) y' → y'.pc = 0x7801c7e0#64 →
      (∀ q ∈ [Reg.x9, .x10, .x11], y'.getReg q = y.getReg q) → SafeN G n P y') :
    SafeN G n P y := by
  have hcode := hs.code
  have hH := offC hspc (Tlsf.headAddr_inCtl hc hf hs')
  have hSL := offC hspc (Tlsf.slBm_inCtl hc hf)
  have hFL := offC hspc (Tlsf.flBm_inCtl hc)
  have dSL : Tlsf.slBm (s0.getReg .x10) f ≠ Tlsf.headAddr (s0.getReg .x10) f s :=
    fun e => Tlsf.headAddr_ne_slBm hf hs' hf e.symm
  have dFL : Tlsf.flBm (s0.getReg .x10) ≠ Tlsf.slBm (s0.getReg .x10) f :=
    fun e => Tlsf.slBm_ne_flBm hf e.symm
  have dFH : Tlsf.flBm (s0.getReg .x10) ≠ Tlsf.headAddr (s0.getReg .x10) f s :=
    fun e => Tlsf.headAddr_ne_flBm hf hs' e.symm
  rw [← setPC_self hpc]
  iterate 5 xstep code
  simp only [r14, r13, r12, hs.self]
  xag0
  simp only [Alloc.head_addr2]
  have hs1 := St.setMem hs hH hsp nx
  xstep code
  · -- The list keeps a node.
    have hz : nx ≠ 0#64 := by simpa [r12] using hb
    have e : popTail (s0.getReg .x10) M f s nx =
        Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) f s) nx := by
      unfold popTail; simp only [if_neg hz]
    refine hk _ ?_ rfl ?_
    · rw [e]
      refine St.setPC ?_ _
      refine St.setMem ?_ hH hsp _
      dst
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> xregs
  have hz : nx = 0#64 := by simpa [r12] using hb
  subst hz
  iterate 10 xstep code
  simp only [hs.self, r13, r14]
  xag0
  simp only [Alloc.sl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
    getMem_setMem, if_neg dSL, hs.mem _ hSL, Alloc.shl_mod hs', Alloc.xor_ones]
  generalize ht : M (Tlsf.slBm (s0.getReg .x10) f) &&& ~~~(1#64 <<< s.toNat) = t
  xstep code
  · -- The class keeps a list.
    have h0 : ¬ t = 0#64 := by simpa using hb
    have e : popTail (s0.getReg .x10) M f s 0#64 =
        Tlsf.upd (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) f s) 0#64)
          (Tlsf.slBm (s0.getReg .x10) f) t := by
      unfold popTail; simp only [if_true, Tlsf.upd_ne dSL, ht, if_neg h0]
    refine hk _ ?_ rfl ?_
    · rw [e]
      refine St.setPC ?_ _
      refine St.setMem ?_ hSL hsp _
      dst
      refine St.setMem ?_ hH hsp _
      dst
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> xregs
  · -- The class empties too.
    have h0 : t = 0#64 := by simpa using hb
    iterate 6 xstep code
    simp only [hs.self, r14]
    xag0
    simp only [Alloc.fl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
      getMem_setMem, if_neg dFL, if_neg dFH, hs.mem _ hFL, Alloc.shl_mod hf, Alloc.xor_ones]
    have e : popTail (s0.getReg .x10) M f s 0#64 =
        Tlsf.upd (Tlsf.upd (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) f s) 0#64)
          (Tlsf.slBm (s0.getReg .x10) f) t) (Tlsf.flBm (s0.getReg .x10))
          (M (Tlsf.flBm (s0.getReg .x10)) &&& ~~~(1#64 <<< f.toNat)) := by
      unfold popTail
      simp only [if_true, Tlsf.upd_ne dSL, ht, h0, Tlsf.upd_ne dFL, Tlsf.upd_ne dFH]
    refine hk _ ?_ rfl ?_
    · rw [e]
      refine St.setPC ?_ _
      refine St.setMem ?_ hFL hsp _
      dst
      refine St.setMem ?_ hSL hsp _
      dst
      refine St.setMem ?_ hH hsp _
      dst
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> xregs

theorem hdr_used_and {sz : Word} {l : Bool} (h : sz &&& 31#64 = 0#64) :
    (Tlsf.Blk.hdr ⟨0, sz, true, l⟩) &&& 1#64 ≠ 0#64 := by
  unfold Tlsf.Blk.hdr
  have : ∀ sz c : BitVec 64, sz &&& 31#64 = 0#64 → (c = 0#64 ∨ c = 2#64) →
      (sz ||| 1#64 ||| c) &&& 1#64 ≠ 0#64 := by intro sz c; bv_decide
  exact this sz _ h (by cases l <;> simp)

theorem hdr_used_sz {sz : Word} (h : sz &&& 31#64 = 0#64) :
    (sz ||| 1#64 ||| 0#64) &&& 0xffffffffffffffe0#64 = sz ∧
      (sz ||| 1#64 ||| 0#64) &&& 0xfffffffffffffffe#64 = sz := by
  have : ∀ sz : BitVec 64, sz &&& 31#64 = 0#64 →
      (sz ||| 1#64 ||| 0#64) &&& 0xffffffffffffffe0#64 = sz ∧
      (sz ||| 1#64 ||| 0#64) &&& 0xfffffffffffffffe#64 = sz := by intro sz; bv_decide
  exact this sz h

theorem hdr_free_sz {sz : Word} (h : sz &&& 31#64 = 0#64) :
    (sz ||| 0#64 ||| 0#64) = sz ∧ sz &&& 1#64 = 0#64 ∧ sz &&& 0xffffffffffffffe0#64 = sz := by
  have : ∀ sz : BitVec 64, sz &&& 31#64 = 0#64 →
      (sz ||| 0#64 ||| 0#64) = sz ∧ sz &&& 1#64 = 0#64 ∧ sz &&& 0xffffffffffffffe0#64 = sz := by
    intro sz; bv_decide
  exact this sz h

/-- Off the frame: anything at or past the heap. -/
theorem offN {sp self a : Word} (h : sp.toNat ≤ self.toNat) (ha : self.toNat ≤ a.toNat) :
    ¬ InFrame sp a := off_frame (by omega)

/-- The next block, `0x7801c66c`–`0x7801c7dc`: if it is free, it leaves its list. -/
theorem nextSeg {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {pre post : List Tlsf.Blk} {b q : Tlsf.Blk}
    (hs : St s0 M y) (hpc : y.pc = 0x7801c66c#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M bs L (fun _ => False))
    (hbs : bs = pre ++ b :: q :: post) (hbu : b.used = true) (hbl : b.last = false)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (r9 : y.getReg .x9 = b.a)
    (hk : ∀ y' M', St s0 M' y' → y'.pc = 0x7801c7e0#64 → y'.getReg .x9 = b.a →
      (q.used = true ∧ M' = M ∧ y'.getReg .x10 = q.a ∧ y'.getReg .x11 = b.sz) ∨
      (q.used = false ∧ M' = Tlsf.unlinkMem (s0.getReg .x10) M (Tlsf.flOf q.sz) (Tlsf.slOf q.sz) q.a ∧
        y'.getReg .x10 = q.a + q.sz ∧ y'.getReg .x11 = b.sz + q.sz) → SafeN G n P y') :
    SafeN G n P y := by
  have hcode := hs.code
  have hc := hsh.ctlOk
  have hlay := hsh.layout.1
  simp only [Tlsf.ctlSize] at hlay
  have hbm : b ∈ bs := by rw [hbs]; simp
  have hqm : q ∈ bs := by rw [hbs]; simp
  -- The chain at `b` and `q`.
  have hch := hsh.chain
  rw [hbs] at hch
  obtain ⟨a', p', -, hcb⟩ := (Tlsf.chain_append (List.cons_ne_nil _ _)).mp hch
  obtain ⟨hb1, hb2, -, hb4, -, hb6⟩ := hcb
  rw [if_neg (by simp [hbl])] at hb6
  obtain ⟨hq1, hq2, -, hq4, -, hq6⟩ := hb6
  subst hb1
  have hbA := hsh.blkA hbm
  have hqA := hsh.blkA hqm
  have offB := offN hspc (a := b.a) (by omega)
  have offQ := offN hspc (a := q.a) (by omega)
  have hbh : b.hdr = b.sz ||| 1#64 ||| 0#64 := by simp [Tlsf.Blk.hdr, hbu, hbl]
  obtain ⟨e32, e2⟩ := hdr_used_sz hb4
  rw [← hq1] at hq2
  -- The next block's header decides.
  have hqu' : q.used = true ↔ M q.a &&& 1#64 ≠ 0#64 := by
    rw [hq2]
    constructor
    · intro hu; exact hdr_used_and (l := q.last) hq4 |> fun h => by simpa [Tlsf.Blk.hdr, hu] using h
    · intro h
      cases hu : q.used
      · exfalso
        have hql : q.last = false := by
          cases hl : q.last
          · rfl
          · have := hsh.chain.last_used q hqm hl; rw [hu] at this; exact absurd this (by simp)
        simp only [Tlsf.Blk.hdr, hu, hql, Bool.false_eq_true, if_false] at h
        rw [(hdr_free_sz hq4).1] at h
        exact h (hdr_free_sz hq4).2.1
      · rfl
  rw [← setPC_self hpc]
  iterate 4 xstep code
  simp only [r9, MachineState.getMem_setReg, MachineState.getMem_setPC, hs.mem _ offB, hb2, hbh,
    e32, ← hq1, hs.mem _ offQ]
  iterate 2 xstep code
  simp only [e2]
  xstep code
  · -- `q` is used.
    have hqu : q.used = true := hqu'.mpr (by simpa using hb)
    exact hk _ M (by dst) rfl (by xregs; try exact r9) (.inl ⟨hqu, rfl, by xregs, by xregs⟩)
  -- `q` is free: unlink it.
  have hqu : q.used = false := by
    cases hu : q.used
    · rfl
    · exact absurd (hqu'.mp hu) (by simpa using hb)
  have hql : q.last = false := by
    cases hl : q.last
    · rfl
    · have := hsh.chain.last_used q hqm hl; rw [hqu] at this; exact absurd this (by simp)
  obtain ⟨-, -, hq32⟩ := hdr_free_sz hq4
  have hqhdr : q.hdr = q.sz := by simp [Tlsf.Blk.hdr, hqu, hql]
  rw [hqhdr] at hq2
  -- Its list and neighbours.
  have hsz := (hsh.blk hqm).2.2.2.2
  have hf := Tlsf.flOf_lt hsz
  have hsl := Tlsf.slOf_lt q.sz
  have hqL : q.a ∈ L (Tlsf.flOf q.sz) (Tlsf.slOf q.sz) := hsh.filed q hqm hqu id
  obtain ⟨l1, l2, hL⟩ := List.append_of_mem hqL
  have hdll := hsh.links (Tlsf.flOf q.sz) (Tlsf.slOf q.sz)
  rw [hL] at hdll
  obtain ⟨h18, h10⟩ := Tlsf.Dll.mid hdll
  have h18' : M (q.a + 0x18#64) = l1.getLast?.getD 0#64 := h18
  have h10' : M (q.a + 0x10#64) = l2.headD 0#64 := h10
  generalize hnf : l2.headD 0#64 = nf at h10'
  generalize hpf : l1.getLast?.getD 0#64 = pf at h18'
  have hnfL : nf ≠ 0#64 → nf ∈ L (Tlsf.flOf q.sz) (Tlsf.slOf q.sz) := fun hz => by
    cases l2 with
    | nil => exact (hz hnf.symm).elim
    | cons z zs => rw [hL, ← hnf]; simp
  have hpfL : pf ≠ 0#64 → pf ∈ L (Tlsf.flOf q.sz) (Tlsf.slOf q.sz) := fun hz => by
    rcases List.eq_nil_or_concat l1 with rfl | ⟨l1', z, rfl⟩
    · exact (hz hpf.symm).elim
    · rw [hL, ← hpf]; simp
  have offNode : ∀ z c, z ∈ L (Tlsf.flOf q.sz) (Tlsf.slOf q.sz) → c.toNat < 32 →
      ¬ InFrame (s0.getReg .x2) (z + c) := fun z c hz hc' => by
    have := hsh.nodeA hz
    exact offN hspc (by rw [BitVec.toNat_add]; omega)
  have offQ16 := offN hspc (a := q.a + 0x10#64) (by rw [BitVec.toNat_add]; simp; omega)
  have offQ24 := offN hspc (a := q.a + 0x18#64) (by rw [BitVec.toNat_add]; simp; omega)
  -- After the successor's back link, at `0x7801c69c`.
  have mid : ∀ y1, St s0 (if nf = 0#64 then M else Tlsf.upd M (nf + 0x18#64) pf) y1 →
      y1.pc = 0x7801c69c#64 → y1.getReg .x9 = b.a → y1.getReg .x10 = q.a →
      y1.getReg .x11 = b.sz → y1.getReg .x12 = nf → y1.getReg .x13 = q.sz →
      y1.getReg .x14 = pf → y1.getReg .x15 = q.sz → SafeN G n P y1 := by
    intro y1 hs1 hpc1 q9 q10 q11 q12 q13 q14 q15
    have hcode1 := hs1.code
    rw [← setPC_self hpc1]
    iterate 2 xstep code
    simp only [q10, q11, q13, q15]
    xstep code
    · -- No predecessor: the head moves on.
      have hp0 : pf = 0#64 := by simpa [q14] using hb
      refine clsN (s0 := s0) (M := if nf = 0#64 then M else Tlsf.upd M (nf + 0x18#64) pf)
        (R := q.sz) ?_ rfl (by xregs; try exact q13)
        (fun e => by have := Tlsf.Shape.sz_ge hsz; rw [e] at this; simp at this) ?_
      · refine St.setPC ?_ _; dst
      intro y2 hs2 hpc2 r14 r13 hregs
      refine headN (nx := nf) hs2 hpc2 hsp hspc hc hf hsl r14 r13 (by rw [hregs .x12 (by simp)]; xregs; try exact q12) ?_
      intro y3 hs3 hpc3 hregs3
      refine hk _ _ hs3 hpc3 ?_ (.inr ⟨hqu, ?_, ?_, ?_⟩)
      · rw [hregs3 .x9 (by simp), hregs .x9 (by simp)]; xregs; exact q9
      · rw [unlinkMem_eq]; simp only [h10', h18', hp0, if_true]
      · rw [hregs3 .x10 (by simp), hregs .x10 (by simp)]; xregs
      · rw [hregs3 .x11 (by simp), hregs .x11 (by simp)]; xregs
    · -- The predecessor forwards past `q`.
      have hp0 : pf ≠ 0#64 := by simpa [q14] using hb
      have offP := offNode pf 0x10#64 (hpfL hp0) (by decide)
      iterate 2 xstep code
      simp only [q12, q14]
      refine hk _ (Tlsf.upd (if nf = 0#64 then M else Tlsf.upd M (nf + 0x18#64) pf) (pf + 0x10#64) nf)
        ?_ rfl ?_ (.inr ⟨hqu, ?_, ?_, ?_⟩)
      · refine St.setPC ?_ _
        refine St.setMem ?_ offP hsp _
        dst
      · xregs; exact q9
      · rw [unlinkMem_eq]; simp only [h10', h18', if_neg hp0]
      · xregs
      · xregs
  iterate 3 xstep code
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, hs.mem _ offQ16,
    hs.mem _ offQ24, h10', h18', hq2, hq32]
  xstep code
  · have hz : nf = 0#64 := by simpa using hb
    refine mid _ ?_ rfl (by xregs; try exact r9) (by xregs) (by xregs) (by xregs; try exact hz.symm)
      (by xregs) (by xregs) (by xregs)
    rw [if_pos hz]; dst
  · have hz : nf ≠ 0#64 := by simpa using hb
    xstep code
    refine mid _ ?_ rfl (by xregs; try exact r9) (by xregs) (by xregs) (by xregs) (by xregs) (by xregs)
      (by xregs)
    rw [if_neg hz]
    refine St.setPC ?_ _
    refine St.setMem ?_ (offNode nf 0x18#64 (hnfL hz) (by decide)) hsp _
    dst

/-- The previous block's class, `0x7801c97c`–`0x7801ca4c`: registers only. -/
theorem clsP {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {R : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c97c#64)
    (r14 : y.getReg .x14 = R) (hR : R ≠ 0#64)
    (hk : ∀ y', St s0 M y' → y'.pc = 0x7801ca50#64 → y'.getReg .x15 = Tlsf.flOf R →
      y'.getReg .x14 = Tlsf.slOf R → (∀ q ∈ [Reg.x9, .x10, .x11, .x12, .x13], y'.getReg q = y.getReg q) →
      SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  xstep code
  · exfalso; rw [r14] at hb; exact hR (by simpa using hb)
  iterate 51 xstep code
  refine hk _ ?_ rfl ?_ ?_ ?_
  · dst
  · xregs
    simp only [r14, Tlsf.flOf, Tlsf.clz]
    xag
    bv_decide
  · xregs
    simp only [r14, Alloc.shr_mod, Alloc.shl_mod', Tlsf.slOf, Tlsf.rotr, Tlsf.subw, Tlsf.clz]
    xag
    bv_decide
  · intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> xregs

/-- The list update after the previous block's class, `0x7801ca50`–`0x7801caac`. -/
theorem headP {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {f s nx : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801ca50#64)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (hc : Tlsf.CtlOk (s0.getReg .x10)) (hf : f < 64#64) (hs' : s < 64#64)
    (r15 : y.getReg .x15 = f) (r14 : y.getReg .x14 = s) (r13 : y.getReg .x13 = nx)
    (hk : ∀ y', St s0 (popTail (s0.getReg .x10) M f s nx) y' → y'.pc = 0x7801c818#64 →
      (∀ q ∈ [Reg.x9, .x10, .x11, .x12], y'.getReg q = y.getReg q) → SafeN G n P y') :
    SafeN G n P y := by
  have hcode := hs.code
  have hH := offC hspc (Tlsf.headAddr_inCtl hc hf hs')
  have hSL := offC hspc (Tlsf.slBm_inCtl hc hf)
  have hFL := offC hspc (Tlsf.flBm_inCtl hc)
  have dSL : Tlsf.slBm (s0.getReg .x10) f ≠ Tlsf.headAddr (s0.getReg .x10) f s :=
    fun e => Tlsf.headAddr_ne_slBm hf hs' hf e.symm
  have dFL : Tlsf.flBm (s0.getReg .x10) ≠ Tlsf.slBm (s0.getReg .x10) f :=
    fun e => Tlsf.slBm_ne_flBm hf e.symm
  have dFH : Tlsf.flBm (s0.getReg .x10) ≠ Tlsf.headAddr (s0.getReg .x10) f s :=
    fun e => Tlsf.headAddr_ne_flBm hf hs' e.symm
  rw [← setPC_self hpc]
  iterate 5 xstep code
  simp only [r15, r14, r13, hs.self]
  xag0
  simp only [Alloc.head_addr2]
  have hs1 := St.setMem hs hH hsp nx
  xstep code
  · -- The list keeps a node.
    have hz : nx ≠ 0#64 := by simpa [r13] using hb
    have e : popTail (s0.getReg .x10) M f s nx =
        Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) f s) nx := by
      unfold popTail; simp only [if_neg hz]
    refine hk _ ?_ rfl ?_
    · rw [e]
      refine St.setPC ?_ _
      refine St.setMem ?_ hH hsp _
      dst
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> xregs
  have hz : nx = 0#64 := by simpa [r13] using hb
  subst hz
  iterate 10 xstep code
  simp only [hs.self, r14, r15]
  xag0
  simp only [Alloc.sl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
    getMem_setMem, if_neg dSL, hs.mem _ hSL, Alloc.shl_mod hs', Alloc.xor_ones]
  generalize ht : M (Tlsf.slBm (s0.getReg .x10) f) &&& ~~~(1#64 <<< s.toNat) = t
  xstep code
  · -- The class keeps a list.
    have h0 : ¬ t = 0#64 := by simpa using hb
    have e : popTail (s0.getReg .x10) M f s 0#64 =
        Tlsf.upd (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) f s) 0#64)
          (Tlsf.slBm (s0.getReg .x10) f) t := by
      unfold popTail; simp only [if_true, Tlsf.upd_ne dSL, ht, if_neg h0]
    refine hk _ ?_ rfl ?_
    · rw [e]
      refine St.setPC ?_ _
      refine St.setMem ?_ hSL hsp _
      dst
      refine St.setMem ?_ hH hsp _
      dst
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> xregs
  · -- The class empties too.
    have h0 : t = 0#64 := by simpa using hb
    iterate 7 xstep code
    simp only [hs.self, r15]
    xag0
    simp only [Alloc.fl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
      getMem_setMem, if_neg dFL, if_neg dFH, hs.mem _ hFL, Alloc.shl_mod hf, Alloc.xor_ones]
    have e : popTail (s0.getReg .x10) M f s 0#64 =
        Tlsf.upd (Tlsf.upd (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) f s) 0#64)
          (Tlsf.slBm (s0.getReg .x10) f) t) (Tlsf.flBm (s0.getReg .x10))
          (M (Tlsf.flBm (s0.getReg .x10)) &&& ~~~(1#64 <<< f.toNat)) := by
      unfold popTail
      simp only [if_true, Tlsf.upd_ne dSL, ht, h0, Tlsf.upd_ne dFL, Tlsf.upd_ne dFH]
    refine hk _ ?_ rfl ?_
    · rw [e]
      refine St.setPC ?_ _
      refine St.setMem ?_ hFL hsp _
      dst
      refine St.setMem ?_ hSL hsp _
      dst
      refine St.setMem ?_ hH hsp _
      dst
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> xregs

/-- A segment's last block is what the next one points back to, and ends where it begins. -/
theorem seg_last {m : Word → Word} {c : Tlsf.Blk} :
    ∀ {l : List Tlsf.Blk} {a p a' p' : Word}, Tlsf.Seg m a p (l ++ [c]) a' p' →
      p' = c.a ∧ a' = c.a + c.sz ∧ m c.a = c.hdr ∧ c.last = false
  | [], _, _, _, _, ⟨h1, h2, _, _, _, h6, h7⟩ => by
    obtain ⟨e1, e2⟩ := h7
    subst h1
    exact ⟨e2.symm, e1.symm, h2, h6⟩
  | _ :: l, _, _, _, _, ⟨_, _, _, _, _, _, h7⟩ => seg_last (l := l) h7

/-- The previous block, `0x7801c7e0`–`0x7801c814`: if it is free, it leaves its list and
    becomes the start of the merged block. -/
theorem prevSeg {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {out : Word → Prop} {pre post : List Tlsf.Blk} {b : Tlsf.Blk}
    (hs : St s0 M y) (hpc : y.pc = 0x7801c7e0#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M bs L out)
    (hbs : bs = pre ++ b :: post) (hpo : ∀ c ∈ pre, ¬ out c.a)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (r9 : y.getReg .x9 = b.a)
    (hk : ∀ y' M' t S', St s0 M' y' → y'.pc = 0x7801c818#64 → y'.getReg .x12 = t →
      y'.getReg .x10 = y.getReg .x10 → y'.getReg .x11 = S' →
      (M' = M ∧ t = b.a ∧ S' = y.getReg .x11 ∧ ∀ pre' p, pre = pre' ++ [p] → p.used = true) ∨
      (∃ pre' p, pre = pre' ++ [p] ∧ p.used = false ∧
        M' = Tlsf.unlinkMem (s0.getReg .x10) M (Tlsf.flOf p.sz) (Tlsf.slOf p.sz) p.a ∧
        t = p.a ∧ S' = p.sz + y.getReg .x11) → SafeN G n P y') :
    SafeN G n P y := by
  have hcode := hs.code
  have hc := hsh.ctlOk
  have hlay := hsh.layout.1
  simp only [Tlsf.ctlSize] at hlay
  have hbm : b ∈ bs := by rw [hbs]; simp
  have hbA := hsh.blkA hbm
  have hch := hsh.chain
  rw [hbs] at hch
  obtain ⟨a', p', hseg, hcb⟩ := (Tlsf.chain_append (List.cons_ne_nil _ _)).mp hch
  obtain ⟨hb1, -, hb3, -⟩ := hcb
  subst hb1
  have offB8 := offN hspc (a := b.a + 8#64) (by rw [BitVec.toNat_add]; simp; omega)
  -- No predecessor, or a used one: the merged block starts at `b`.
  have keep : ∀ y1, St s0 M y1 → y1.pc = 0x7801c814#64 → y1.getReg .x9 = b.a →
      y1.getReg .x10 = y.getReg .x10 → y1.getReg .x11 = y.getReg .x11 →
      (∀ pre' p, pre = pre' ++ [p] → p.used = true) → SafeN G n P y1 := by
    intro y1 hs1 hpc1 q9 q10 q11 hu
    have hcode1 := hs1.code
    rw [← setPC_self hpc1]
    xstep code
    exact hk _ M b.a _ (by dst) rfl (by xregs; try exact q9) (by xregs; try exact q10)
      (by xregs; try exact q11) (.inl ⟨rfl, rfl, rfl, hu⟩)
  rw [← setPC_self hpc]
  xstep code
  simp only [r9, MachineState.getMem_setPC, hs.mem _ offB8, hb3]
  xstep code
  · -- No predecessor.
    have hp0 : p' = 0#64 := by simpa using hb
    refine keep _ (by dst) rfl (by xregs; try exact r9) (by xregs) (by xregs) ?_
    intro pre' p hpre
    subst hpre
    obtain ⟨e, -⟩ := seg_last hseg
    have hpm : p ∈ bs := by rw [hbs]; simp
    have := (hsh.blkA hpm).2.1
    rw [e] at hp0; rw [hp0] at this; simp at this; omega
  have hp0 : p' ≠ 0#64 := by simpa using hb
  -- There is a predecessor `p`.
  rcases List.eq_nil_or_concat pre with rfl | ⟨pre', p, rfl⟩
  · exact absurd hseg.2.symm hp0
  simp only [List.concat_eq_append] at hseg hbs hpo hk
  obtain ⟨e1, e2, hpH, hpl⟩ := seg_last hseg
  subst e1
  have hpm : p ∈ bs := by rw [hbs]; simp
  have hpA := hsh.blkA hpm
  have offP := offN hspc (a := p.a) (by omega)
  obtain ⟨-, -, -, hp4, hsz⟩ := hsh.blk hpm
  have hpu' : p.used = true ↔ p.hdr &&& 1#64 ≠ 0#64 := by
    constructor
    · intro hu; simpa [Tlsf.Blk.hdr, hu] using hdr_used_and (l := p.last) hp4
    · intro h
      cases hu : p.used
      · exfalso
        simp only [Tlsf.Blk.hdr, hu, hpl, Bool.false_eq_true, if_false] at h
        rw [(hdr_free_sz hp4).1] at h
        exact h (hdr_free_sz hp4).2.1
      · rfl
  iterate 2 xstep code
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, hs.mem _ offP, hpH]
  xstep code
  · -- A used predecessor.
    refine keep _ (by dst) rfl (by xregs; try exact r9) (by xregs) (by xregs) ?_
    intro pre'' p'' he
    rw [List.concat_eq_append] at he
    have h2 := (List.append_inj' he rfl).2
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    exact hpu'.mpr (by simpa using hb)
  -- A free predecessor: unlink it.
  have hpu : p.used = false := by
    cases hu : p.used
    · rfl
    · exact absurd (hpu'.mp hu) (by simpa using hb)
  have hphdr : p.hdr = p.sz := by
    simp [Tlsf.Blk.hdr, hpu, hpl]
  rw [hphdr]
  have hf := Tlsf.flOf_lt hsz
  have hsl := Tlsf.slOf_lt p.sz
  have hpL : p.a ∈ L (Tlsf.flOf p.sz) (Tlsf.slOf p.sz) :=
    hsh.filed p hpm hpu (hpo p (by simp))
  obtain ⟨l1, l2, hL⟩ := List.append_of_mem hpL
  have hdll := hsh.links (Tlsf.flOf p.sz) (Tlsf.slOf p.sz)
  rw [hL] at hdll
  obtain ⟨h18, h10⟩ := Tlsf.Dll.mid hdll
  have h18' : M (p.a + 0x18#64) = l1.getLast?.getD 0#64 := h18
  have h10' : M (p.a + 0x10#64) = l2.headD 0#64 := h10
  generalize hnf : l2.headD 0#64 = nf at h10'
  generalize hpf : l1.getLast?.getD 0#64 = pf at h18'
  have hnfL : nf ≠ 0#64 → nf ∈ L (Tlsf.flOf p.sz) (Tlsf.slOf p.sz) := fun hz => by
    cases l2 with
    | nil => exact (hz hnf.symm).elim
    | cons z zs => rw [hL, ← hnf]; simp
  have hpfL : pf ≠ 0#64 → pf ∈ L (Tlsf.flOf p.sz) (Tlsf.slOf p.sz) := fun hz => by
    rcases List.eq_nil_or_concat l1 with rfl | ⟨l1', z, rfl⟩
    · exact (hz hpf.symm).elim
    · rw [hL, ← hpf]; simp
  have offNode : ∀ z c, z ∈ L (Tlsf.flOf p.sz) (Tlsf.slOf p.sz) → c.toNat < 32 →
      ¬ InFrame (s0.getReg .x2) (z + c) := fun z c hz hc' => by
    have := hsh.nodeA hz
    exact offN hspc (by rw [BitVec.toNat_add]; omega)
  have offP16 := offN hspc (a := p.a + 0x10#64) (by rw [BitVec.toNat_add]; simp; omega)
  have offP24 := offN hspc (a := p.a + 0x18#64) (by rw [BitVec.toNat_add]; simp; omega)
  have hres : ∀ M', M' = Tlsf.unlinkMem (s0.getReg .x10) M (Tlsf.flOf p.sz) (Tlsf.slOf p.sz) p.a →
      ∃ pre'' p'', pre' ++ [p] = pre'' ++ [p''] ∧ p''.used = false ∧
        M' = Tlsf.unlinkMem (s0.getReg .x10) M (Tlsf.flOf p''.sz) (Tlsf.slOf p''.sz) p''.a ∧
        p.a = p''.a ∧ p.sz + y.getReg .x11 = p''.sz + y.getReg .x11 :=
    fun M' hM' => ⟨pre', p, rfl, hpu, hM', rfl, rfl⟩
  -- After the successor's back link, at `0x7801c804`.
  have mid : ∀ y1, St s0 (if nf = 0#64 then M else Tlsf.upd M (nf + 0x18#64) pf) y1 →
      y1.pc = 0x7801c804#64 → y1.getReg .x10 = y.getReg .x10 → y1.getReg .x11 = y.getReg .x11 →
      y1.getReg .x12 = p.a → y1.getReg .x13 = nf → y1.getReg .x14 = p.sz →
      y1.getReg .x15 = pf → SafeN G n P y1 := by
    intro y1 hs1 hpc1 q10 q11 q12 q13 q14 q15
    have hcode1 := hs1.code
    rw [← setPC_self hpc1]
    xstep code
    simp only [q11, q14]
    xstep code
    · -- No predecessor in the list: the head moves on.
      have hp0 : pf = 0#64 := by simpa [q15] using hb
      refine clsP (s0 := s0) (M := if nf = 0#64 then M else Tlsf.upd M (nf + 0x18#64) pf)
        (R := p.sz) ?_ rfl (by xregs; try exact q14)
        (fun e => by have := Tlsf.Shape.sz_ge hsz; rw [e] at this; simp at this) ?_
      · refine St.setPC ?_ _; dst
      intro y2 hs2 hpc2 r15 r14 hregs
      refine headP (nx := nf) hs2 hpc2 hsp hspc hc hf hsl r15 r14
        (by rw [hregs .x13 (by simp)]; xregs; try exact q13) ?_
      intro y3 hs3 hpc3 hregs3
      obtain ⟨pre'', p'', h1, h2, h3, h4, h5⟩ := hres
        (popTail (s0.getReg .x10) (if nf = 0#64 then M else Tlsf.upd M (nf + 0x18#64) pf)
          (Tlsf.flOf p.sz) (Tlsf.slOf p.sz) nf) (by
        rw [unlinkMem_eq]; simp only [h10', h18', hp0, if_true])
      refine hk _ _ p.a (p.sz + y.getReg .x11) hs3 hpc3 ?_ ?_ ?_ (.inr ⟨pre'', p'', h1, h2, h3, h4, h5⟩)
      · rw [hregs3 .x12 (by simp), hregs .x12 (by simp)]; xregs; try exact q12
      · rw [hregs3 .x10 (by simp), hregs .x10 (by simp)]; xregs; try exact q10
      · rw [hregs3 .x11 (by simp), hregs .x11 (by simp)]; xregs
    · -- The list predecessor forwards past `p`.
      have hp0 : pf ≠ 0#64 := by simpa [q15] using hb
      have offPf := offNode pf 0x10#64 (hpfL hp0) (by decide)
      iterate 2 xstep code
      simp only [q13, q15]
      obtain ⟨pre'', p'', h1, h2, h3, h4, h5⟩ := hres
        (Tlsf.upd (if nf = 0#64 then M else Tlsf.upd M (nf + 0x18#64) pf) (pf + 0x10#64) nf) (by
        rw [unlinkMem_eq]; simp only [h10', h18', if_neg hp0])
      refine hk _ _ p.a (p.sz + y.getReg .x11) ?_ rfl ?_ ?_ ?_
        (.inr ⟨pre'', p'', h1, h2, h3, h4, h5⟩)
      · refine St.setPC ?_ _
        refine St.setMem ?_ offPf hsp _
        dst
      · xregs; try exact q12
      · xregs; try exact q10
      · xregs
  iterate 2 xstep code
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, hs.mem _ offP16,
    hs.mem _ offP24, h10', h18']
  xstep code
  · have hz : nf = 0#64 := by simpa using hb
    refine mid _ ?_ rfl (by xregs) (by xregs) (by xregs) (by xregs; try exact hz.symm)
      (by xregs) (by xregs)
    rw [if_pos hz]; dst
  · have hz : nf ≠ 0#64 := by simpa using hb
    xstep code
    refine mid _ ?_ rfl (by xregs) (by xregs) (by xregs) (by xregs) (by xregs) (by xregs)
    rw [if_neg hz]
    refine St.setPC ?_ _
    refine St.setMem ?_ (offNode nf 0x18#64 (hnfL hz) (by decide)) hsp _
    dst

/-- The merged block's class, `0x7801c81c`–`0x7801c8ec`: registers only. -/
theorem clsF {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {R : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c81c#64)
    (r11 : y.getReg .x11 = R) (hR : R ≠ 0#64)
    (hk : ∀ y', St s0 M y' → y'.pc = 0x7801c8f0#64 → y'.getReg .x13 = Tlsf.flOf R →
      y'.getReg .x11 = Tlsf.slOf R → (∀ q ∈ [Reg.x10, .x12], y'.getReg q = y.getReg q) →
      SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  xstep code
  · exfalso; rw [r11] at hb; exact hR (by simpa using hb)
  iterate 51 xstep code
  refine hk _ ?_ rfl ?_ ?_ ?_
  · dst
  · xregs
    simp only [r11, Tlsf.flOf, Tlsf.clz]
    xag
    bv_decide
  · xregs
    simp only [r11, Alloc.shr_mod, Alloc.shl_mod', Tlsf.slOf, Tlsf.rotr, Tlsf.subw, Tlsf.clz]
    xag
    bv_decide
  · intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl <;> xregs

/-- Memory after the merged block at `t` (size `S`, ending at `e`) is filed: its header, the
    head of its list and its links, the old head's back link, the bitmaps, the next block's
    back link and the lock's release. In the code's order. -/
def relMem (self : Word) (m : Word → Word) (t S e : Word) : Word → Word :=
  let f := Tlsf.flOf S
  let s := Tlsf.slOf S
  let m1 := Tlsf.upd m t S
  let h := m1 (Tlsf.headAddr self f s)
  let m2 := Tlsf.upd (Tlsf.upd (Tlsf.upd m1 (Tlsf.headAddr self f s) t) (t + 0x10#64) h)
    (t + 0x18#64) 0#64
  let m3 := if h = 0#64 then m2 else Tlsf.upd m2 (h + 0x18#64) t
  let m4 := Tlsf.upd m3 (Tlsf.flBm self) (m3 (Tlsf.flBm self) ||| 1#64 <<< f.toNat)
  let v := m4 (Tlsf.slBm self f)
  let m5 := Tlsf.upd m4 (e + 8#64) t
  Tlsf.upd (Tlsf.upd m5 (Tlsf.slBm self f) (v ||| 1#64 <<< s.toNat)) self (m5 self + 1#64)

/-- `relMem` in stages: after the header and the list links, the class bit, and the next
    block's back link. -/
def rel3 (self : Word) (m : Word → Word) (t S : Word) : Word → Word :=
  let f := Tlsf.flOf S
  let s := Tlsf.slOf S
  let m1 := Tlsf.upd m t S
  let h := m1 (Tlsf.headAddr self f s)
  let m2 := Tlsf.upd (Tlsf.upd (Tlsf.upd m1 (Tlsf.headAddr self f s) t) (t + 0x10#64) h)
    (t + 0x18#64) 0#64
  if h = 0#64 then m2 else Tlsf.upd m2 (h + 0x18#64) t

def rel4 (self : Word) (m : Word → Word) (t S : Word) : Word → Word :=
  Tlsf.upd (rel3 self m t S) (Tlsf.flBm self)
    (rel3 self m t S (Tlsf.flBm self) ||| 1#64 <<< (Tlsf.flOf S).toNat)

def rel5 (self : Word) (m : Word → Word) (t S e : Word) : Word → Word :=
  Tlsf.upd (rel4 self m t S) (e + 8#64) t

theorem relMem_eq (self : Word) (m : Word → Word) (t S e : Word) :
    relMem self m t S e =
      Tlsf.upd (Tlsf.upd (rel5 self m t S e) (Tlsf.slBm self (Tlsf.flOf S))
        (rel4 self m t S (Tlsf.slBm self (Tlsf.flOf S)) ||| 1#64 <<< (Tlsf.slOf S).toNat))
        self (rel5 self m t S e self + 1#64) := rfl

/-- The release, `0x7801c948` on: the second-level bit, the lock, and the return. -/
theorem fin {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {v f s : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c948#64)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (hc : Tlsf.CtlOk (s0.getReg .x10)) (hf : f < 64#64) (hs' : s < 64#64)
    (r11 : y.getReg .x11 = s) (r13 : y.getReg .x13 = s0.getReg .x10 + 0x8000#64 + f <<< 3)
    (r14 : y.getReg .x14 = v) (r17 : y.getReg .x17 = 1#64)
    (hk : ∀ t, Out s0 (Tlsf.upd (Tlsf.upd M (Tlsf.slBm (s0.getReg .x10) f) (v ||| 1#64 <<< s.toNat))
      (s0.getReg .x10) (M (s0.getReg .x10) + 1#64)) t → SafeN G n P t) : SafeN G n P y := by
  have hcode := hs.code
  have hself := offN (a := s0.getReg .x10) hspc (Nat.le_refl _)
  have hSL := offC hspc (Tlsf.slBm_inCtl hc hf)
  have dS : s0.getReg .x10 ≠ Tlsf.slBm (s0.getReg .x10) f := by
    have := Tlsf.slBm_inCtl hc hf; intro e; rw [← e] at this; have := this.1; omega
  rw [← setPC_self hpc]
  iterate 6 xstep code
  simp only [hs.self, r11, r13, r14, r17, MachineState.getMem_setPC, hs.mem _ hself]
  xag0
  simp only [Alloc.sl_addr2, Alloc.shl_mod hs']
  iterate 7 xstep code
  xstep Entry.dumpF_code
  have hn : ∀ c : Word, 2 ^ 64 - 0x20 ≤ c.toNat → ∀ a, ¬ InFrame (s0.getReg .x2) a →
      a ≠ s0.getReg .x2 + c := fun c hc' a ha e => slot_ne ha hsp hc' e.symm
  have n1 := hn 0xfffffffffffffff8#64 (by decide) _ hself
  have n2 := hn 0xfffffffffffffff0#64 (by decide) _ hself
  have n3 := hn 0xffffffffffffffe8#64 (by decide) _ hself
  have n4 := hn 0xffffffffffffffe0#64 (by decide) _ hself
  have m1 := hn 0xfffffffffffffff8#64 (by decide) _ hSL
  have m2 := hn 0xfffffffffffffff0#64 (by decide) _ hSL
  have m3 := hn 0xffffffffffffffe8#64 (by decide) _ hSL
  have m4 := hn 0xffffffffffffffe0#64 (by decide) _ hSL
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, hs.sp]
  xa
  simp only [getMem_setMem, MachineState.getMem_setReg, Ne.symm n1,
    Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm m1, Ne.symm m2, Ne.symm m3, Ne.symm m4, if_false,
    hs.fra, hs.fs0, hs.fs1, hs.fs2]
  apply hk
  refine ⟨by simp, fun q hq => ?_, by simpa using hs.code.trans hs.code0.symm, fun a ha => ?_⟩
  · simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> xregs <;> first | rfl | (rw [hs.sp]; bv_omega) |
        (refine hs.regs _ ?_; simp [untouched])
  · simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem]
    unfold Tlsf.upd
    by_cases e1 : a = s0.getReg .x10
    · rw [if_pos e1, if_pos e1]
    · rw [if_neg e1, if_neg e1]
      by_cases e2 : a = Tlsf.slBm (s0.getReg .x10) f
      · rw [if_pos e2, if_pos e2]
      · rw [if_neg e2, if_neg e2]; exact hs.mem a ha

/-- Filing the merged block, `0x7801c818`–`0x7801c944`, then `fin`. -/
theorem relSeg {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {t S e : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c818#64)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (hc : Tlsf.CtlOk (s0.getReg .x10)) (hS : S ≠ 0#64) (hf : Tlsf.flOf S < 64#64)
    (r10 : y.getReg .x10 = e) (r11 : y.getReg .x11 = S) (r12 : y.getReg .x12 = t)
    (offT : ∀ c : Word, c.toNat < 32 → ¬ InFrame (s0.getReg .x2) (t + c))
    (offE : ¬ InFrame (s0.getReg .x2) (e + 8#64))
    (offH : Tlsf.upd M t S (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf S) (Tlsf.slOf S)) ≠ 0#64 →
      ¬ InFrame (s0.getReg .x2)
        (Tlsf.upd M t S (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf S) (Tlsf.slOf S)) + 0x18#64))
    (hk : ∀ t', Out s0 (relMem (s0.getReg .x10) M t S e) t' → SafeN G n P t') :
    SafeN G n P y := by
  have hcode := hs.code
  have hsl := Tlsf.slOf_lt S
  have offT0 : ¬ InFrame (s0.getReg .x2) t := by simpa using offT 0#64 (by decide)
  have offHd := offC hspc (Tlsf.headAddr_inCtl hc hf hsl)
  have hSL := offC hspc (Tlsf.slBm_inCtl hc hf)
  have hFL := offC hspc (Tlsf.flBm_inCtl hc)
  -- After the bitmaps' first level, at `0x7801c934`.
  have c4 : ∀ y4, St s0 (rel4 (s0.getReg .x10) M t S) y4 → y4.pc = 0x7801c934#64 →
      y4.getReg .x10 = e → y4.getReg .x11 = Tlsf.slOf S → y4.getReg .x12 = t →
      y4.getReg .x13 = Tlsf.flOf S → y4.getReg .x14 = 0x8000#64 → y4.getReg .x17 = 1#64 →
      SafeN G n P y4 := by
    intro y4 hs4 hpc4 q10 q11 q12 q13 q14 q17
    have hcode4 := hs4.code
    rw [← setPC_self hpc4]
    iterate 5 xstep code
    simp only [hs4.self, q10, q12, q13, q14]
    xag0
    simp only [Alloc.sl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
      hs4.mem _ hSL]
    refine fin (M := rel5 (s0.getReg .x10) M t S e) (f := Tlsf.flOf S) ?_ rfl hsp hspc hc hf hsl
      (by xregs; try exact q11) (by xregs; try rfl) (by xregs; try rfl) (by xregs; try exact q17) ?_
    · refine St.setPC ?_ _
      refine St.setMem ?_ offE hsp _
      dst
    · intro t' ht'
      exact hk t' (by rw [relMem_eq]; exact ht')
  -- After the list links, at `0x7801c918`.
  have c3 : ∀ y3, St s0 (rel3 (s0.getReg .x10) M t S) y3 → y3.pc = 0x7801c918#64 →
      y3.getReg .x10 = e → y3.getReg .x11 = Tlsf.slOf S → y3.getReg .x12 = t →
      y3.getReg .x13 = Tlsf.flOf S → SafeN G n P y3 := by
    intro y3 hs3 hpc3 q10 q11 q12 q13
    have hcode3 := hs3.code
    rw [← setPC_self hpc3]
    iterate 7 xstep code
    simp only [hs3.self, q13]
    xag0
    simp only [Alloc.fl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
      hs3.mem _ hFL, Alloc.shl_mod hf]
    refine c4 _ ?_ rfl (by xregs; try exact q10) (by xregs; try exact q11)
      (by xregs; try exact q12) (by xregs; try exact q13) (by xregs) (by xregs)
    refine St.setPC ?_ _
    refine St.setMem ?_ hFL hsp _
    dst
  rw [← setPC_self hpc]
  xstep code
  simp only [r11, r12]
  refine clsF (s0 := s0) (M := Tlsf.upd M t S) (R := S) ?_ rfl (by xregs; try exact r11) hS ?_
  · refine St.setPC ?_ _
    refine St.setMem ?_ offT0 hsp _
    dst
  intro y2 hs2 hpc2 q13 q11 hregs
  have q10 : y2.getReg .x10 = e := by rw [hregs .x10 (by simp)]; xregs; try exact r10
  have q12 : y2.getReg .x12 = t := by rw [hregs .x12 (by simp)]; xregs; try exact r12
  have hcode2 := hs2.code
  rw [← setPC_self hpc2]
  iterate 5 xstep code
  simp only [hs2.self, q13, q11]
  xag0
  simp only [Alloc.head_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
    hs2.mem _ offHd]
  iterate 3 xstep code
  simp only [q12, Alloc.head_addr2]
  generalize hh : Tlsf.upd M t S (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf S) (Tlsf.slOf S)) = h
    at offH
  have e3 : rel3 (s0.getReg .x10) M t S =
      if h = 0#64 then Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd M t S)
        (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf S) (Tlsf.slOf S)) t) (t + 0x10#64) h)
        (t + 0x18#64) 0#64
      else Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd M t S)
        (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf S) (Tlsf.slOf S)) t) (t + 0x10#64) h)
        (t + 0x18#64) 0#64) (h + 0x18#64) t := by
    unfold rel3; simp only [hh]
  xstep code
  · have hz : h = 0#64 := by simpa using hb
    refine c3 _ ?_ rfl (by xregs; try exact q10) (by xregs; try exact q11) (by xregs; try exact q12)
      (by xregs; try exact q13)
    rw [e3, if_pos hz]
    refine St.setPC ?_ _
    refine St.setMem ?_ (offT _ (by decide)) hsp _
    refine St.setMem ?_ (offT _ (by decide)) hsp _
    refine St.setMem ?_ offHd hsp _
    dst
  · have hz : h ≠ 0#64 := by simpa using hb
    xstep code
    simp only [q12]
    refine c3 _ ?_ rfl (by xregs; try exact q10) (by xregs; try exact q11) (by xregs; try exact q12)
      (by xregs; try exact q13)
    rw [e3, if_neg hz]
    refine St.setPC ?_ _
    refine St.setMem ?_ (offH hz) hsp _
    refine St.setMem ?_ (offT _ (by decide)) hsp _
    refine St.setMem ?_ (offT _ (by decide)) hsp _
    refine St.setMem ?_ offHd hsp _
    dst

end Cases.Zip2005.Runtime.Dealloc
