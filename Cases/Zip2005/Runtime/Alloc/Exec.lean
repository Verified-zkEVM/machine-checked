/-
  Cases.Zip2005.Runtime.Alloc.Exec

  rlsf's `alloc` (`GlobalAlloc::alloc` for the TLSF heap, `0x7801c18c`), run by the symbolic
  executor from the found block to the return (phase D4).

  `St` is what holds inside `alloc` after its prologue: the frame holds the saved registers,
  `s0`–`s2` the arguments (heap, alignment, size), and memory off the frame is a model `M`.
  Each segment below takes `St` with the `M` its stores built and hands on `St` with the next;
  the heap lemmas (`Tlsf.Shape.pop`, `mark`, `split`) speak about those `M`s.

  * `found` (`0x7801c378`): unlink the head `x` of list `(fl, sl)` — `Tlsf.popMem`.
  * `tail` (`0x7801c444`): place the pointer (`ptrOf`), size the block (`needOf`), then
    `fin` directly when it fits exactly, or `splitPath` first: the next block's back link,
    the remainder's header and links, its list (`classes`: the code's class arithmetic is
    `flOf`/`slOf`) and bitmaps (`bitmaps`) — `splitPre`.
  * `fin` (`0x7801c5a8`): the header, the back pointer for large alignments, then `exit`:
    release the lock and return the pointer.
-/

import MachineChecked.RiscV.Exec.Tactic
import MachineChecked.RiscV.Check.Image
import Cases.Zip2005.Runtime.Entry
import Cases.Zip2005.Runtime.Tlsf.Update

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Alloc

open RiscvZkvm.Rv64
open MachineChecked.RiscV MachineChecked.RiscV.Frame MachineChecked.RiscV.Check MachineChecked.RiscV.Exec
  Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7801c18c.base, prog := F_7801c18c.prog }

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 42) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn] at h)

/-- `alloc`'s frame: the 48 bytes below the entry stack pointer. -/
def InFrame (sp a : Word) : Prop := sp.toNat - 0x30 ≤ a.toNat ∧ a.toNat < sp.toNat

/-- The callee-saved registers `alloc` does not save. -/
def untouched : List Reg := [.x3, .x4, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- Inside `alloc`, after its prologue: the frame holds the saved registers, `s0`–`s2` the
    arguments, and memory off the frame is `M`. -/
structure St (s0 : MachineState) (M : Word → Word) (y : MachineState) : Prop where
  code0 : s0.code = C
  code : y.code = C
  sp : y.getReg .x2 = s0.getReg .x2 + 0xffffffffffffffd0#64
  self : y.getReg .x8 = s0.getReg .x10
  align : y.getReg .x9 = s0.getReg .x11
  size : y.getReg .x18 = s0.getReg .x12
  regs : ∀ r ∈ untouched, y.getReg r = s0.getReg r
  fra : y.getMem (s0.getReg .x2 + 0xfffffffffffffff8#64) = s0.getReg .x1
  fs0 : y.getMem (s0.getReg .x2 + 0xfffffffffffffff0#64) = s0.getReg .x8
  fs1 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe8#64) = s0.getReg .x9
  fs2 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe0#64) = s0.getReg .x18
  fs3 : y.getMem (s0.getReg .x2 + 0xffffffffffffffd8#64) = s0.getReg .x19
  mem : ∀ a, ¬ InFrame (s0.getReg .x2) a → y.getMem a = M a
  priv : y.privateInput = s0.privateInput

/-- What the caller gets back: `ret` to `ra`, the callee-saved registers and the code as they
    were, and memory off the frame `M'`, with the result in `a0`. -/
structure Out (s0 : MachineState) (M' : Word → Word) (r : Word) (t : MachineState) : Prop where
  pc : t.pc = s0.getReg .x1 &&& ~~~1#64
  saved : ∀ q ∈ savedRegs, t.getReg q = s0.getReg q
  code : t.code = s0.code
  mem : ∀ a, ¬ InFrame (s0.getReg .x2) a → t.getMem a = M' a
  res : t.getReg .x10 = r
  priv : t.privateInput = s0.privateInput

/-- Fold literal offsets on a symbolic base. -/
macro "xa" : tactic => `(tactic| (
  try simp only [BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceNeg,
    signExtend12, BitVec.reduceSignExtend, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft,
    BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceNot, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceHShiftRight] at *))

/-- The same, on the goal only. -/
macro "xag" : tactic => `(tactic| (
  try simp only [BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceNeg,
    signExtend12, BitVec.reduceSignExtend, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft,
    BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceNot, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceHShiftRight]))

/-- Fold literals without reassociating sums. -/
macro "xag0" : tactic => `(tactic| (
  try simp only [BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceNeg,
    signExtend12, BitVec.reduceSignExtend, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft,
    BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceNot, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceHShiftRight]))

/-- A frame slot is not an address off the frame. -/
theorem slot_ne {sp a c : Word} (ha : ¬ InFrame sp a) (hsp : 0x30 ≤ sp.toNat)
    (hc : 2 ^ 64 - 0x30 ≤ c.toNat) : sp + c ≠ a := by
  intro h
  apply ha
  subst h
  have := c.isLt
  unfold InFrame
  rw [BitVec.toNat_add]
  omega

/-- The exit at `0x7801c2ec`: release the lock (add one), return `s3`. -/
theorem exit {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c2ec#64)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat)
    (hself : ¬ InFrame (s0.getReg .x2) (s0.getReg .x10))
    (hk : ∀ t, Out s0 (Tlsf.upd M (s0.getReg .x10) (M (s0.getReg .x10) + 1)) (y.getReg .x19) t →
      SafeN G n P t) : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  iterate 5 xstep code
  xstep Entry.dumpF_code
  iterate 8 xstep code
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, hs.sp, hs.self]
  xa
  have hne : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → s0.getReg .x2 + c ≠ s0.getReg .x10 :=
    fun c hc => slot_ne hself hsp hc
  have n1 := hne 0xfffffffffffffff8#64 (by decide)
  have n2 := hne 0xfffffffffffffff0#64 (by decide)
  have n3 := hne 0xffffffffffffffe8#64 (by decide)
  have n4 := hne 0xffffffffffffffe0#64 (by decide)
  have n5 := hne 0xffffffffffffffd8#64 (by decide)
  simp only [MachineState.getMem_setReg, getMem_setMem, n1, n2, n3,
    n4, n5, if_false, hs.fra, hs.fs0, hs.fs1, hs.fs2, hs.fs3]
  apply hk
  refine ⟨by simp, fun q hq => ?_, by simpa using hs.code.trans hs.code0.symm, fun a ha => ?_, ?_,
    by simp [hs.priv]⟩
  · simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> xregs <;> first | rfl | (rw [hs.sp]; bv_omega) |
        (refine hs.regs _ ?_; simp [untouched])
  · simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem]
    by_cases he : a = s0.getReg .x10
    · rw [if_pos he, he, hs.mem _ hself, Tlsf.upd_same]; rfl
    · rw [if_neg he, hs.mem _ ha, Tlsf.upd_ne he]
  · xregs

namespace St

variable {s0 y : MachineState} {M : Word → Word}

theorem setPC (h : St s0 M y) (v : Word) : St s0 M (y.setPC v) :=
  ⟨h.code0, by simp [h.code], by simp [h.sp], by simp [h.self], by simp [h.align], by simp [h.size],
    fun r hr => by simp [h.regs r hr], by simp [h.fra], by simp [h.fs0], by simp [h.fs1],
    by simp [h.fs2], by simp [h.fs3], fun a ha => by simp [h.mem a ha], by simp [h.priv]⟩

theorem setReg (h : St s0 M y) {r : Reg} (hr : r ∉ untouched) (h2 : r ≠ .x2) (h8 : r ≠ .x8)
    (h9 : r ≠ .x9) (h18 : r ≠ .x18) (v : Word) : St s0 M (y.setReg r v) := by
  refine ⟨h.code0, by simp [h.code], ?_, ?_, ?_, ?_, fun r' hr' => ?_, by simp [h.fra],
    by simp [h.fs0], by simp [h.fs1], by simp [h.fs2], by simp [h.fs3],
    fun a ha => by simp [h.mem a ha], by simp [h.priv]⟩
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h2]; exact h.sp
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h8]; exact h.self
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h9]; exact h.align
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h18]; exact h.size
  · have : r ≠ r' := fun e => hr (e ▸ hr')
    rw [MachineState.getReg_setReg_ne _ _ _ _ this]; exact h.regs r' hr'

/-- A store off the frame. -/
theorem setMem (h : St s0 M y) {k : Word} (hk : ¬ InFrame (s0.getReg .x2) k)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat) (v : Word) : St s0 (Tlsf.upd M k v) (y.setMem k v) := by
  have hne : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → s0.getReg .x2 + c ≠ k :=
    fun c hc => slot_ne hk hsp hc
  refine ⟨h.code0, by simp [h.code], by simp [getReg_setMem, h.sp], by simp [getReg_setMem, h.self],
    by simp [getReg_setMem, h.align], by simp [getReg_setMem, h.size],
    fun r hr => by simp [getReg_setMem, h.regs r hr], ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, ?_⟩
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fra
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs0
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs1
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs2
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs3
  · rw [getMem_setMem]
    by_cases e : a = k
    · rw [if_pos e, e, Tlsf.upd_same]
    · rw [if_neg e, Tlsf.upd_ne e]; exact h.mem a ha
  · simp [h.priv]

end St

/-- `St` through register writes and `pc` updates, down to a hypothesis. -/
macro "xst" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine St.setPC ?_ _ |
    with_reducible refine St.setReg ?_ (by decide) (by decide) (by decide) (by decide) (by decide) _))

/-- Above the stack pointer is off the frame. -/
theorem off_frame {sp a : Word} (h : sp.toNat ≤ a.toNat) : ¬ InFrame sp a := fun h' => by
  unfold InFrame at h'; omega

theorem xor_ones (x : Word) : x ^^^ 0xffffffffffffffff#64 = ~~~x := by
  have : ∀ x : BitVec 64, x ^^^ 0xffffffffffffffff#64 = ~~~x := by intro x; bv_decide
  exact this x

theorem sl_addr (self fl : Word) :
    self + (0x8000#64 + (fl <<< 3 + 8#64)) = Tlsf.slBm self fl := by
  have : ∀ self fl : BitVec 64,
      self + (0x8000#64 + (fl <<< 3 + 8#64)) = self + 0x8008#64 + fl * 8#64 := by
    intro self fl; bv_decide
  exact this self fl

theorem shl_mod {s : Word} (h : s < 64#64) (x : Word) : x <<< (s.toNat % 64) = x <<< s.toNat := by
  rw [Nat.mod_eq_of_lt (Tlsf.lt64 h)]

theorem head_addr (self fl sl : Word) :
    self + (sl <<< 3 + (fl <<< 9 + 8#64)) = Tlsf.headAddr self fl sl := by
  have : ∀ self fl sl : BitVec 64,
      self + (sl <<< 3 + (fl <<< 9 + 8#64)) = self + 8#64 + fl * 0x200#64 + sl * 8#64 := by
    intro self fl sl; bv_decide
  exact this self fl sl

/-- The pop at `0x7801c378`: the head `x` of list `(fl, sl)` leaves it. -/
theorem found {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {fl sl x : Word} {xs : List Word}
    (hs : St s0 M y) (hpc : y.pc = 0x7801c378#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M bs L (fun _ => False))
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (h10 : y.getReg .x10 = s0.getReg .x10 + 0x8000#64) (h12 : y.getReg .x12 = fl)
    (h13 : y.getReg .x13 = sl) (hfl : fl < 64#64) (hsl : sl < 64#64) (hL : L fl sl = x :: xs)
    (hk : ∀ y', St s0 (Tlsf.popMem (s0.getReg .x10) M fl sl (xs.headD 0#64)) y' →
      y'.pc = 0x7801c444#64 → y'.getReg .x10 = s0.getReg .x10 + 0x8000#64 →
      y'.getReg .x11 = x → y'.getReg .x14 = M x → y'.getReg .x15 = x + 0x10#64 →
      SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  -- What the heap says about the list.
  have hx : x ∈ L fl sl := by rw [hL]; exact List.mem_cons_self ..
  have hH : M (Tlsf.headAddr (s0.getReg .x10) fl sl) = x := by
    rw [hsh.heads fl sl hfl hsl, hL]; rfl
  have hdll := hsh.links fl sl
  rw [hL] at hdll
  have hnx : M (x + 0x10#64) = xs.headD 0#64 := hdll.2.1
  have hc := hsh.ctlOk
  have hxA := hsh.nodeA hx
  have hlay := hsh.layout.1
  have offC : ∀ k, Tlsf.InCtl (s0.getReg .x10) k → ¬ InFrame (s0.getReg .x2) k :=
    fun k hk => off_frame (by have := hk.1; omega)
  have offA : ∀ z c : Word, (Tlsf.A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) → c < 32#64 →
      ¬ InFrame (s0.getReg .x2) (z + c) := fun z c hz hc' => off_frame (by
    rw [BitVec.lt_def] at hc'
    rw [BitVec.toNat_add]; simp only [Tlsf.ctlSize] at hlay; simp at hc'; omega)
  have offH := offC _ (Tlsf.headAddr_inCtl hc hfl hsl)
  have offx := offA x 0#64 hxA (by decide)
  simp only [BitVec.add_zero] at offx
  have offx16 := offA x 0x10#64 hxA (by decide)
  rw [← setPC_self hpc]
  iterate 8 xstep code
  simp only [h12, h13, hs.self]
  xag
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, head_addr]
  rw [hs.mem _ offH, hH, hs.mem _ offx16, hnx, hs.mem _ offx]
  generalize hnxe : xs.headD 0#64 = nx at hk
  -- After the head moves on, at `0x7801c39c`.
  have rest : ∀ y1, St s0 (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) fl sl) nx) y1 →
      y1.pc = 0x7801c39c#64 → y1.getReg .x16 = nx → y1.getReg .x10 = s0.getReg .x10 + 0x8000#64 →
      y1.getReg .x11 = x → y1.getReg .x12 = fl → y1.getReg .x13 = sl → y1.getReg .x14 = M x →
      y1.getReg .x15 = x + 0x10#64 → SafeN G n P y1 := by
    intro y1 hs1 hpc1 r16 r10 r11 r12 r13 r14 r15
    have hcode1 := hs1.code
    rw [← setPC_self hpc1]
    xstep code
    · -- The list empties: clear its bit, and the class's if that empties.
      rw [r16] at hb
      have hnx0 : nx = 0#64 := by simpa using hb
      subst hnx0
      have hSL := Tlsf.slBm_inCtl hc hfl
      have hFL := Tlsf.flBm_inCtl hc
      have dSL : Tlsf.slBm (s0.getReg .x10) fl ≠ Tlsf.headAddr (s0.getReg .x10) fl sl :=
        fun e => Tlsf.headAddr_ne_slBm hfl hsl hfl e.symm
      have dFL : Tlsf.flBm (s0.getReg .x10) ≠ Tlsf.slBm (s0.getReg .x10) fl :=
        fun e => Tlsf.slBm_ne_flBm hfl e.symm
      have dFH : Tlsf.flBm (s0.getReg .x10) ≠ Tlsf.headAddr (s0.getReg .x10) fl sl :=
        fun e => Tlsf.headAddr_ne_flBm hfl hsl e.symm
      iterate 8 xstep code
      simp only [r10, r12, r13]
      xag
      simp only [sl_addr, MachineState.getMem_setReg, MachineState.getMem_setPC,
        hs1.mem _ (offC _ hSL), Tlsf.upd_ne dSL, shl_mod hsl, xor_ones]
      generalize ht : M (Tlsf.slBm (s0.getReg .x10) fl) &&& ~~~(1#64 <<< sl.toNat) = t
      xstep code
      · -- The class still has a list.
        refine hk _ ?_ rfl ?_ ?_ ?_ ?_
        · have hpm : Tlsf.popMem (s0.getReg .x10) M fl sl 0#64 =
              Tlsf.upd (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) fl sl) 0#64)
                (Tlsf.slBm (s0.getReg .x10) fl) t := by
            have : ¬ t = 0#64 := by simpa using hb
            unfold Tlsf.popMem; simp only [if_true, ht, if_neg this]
          rw [hpm]
          refine St.setPC ?_ _
          refine St.setMem ?_ (offC _ hSL) hsp _
          xst
        all_goals xregs
        all_goals first | rfl | assumption
      · -- The class empties too.
        have ht0 : t = 0#64 := by simpa using hb
        iterate 7 xstep code
        simp only [hs1.self, r12]
        xag
        simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
          show (s0.getReg .x10 + 0x8208#64) = Tlsf.flBm (s0.getReg .x10) from rfl, if_neg dFL,
          hs1.mem _ (offC _ hFL), Tlsf.upd_ne dFH, shl_mod hfl, xor_ones]
        refine hk _ ?_ rfl ?_ ?_ ?_ ?_
        · have hpm : Tlsf.popMem (s0.getReg .x10) M fl sl 0#64 =
              Tlsf.upd (Tlsf.upd (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) fl sl) 0#64)
                (Tlsf.slBm (s0.getReg .x10) fl) t) (Tlsf.flBm (s0.getReg .x10))
                (M (Tlsf.flBm (s0.getReg .x10)) &&& ~~~(1#64 <<< fl.toNat)) := by
            unfold Tlsf.popMem; simp only [if_true, ht, ht0]
          rw [hpm]
          refine St.setPC ?_ _
          refine St.setMem ?_ (offC _ hFL) hsp _
          xst
          refine St.setMem ?_ (offC _ hSL) hsp _
          xst
        all_goals xregs
        all_goals first | rfl | assumption
    · -- The successor's back link clears.
      rw [r16] at hb
      have hnx0 : nx ≠ 0#64 := by simpa using hb
      have hnxL : nx ∈ L fl sl := by
        cases xs with
        | nil => exact (hnx0 hnxe.symm).elim
        | cons z zs =>
          simp only [List.headD] at hnxe
          rw [hL, ← hnxe]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      have off18 := offA nx 0x18#64 (hsh.nodeA hnxL) (by decide)
      iterate 2 xstep code
      simp only [r16]
      refine hk _ ?_ rfl ?_ ?_ ?_ ?_
      · have hpm : Tlsf.popMem (s0.getReg .x10) M fl sl nx =
            Tlsf.upd (Tlsf.upd M (Tlsf.headAddr (s0.getReg .x10) fl sl) nx) (nx + 0x18#64) 0#64 := by
          unfold Tlsf.popMem; rw [if_neg hnx0]
        rw [hpm]
        refine St.setPC ?_ _
        refine St.setMem ?_ off18 hsp _
        xst
      all_goals xregs
      all_goals first | rfl | assumption
  xstep code
  xag
  simp only [head_addr]
  refine rest _ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine St.setPC ?_ _
    refine St.setMem ?_ offH hsp _
    xst
  all_goals xregs
  all_goals first | rfl | assumption

/-- Memory after the header write, the back pointer (for large alignments) and the lock's
    release. -/
def finMem (self : Word) (M : Word → Word) (x N ptr align : Word) : Word → Word :=
  let M2 := Tlsf.upd M x (N + 1#64)
  let M3 := if align < 32#64 then M2 else Tlsf.upd M2 (ptr + 0xfffffffffffffff8#64) x
  Tlsf.upd M3 self (M3 self + 1#64)

/-- The tail at `0x7801c5a8`: mark the block used, store the back pointer, leave. -/
theorem fin {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {x N ptr : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c5a8#64)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat)
    (hself : ¬ InFrame (s0.getReg .x2) (s0.getReg .x10))
    (r11 : y.getReg .x11 = x) (r12 : y.getReg .x12 = N) (r19 : y.getReg .x19 = ptr)
    (offx : ¬ InFrame (s0.getReg .x2) x)
    (offp : 32#64 ≤ s0.getReg .x11 → ¬ InFrame (s0.getReg .x2) (ptr + 0xfffffffffffffff8#64))
    (hk : ∀ t, Out s0 (finMem (s0.getReg .x10) M x N ptr (s0.getReg .x11)) ptr t →
      SafeN G n P t) : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  iterate 3 xstep code
  simp only [r11, r12]
  xag
  xstep code
  · -- small alignment: straight out
    have ha : s0.getReg .x11 < 32#64 := by
      rw [hs.align] at hb; simpa [BitVec.ult_iff_lt] using hb
    refine exit (M := Tlsf.upd M x (N + 1#64)) ?_ rfl hsp hself ?_
    · refine St.setPC ?_ _
      refine St.setMem ?_ offx hsp _
      xst
    · intro t ht
      apply hk
      have : finMem (s0.getReg .x10) M x N ptr (s0.getReg .x11) =
          Tlsf.upd (Tlsf.upd M x (N + 1#64)) (s0.getReg .x10)
            (Tlsf.upd M x (N + 1#64) (s0.getReg .x10) + 1#64) := by
        unfold finMem; simp only [if_pos ha]
      rw [this]
      simp only [getReg_setReg, MachineState.getReg_setPC, getReg_setMem, reduceCtorEq, ne_eq,
        not_false_eq_true, and_true, if_false, r19] at ht
      exact ht
  · have ha : 32#64 ≤ s0.getReg .x11 := by
      rw [hs.align] at hb; simpa [BitVec.ult_iff_lt, BitVec.not_lt] using hb
    iterate 2 xstep code
    simp only [r19, r11]
    xag
    refine exit (M := Tlsf.upd (Tlsf.upd M x (N + 1#64)) (ptr + 0xfffffffffffffff8#64) x) ?_ rfl
      hsp hself ?_
    · refine St.setPC ?_ _
      refine St.setMem ?_ (offp ha) hsp _
      xst
      refine St.setMem ?_ offx hsp _
      xst
    · intro t ht
      apply hk
      have : ¬ s0.getReg .x11 < 32#64 := by simpa [BitVec.not_lt] using ha
      have e : finMem (s0.getReg .x10) M x N ptr (s0.getReg .x11) =
          Tlsf.upd (Tlsf.upd (Tlsf.upd M x (N + 1#64)) (ptr + 0xfffffffffffffff8#64) x)
            (s0.getReg .x10)
            (Tlsf.upd (Tlsf.upd M x (N + 1#64)) (ptr + 0xfffffffffffffff8#64) x (s0.getReg .x10) +
              1#64) := by
        unfold finMem; simp only [if_neg this]
      rw [e]
      simp only [getReg_setReg, MachineState.getReg_setPC, getReg_setMem, reduceCtorEq, ne_eq,
        not_false_eq_true, and_true, if_false, r19] at ht
      exact ht

/-- `splitMem` without its last write, `x`'s header: what the split path leaves. -/
def splitPre (self : Word) (m : Word → Word) (x S N : Word) : Word → Word :=
  let y := x + N
  let R := S - N
  let f2 := Tlsf.flOf R
  let s2 := Tlsf.slOf R
  let m := Tlsf.upd m (x + S + 8#64) y
  let h2 := m (Tlsf.headAddr self f2 s2)
  let m := Tlsf.upd m (Tlsf.headAddr self f2 s2) y
  let m := Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd m y R) (y + 8#64) x) (y + 0x10#64) h2)
    (y + 0x18#64) 0#64
  let m := if h2 = 0#64 then m else Tlsf.upd m (h2 + 0x18#64) y
  let m := Tlsf.upd m (Tlsf.flBm self) (m (Tlsf.flBm self) ||| 1#64 <<< f2.toNat)
  Tlsf.upd m (Tlsf.slBm self f2) (m (Tlsf.slBm self f2) ||| 1#64 <<< s2.toNat)

theorem splitMem_eq (self : Word) (m : Word → Word) (x S N : Word) :
    Tlsf.splitMem self m x S N = Tlsf.upd (splitPre self m x S N) x (N + 1#64) := rfl

theorem and_granule {S : Word} (h : S &&& 31#64 = 0#64) : S &&& 0xffffffffffffffe0#64 = S := by
  have : ∀ S : BitVec 64, S &&& 31#64 = 0#64 → S &&& 0xffffffffffffffe0#64 = S := by
    intro S h; bv_decide
  exact this S h

theorem head_addr' (self fl sl : Word) :
    self + (fl <<< 9 + (sl <<< 3 + 8#64)) = Tlsf.headAddr self fl sl := by
  have : ∀ self fl sl : BitVec 64,
      self + (fl <<< 9 + (sl <<< 3 + 8#64)) = self + 8#64 + fl * 0x200#64 + sl * 8#64 := by
    intro self fl sl; bv_decide
  exact this self fl sl

theorem head_addr2 (self fl sl : Word) :
    self + fl <<< 9 + sl <<< 3 + 8#64 = Tlsf.headAddr self fl sl := by
  have : ∀ self fl sl : BitVec 64,
      self + fl <<< 9 + sl <<< 3 + 8#64 = self + 8#64 + fl * 0x200#64 + sl * 8#64 := by
    intro self fl sl; bv_decide
  exact this self fl sl

theorem sl_addr2 (self fl : Word) :
    self + 0x8000#64 + fl <<< 3 + 8#64 = Tlsf.slBm self fl := by
  have : ∀ self fl : BitVec 64,
      self + 0x8000#64 + fl <<< 3 + 8#64 = self + 0x8008#64 + fl * 8#64 := by
    intro self fl; bv_decide
  exact this self fl

theorem fl_addr2 (self : Word) : self + 0x8000#64 + 0x208#64 = Tlsf.flBm self := by
  unfold Tlsf.flBm; bv_omega

theorem shr_mod (x y : Word) : x >>> (y.toNat % 64) = x >>> (y &&& 63#64) := by
  rw [BitVec.ushiftRight_eq']
  congr 1
  rw [BitVec.toNat_and, show (63#64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shl_mod' (x y : Word) : x <<< (y.toNat % 64) = x <<< (y &&& 63#64) := by
  rw [BitVec.shiftLeft_eq']
  congr 1
  rw [BitVec.toNat_and, show (63#64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The class arithmetic on the remainder, `0x7801c47c`–`0x7801c540`: nothing but registers.
    The code's `clz` and rotate are `flOf`/`slOf` (the remainder is not zero). -/
theorem classes {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {R : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c47c#64)
    (r14 : y.getReg .x14 = R)
    (hk : ∀ y', St s0 M y' → y'.pc = 0x7801c544#64 → y'.getReg .x15 = Tlsf.flOf R →
      y'.getReg .x16 = Tlsf.slOf R → (∀ q ∈ [Reg.x10, .x11, .x12, .x13, .x14, .x19],
        y'.getReg q = y.getReg q) → SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  iterate 50 xstep code
  refine hk _ ?_ rfl ?_ ?_ ?_
  · xst
  · xregs
    simp only [r14, Tlsf.flOf, Tlsf.clz]
    xag
    bv_decide
  · xregs
    simp only [r14, shr_mod, shl_mod', Tlsf.slOf, Tlsf.rotr, Tlsf.subw, Tlsf.clz]
    xag
    bv_decide
  · intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> xregs

/-- The remainder's bitmap bits, `0x7801c574`–`0x7801c5a4`. -/
theorem bitmaps {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {f2 s2 x N ptr : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c574#64)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat)
    (hFL : ¬ InFrame (s0.getReg .x2) (Tlsf.flBm (s0.getReg .x10)))
    (hSL : ¬ InFrame (s0.getReg .x2) (Tlsf.slBm (s0.getReg .x10) f2))
    (hne : Tlsf.slBm (s0.getReg .x10) f2 ≠ Tlsf.flBm (s0.getReg .x10))
    (hf2 : f2 < 64#64) (hs2 : s2 < 64#64)
    (r10 : y.getReg .x10 = s0.getReg .x10 + 0x8000#64) (r11 : y.getReg .x11 = x)
    (r12 : y.getReg .x12 = N) (r15 : y.getReg .x15 = f2) (r16 : y.getReg .x16 = s2)
    (r19 : y.getReg .x19 = ptr)
    (hk : ∀ y', St s0 (Tlsf.upd (Tlsf.upd M (Tlsf.flBm (s0.getReg .x10))
        (M (Tlsf.flBm (s0.getReg .x10)) ||| 1#64 <<< f2.toNat)) (Tlsf.slBm (s0.getReg .x10) f2)
        (M (Tlsf.slBm (s0.getReg .x10) f2) ||| 1#64 <<< s2.toNat)) y' →
      y'.pc = 0x7801c5a8#64 → y'.getReg .x11 = x → y'.getReg .x12 = N → y'.getReg .x19 = ptr →
      SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  iterate 13 xstep code
  simp only [r10, r15, r16, hs.self]
  xag0
  simp only [fl_addr2, sl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC,
    getMem_setMem, if_neg hne, hs.mem _ hFL, hs.mem _ hSL, shl_mod hf2, shl_mod hs2]
  refine hk _ ?_ rfl ?_ ?_ ?_
  · refine St.setPC ?_ _
    refine St.setMem ?_ hSL hsp _
    xst
    refine St.setMem ?_ hFL hsp _
    xst
  all_goals xregs
  all_goals assumption

/-- The split, `0x7801c468`–`0x7801c5a4`: the next block's back link, the remainder's
    header and links, its list and bitmaps. -/
theorem splitPath {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {pre post : List Tlsf.Blk} {x S N ptr : Word}
    (hs : St s0 M y) (hpc : y.pc = 0x7801c468#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M bs L (fun a => False ∨ a = x))
    (hbs : bs = pre ++ ⟨x, S, false, false⟩ :: post)
    (hN31 : N &&& 31#64 = 0#64) (hNS : N < S)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (r10 : y.getReg .x10 = s0.getReg .x10 + 0x8000#64) (r11 : y.getReg .x11 = x)
    (r12 : y.getReg .x12 = N) (r14 : y.getReg .x14 = S) (r19 : y.getReg .x19 = ptr)
    (hk : ∀ y', St s0 (splitPre (s0.getReg .x10) M x S N) y' → y'.pc = 0x7801c5a8#64 →
      y'.getReg .x11 = x → y'.getReg .x12 = N → y'.getReg .x19 = ptr → SafeN G n P y') :
    SafeN G n P y := by
  have hcode := hs.code
  have hb : (⟨x, S, false, false⟩ : Tlsf.Blk) ∈ bs := by
    rw [hbs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hbA := hsh.blkA hb
  obtain ⟨_, _, hxS, hS31, hSok⟩ := hsh.blk hb
  dsimp only at hxS hS31 hSok hbA
  obtain ⟨_, hRok⟩ := Tlsf.rem_ok hS31 hSok hN31 hNS
  have hf2 := Tlsf.flOf_lt hRok
  have hs2 := Tlsf.slOf_lt (S - N)
  have hc := hsh.ctlOk
  have hlay := hsh.layout.1
  simp only [Tlsf.ctlSize] at hlay
  have hN2 : N.toNat < S.toNat := by rw [BitVec.lt_def] at hNS; exact hNS
  have hR0 : S - N ≠ 0#64 := fun e => by
    have := Tlsf.Shape.sz_ge hRok; rw [e] at this; simp at this
  -- Everything written lies past the control block's start, so off the frame.
  have offN : ∀ a : Word, (s0.getReg .x10).toNat ≤ a.toNat → ¬ InFrame (s0.getReg .x2) a :=
    fun a h => off_frame (by omega)
  have offC : ∀ k, Tlsf.InCtl (s0.getReg .x10) k → ¬ InFrame (s0.getReg .x2) k :=
    fun k hk => offN k (by have := hk.1; omega)
  have offX : ∀ c : Word, c.toNat < 2 ^ 41 → ¬ InFrame (s0.getReg .x2) (x + c) :=
    fun c hc1 => offN _ (by rw [BitVec.toNat_add]; have := hbA.2.1; have := hbA.2.2; omega)
  have hxS8 : ¬ InFrame (s0.getReg .x2) (x + S + 8#64) := by
    rw [BitVec.add_assoc]; exact offX _ (by rw [BitVec.toNat_add]; simp; omega)
  have hxN : ∀ c : Word, c.toNat < 32 → ¬ InFrame (s0.getReg .x2) (x + N + c) := fun c hc' => by
    rw [BitVec.add_assoc]; exact offX _ (by rw [BitVec.toNat_add]; omega)
  -- The first store: the next block's back link.
  rw [← setPC_self hpc]
  iterate 5 xstep code
  simp only [r11, r12, r14, and_granule hS31]
  xag
  simp only [show x + (S + 8#64) = x + S + 8#64 from (BitVec.add_assoc _ _ _).symm]
  refine classes (s0 := s0) (M := Tlsf.upd M (x + S + 8#64) (x + N)) (R := S - N) ?_ rfl
    (by xregs) ?_
  · refine St.setPC ?_ _
    refine St.setMem ?_ hxS8 hsp _
    xst
  intro y2 hs2' hpc2 r15 r16 hregs
  have q : ∀ q ∈ [Reg.x10, .x11, .x12, .x13, .x14, .x19], y2.getReg q = _ := hregs
  have q10 : y2.getReg .x10 = s0.getReg .x10 + 0x8000#64 := by
    rw [hregs .x10 (by simp)]; xregs; exact r10
  have q11 : y2.getReg .x11 = x := by rw [hregs .x11 (by simp)]; xregs; exact r11
  have q12 : y2.getReg .x12 = N := by rw [hregs .x12 (by simp)]; xregs; exact r12
  have q13 : y2.getReg .x13 = x + N := by rw [hregs .x13 (by simp)]; xregs
  have q14 : y2.getReg .x14 = S - N := by rw [hregs .x14 (by simp)]; xregs
  have q19 : y2.getReg .x19 = ptr := by rw [hregs .x19 (by simp)]; xregs; exact r19
  clear q hregs
  have hcode2 := hs2'.code
  have offH2 := offC _ (Tlsf.headAddr_inCtl hc hf2 hs2)
  rw [← setPC_self hpc2]
  iterate 10 xstep code
  simp only [q11, q13, q14, hs2'.self, r15, r16]
  xag0
  simp only [head_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC, hs2'.mem _ offH2]
  have hSL := offC _ (Tlsf.slBm_inCtl hc hf2)
  have hFL := offC _ (Tlsf.flBm_inCtl hc)
  have hne := Tlsf.slBm_ne_flBm (self := s0.getReg .x10) hf2
  -- `splitPre`, unfolded to what the bitmap tail leaves.
  have hpre : ∀ M3, M3 = (if Tlsf.upd M (x + S + 8#64) (x + N)
        (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) = 0#64 then
        Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd M (x + S + 8#64) (x + N))
          (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) (x + N))
          (x + N) (S - N)) (x + N + 8#64) x) (x + N + 0x10#64) (Tlsf.upd M (x + S + 8#64) (x + N)
          (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)))))
          (x + N + 0x18#64) 0#64
      else Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd M (x + S + 8#64)
          (x + N)) (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) (x + N))
          (x + N) (S - N)) (x + N + 8#64) x) (x + N + 0x10#64) (Tlsf.upd M (x + S + 8#64) (x + N)
          (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)))))
          (x + N + 0x18#64) 0#64) (Tlsf.upd M (x + S + 8#64) (x + N)
          (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) + 0x18#64)
          (x + N)) →
      splitPre (s0.getReg .x10) M x S N =
        Tlsf.upd (Tlsf.upd M3 (Tlsf.flBm (s0.getReg .x10))
          (M3 (Tlsf.flBm (s0.getReg .x10)) ||| 1#64 <<< (Tlsf.flOf (S - N)).toNat))
          (Tlsf.slBm (s0.getReg .x10) (Tlsf.flOf (S - N)))
          (M3 (Tlsf.slBm (s0.getReg .x10) (Tlsf.flOf (S - N))) |||
            1#64 <<< (Tlsf.slOf (S - N)).toNat) := by
    intro M3 hM3
    subst hM3
    unfold splitPre
    simp only [Tlsf.upd_ne hne]
  generalize hh2 : Tlsf.upd M (x + S + 8#64) (x + N)
    (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) = h2 at *
  have hM2 : St s0 (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd (Tlsf.upd M (x + S + 8#64)
      (x + N)) (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) (x + N))
      (x + N) (S - N)) (x + N + 8#64) x) (x + N + 0x10#64) h2) (x + N + 0x18#64) 0#64)
      ((((((((y2.setReg .x17 (s0.getReg .x10 + Tlsf.flOf (S - N) <<< 9)).setReg .x5
        (s0.getReg .x10 + Tlsf.flOf (S - N) <<< 9 + Tlsf.slOf (S - N) <<< 3)).setReg .x17 h2).setMem
        (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) (x + N)).setMem
        (x + N) (S - N)).setMem (x + N + 8#64) x).setMem (x + N + 0x10#64) h2).setMem
        (x + N + 0x18#64) 0#64) := by
    refine St.setMem ?_ (hxN _ (by decide)) hsp _
    refine St.setMem ?_ (hxN _ (by decide)) hsp _
    refine St.setMem ?_ (hxN _ (by decide)) hsp _
    refine St.setMem ?_ (by simpa using hxN 0#64 (by decide)) hsp _
    refine St.setMem ?_ offH2 hsp _
    xst
  xstep code
  · -- No old head: the remainder is alone in its list.
    have hz : h2 = 0#64 := by simpa using hb
    refine bitmaps (s0 := s0) (St.setPC hM2 _) rfl hsp hFL hSL hne hf2 hs2 (by xregs; exact q10)
      (by xregs; exact q11) (by xregs; exact q12) (by xregs; exact r15) (by xregs; exact r16)
      (by xregs; exact q19) ?_
    intro y' hy' hpc' a b c
    exact hk y' (by rw [hpre _ (if_pos hz).symm]; exact hy') hpc' a b c
  · -- The old head's back link to the remainder.
    have hz : h2 ≠ 0#64 := by simpa using hb
    -- The old head is a free block of the arena.
    have hh2' : h2 = (L (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))).headD 0#64 := by
      have t1 : (x + S + 8#64).toNat = x.toNat + S.toNat + 8 := by
        rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
      have hH := (Tlsf.headAddr_inCtl hc hf2 hs2).2
      have := hbA.2.1
      rw [← hh2, Tlsf.upd_ne (Tlsf.ne_nat (by simp only [Tlsf.ctlSize] at hH; omega))]
      exact hsh.heads _ _ hf2 hs2
    have hm : h2 ∈ L (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)) := by
      cases hl : L (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)) with
      | nil => rw [hl] at hh2'; exact (hz hh2').elim
      | cons z zs => rw [hl] at hh2'; rw [hh2']; exact List.mem_cons_self ..
    have hA := hsh.nodeA hm
    have off18 : ¬ InFrame (s0.getReg .x2) (h2 + 0x18#64) :=
      offN _ (by rw [BitVec.toNat_add]; simp; omega)
    xstep code
    simp only [q13]
    have hM3 := St.setPC (St.setMem hM2 off18 hsp (x + N)) 0x7801c574#64
    refine bitmaps (s0 := s0) hM3 rfl hsp hFL hSL hne hf2 hs2 (by xregs; exact q10)
      (by xregs; exact q11) (by xregs; exact q12) (by xregs; exact r15) (by xregs; exact r16)
      (by xregs; exact q19) ?_
    intro y' hy' hpc' a b c
    exact hk y' (by rw [hpre _ (if_neg hz).symm]; exact hy') hpc' a b c

/-- Where the pointer goes in a block at `x`, and the block size it needs. -/
def ptrOf (x align : Word) : Word :=
  (align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)
def needOf (x align size : Word) : Word :=
  (size - x + ptrOf x align + 31#64) &&& 0xffffffffffffffe0#64

/-- After the pop, at `0x7801c444`: place the pointer, then mark the block used whole or split
    it, and leave. -/
theorem tail {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {pre post : List Tlsf.Blk} {x S : Word}
    (hs : St s0 M y) (hpc : y.pc = 0x7801c444#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M bs L (fun a => False ∨ a = x))
    (hbs : bs = pre ++ ⟨x, S, false, false⟩ :: post)
    (hN31 : needOf x (s0.getReg .x11) (s0.getReg .x12) &&& 31#64 = 0#64)
    (hNS : needOf x (s0.getReg .x11) (s0.getReg .x12) ≤ S)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (hself : ¬ InFrame (s0.getReg .x2) (s0.getReg .x10))
    (offx : ¬ InFrame (s0.getReg .x2) x)
    (offp : 32#64 ≤ s0.getReg .x11 →
      ¬ InFrame (s0.getReg .x2) (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64))
    (r10 : y.getReg .x10 = s0.getReg .x10 + 0x8000#64) (r11 : y.getReg .x11 = x)
    (r14 : y.getReg .x14 = S) (r15 : y.getReg .x15 = x + 0x10#64)
    (hk : ∀ M' t, (M' = M ∧ needOf x (s0.getReg .x11) (s0.getReg .x12) = S ∨
        M' = splitPre (s0.getReg .x10) M x S (needOf x (s0.getReg .x11) (s0.getReg .x12)) ∧
          needOf x (s0.getReg .x11) (s0.getReg .x12) < S) →
      Out s0 (finMem (s0.getReg .x10) M' x (needOf x (s0.getReg .x11) (s0.getReg .x12))
        (ptrOf x (s0.getReg .x11)) (s0.getReg .x11)) (ptrOf x (s0.getReg .x11)) t →
      SafeN G n P t) : SafeN G n P y := by
  have hcode := hs.code
  -- The arithmetic, up to the branch at `0x7801c464`.
  have branch : ∀ y3, St s0 M y3 → y3.pc = 0x7801c464#64 →
      y3.getReg .x10 = s0.getReg .x10 + 0x8000#64 → y3.getReg .x11 = x → y3.getReg .x14 = S →
      y3.getReg .x12 = needOf x (s0.getReg .x11) (s0.getReg .x12) →
      y3.getReg .x19 = ptrOf x (s0.getReg .x11) → SafeN G n P y3 := by
    intro y3 hs3 hpc3 q10 q11 q14 q12 q19
    have hcode3 := hs3.code
    rw [← setPC_self hpc3]
    xstep code
    · -- exact fit
      have he : S = needOf x (s0.getReg .x11) (s0.getReg .x12) := by
        rw [q14, q12] at hb; simpa using hb
      refine fin (St.setPC hs3 _) rfl hsp hself (by xregs; exact q11) (by xregs; exact q12)
        (by xregs; exact q19) offx offp fun t ht => hk M t (.inl ⟨rfl, he.symm⟩) ht
    · have he : S ≠ needOf x (s0.getReg .x11) (s0.getReg .x12) := by
        rw [q14, q12] at hb; simpa using hb
      have hlt : needOf x (s0.getReg .x11) (s0.getReg .x12) < S := by
        generalize needOf x (s0.getReg .x11) (s0.getReg .x12) = N at *
        bv_omega
      refine splitPath (St.setPC hs3 _) rfl hsh hbs hN31 hlt hsp hspc
        (by xregs; exact q10) (by xregs; exact q11) (by xregs; exact q12) (by xregs; exact q14)
        (by xregs; exact q19) fun y4 hs4 hpc4 a b c => ?_
      exact fin hs4 hpc4 hsp hself a b c offx offp fun t ht =>
        hk _ t (.inr ⟨rfl, hlt⟩) ht
  rw [← setPC_self hpc]
  iterate 8 xstep code
  refine branch _ ?_ rfl ?_ ?_ ?_ ?_ ?_
  · xst
  all_goals xregs
  all_goals first | with_reducible assumption | (simp only [r11, r15, hs.align, hs.size, ptrOf, needOf]; rfl)

end Cases.Zip2005.Runtime.Alloc
