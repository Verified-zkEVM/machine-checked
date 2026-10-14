/-
  Cases.Zip2005.Runtime.Alloc.Spec

  rlsf's `alloc` (`0x7801c18c`), end to end (phase D4).

  The segments compose: the prologue takes the lock and sizes the request (`entrySeg`); the
  class search (`classSearch`) and the two bitmap lookups (`slLookup`, `flLookup`) find a
  nonempty free list at least as large as the request, or return null; `afterFound` pops its
  head, splits off the remainder or takes the exact fit, marks the block used, places the
  pointer at the requested alignment and returns.

  `spec` is stated against the heap model `Tlsf.Rep`: from a well-formed heap, `alloc`
  returns with the heap well formed again, every used block kept, memory outside the
  allocator's own doublewords unchanged, and the result null or a fresh block that holds
  `size` bytes at `align` (`Grant`). Its premises are the reference run's: the lock is free
  (it is part of `Rep`), the de Bruijn table is in `.rodata` (`RoOk`), the stack frame fits
  and the control block sits above `.rodata`.
-/

import Cases.Zip2005.Runtime.Alloc.Search

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Alloc

open RiscvZkvm.Rv64
open AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check AsmVerif.RiscV.Exec
  Cases.Zip2005.Image

/-- `St` through register writes, `pc` updates and stores off the frame (`hsp` in scope). -/
macro "xstm" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine St.setPC ?_ _ |
    with_reducible refine St.setReg ?_ (by decide) (by decide) (by decide) (by decide) (by decide) _ |
    (refine St.setMem ?_ (by assumption) (by assumption) _)))

theorem off_eq_iff (x c d : Word) : (x + c = x + d) ↔ c = d := by
  constructor
  · intro h; bv_omega
  · rintro rfl; rfl

/-- The prologue and the lock, `0x7801c18c`–`0x7801c1e8`: save the registers, take the lock,
    and size the request; too large a request returns null. -/
theorem entrySeg {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 : MachineState}
    (hpc : s0.pc = 0x7801c18c#64) (hcode : s0.code = C)
    (hlock : s0.getMem (s0.getReg .x10) = 0#64)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat) (hself : ¬ InFrame (s0.getReg .x2) (s0.getReg .x10))
    (hnull : ∀ y, St s0 (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) y →
      y.pc = 0x7801c2ec#64 → y.getReg .x19 = 0#64 → SafeN G n P y)
    (hgo : ∀ y a, St s0 (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) y →
      y.pc = 0x7801c1ec#64 → y.getReg .x10 = a → y.getReg .x19 = 0#64 →
      a = s0.getReg .x12 + (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64) →
      ¬ a < s0.getReg .x12 → ¬ 0xffffffffffffffe0#64 < a → SafeN G n P y) :
    SafeN G n P s0 := by
  -- After the prologue and the (empty) `syscall_dump_elf`, at `0x7801c1b8`.
  -- After the lock, at `0x7801c1d8`, with `max(align, 16)` in `a0`.
  have mid : ∀ y, St s0 (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) y →
      y.pc = 0x7801c1d8#64 →
      y.getReg .x10 = (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64) →
      SafeN G n P y := by
    intro y hs hpcy h10
    have hcy := hs.code
    rw [← setPC_self hpcy]
    iterate 3 xstep code
    · exact hnull _ (by xst) rfl (by xregs; rfl)
    have hov1 := hb
    iterate 2 xstep code
    · exact hnull _ (by xst) rfl (by xregs; rfl)
    have hov2 := hb
    rw [hs.size, h10] at hov1 hov2
    refine hgo _ (s0.getReg .x12 + if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64)
      (by xst) rfl (by xregs; rw [hs.size, h10]) (by xregs; rfl) rfl ?_ ?_
    · simpa [BitVec.ult_iff_lt] using hov1
    · simpa [BitVec.ult_iff_lt] using hov2
  have rest : ∀ y, St s0 s0.getMem y → y.pc = 0x7801c1b8#64 → SafeN G n P y := by
    intro y hs hpcy
    have hcy := hs.code
    rw [← setPC_self hpcy]
    xstep code
    simp only [MachineState.getMem_setPC, hs.self, hs.mem _ hself, hlock]
    xstep code
    · exfalso; simp at hb
    iterate 3 xstep code
    simp only [hs.self]
    have hs1 := St.setMem hs hself hsp 0xffffffffffffffff#64
    iterate 2 xstep code
    · refine mid _ (by xstm) rfl ?_
      xregs
      rw [hs.align] at hb ⊢
      simp only [BitVec.ult_iff_lt] at hb
      rw [if_pos hb]
    · xstep code
      refine mid _ (by xstm) rfl ?_
      xregs
      rw [hs.align] at hb
      simp only [BitVec.ult_iff_lt] at hb
      rw [if_neg hb]
  rw [← setPC_self hpc]
  iterate 11 xstep code
  xstep Entry.dumpF_code
  refine rest _ ?_ rfl
  xag
  have hn : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → ∀ a, ¬ InFrame (s0.getReg .x2) a →
      a ≠ s0.getReg .x2 + c := fun c hc a ha e => slot_ne ha hsp hc e.symm
  refine ⟨hcode, by simp [hcode], by xregs, by xregs, by xregs, by xregs,
    fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, by simp⟩
  · simp only [untouched, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> xregs
  all_goals simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
    off_eq_iff, BitVec.reduceEq, if_true, if_false]
  simp only [hn 0xfffffffffffffff8#64 (by decide) a ha, hn 0xfffffffffffffff0#64 (by decide) a ha,
    hn 0xffffffffffffffe8#64 (by decide) a ha, hn 0xffffffffffffffe0#64 (by decide) a ha,
    hn 0xffffffffffffffd8#64 (by decide) a ha, if_false]

/-! ## Arithmetic of the placement -/

/-- The block a request needs, and where its pointer goes, are within the block found. -/
theorem place {x S align size : Word} (hx : x &&& 31#64 = 0#64) (hx40 : x < 1#64 <<< 40)
    (hS : x + S < 1#64 <<< 40) (hS' : S < 1#64 <<< 40)
    (hp : align &&& (align - 1#64) = 0#64) (hp0 : align ≠ 0#64)
    (hov1 : ¬ size + (if 16#64 < align then align else 16#64) < size)
    (hov2 : ¬ 0xffffffffffffffe0#64 < size + (if 16#64 < align then align else 16#64))
    (hr : reqOf (size + (if 16#64 < align then align else 16#64)) ≤ S) :
    needOf x align size ≤ S ∧ 32#64 ≤ needOf x align size ∧
      needOf x align size &&& 31#64 = 0#64 ∧
      x + 16#64 ≤ ptrOf x align ∧ ptrOf x align ≤ ptrOf x align + size ∧
      ptrOf x align + size ≤ x + needOf x align size ∧
      ptrOf x align &&& (align - 1#64) = 0#64 ∧
      (align < 32#64 → ptrOf x align = x + 16#64) ∧
      (32#64 ≤ align → x + 32#64 ≤ ptrOf x align) := by
  have : ∀ x S align size : BitVec 64, x &&& 31#64 = 0#64 → x < 1#64 <<< 40 →
      x + S < 1#64 <<< 40 → S < 1#64 <<< 40 →
      align &&& (align - 1#64) = 0#64 → align ≠ 0#64 →
      ¬ size + (if 16#64 < align then align else 16#64) < size →
      ¬ 0xffffffffffffffe0#64 < size + (if 16#64 < align then align else 16#64) →
      (size + (if 16#64 < align then align else 16#64) + 31#64) &&& 0xffffffffffffffe0#64 ≤ S →
      ((size - x + ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) + 31#64) &&&
          0xffffffffffffffe0#64) ≤ S ∧
        32#64 ≤ ((size - x + ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) +
          31#64) &&& 0xffffffffffffffe0#64) ∧
        ((size - x + ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) + 31#64) &&&
          0xffffffffffffffe0#64) &&& 31#64 = 0#64 ∧
        x + 16#64 ≤ ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) ∧
        ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) ≤
          ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) + size ∧
        ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) + size ≤
          x + ((size - x + ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) +
            31#64) &&& 0xffffffffffffffe0#64) ∧
        ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) &&& (align - 1#64) =
          0#64 ∧
        (align < 32#64 → ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align)) =
          x + 16#64) ∧
        (32#64 ≤ align → x + 32#64 ≤
          ((align + (x + 16#64) + 0xffffffffffffffff#64) &&& (0#64 - align))) := by
    intro x S align size hx hx40 hS hS' hp hp0 hov1 hov2 hr
    bv_decide
  exact this x S align size hx hx40 hS hS' hp hp0 hov1 hov2 hr

/-! ## What `alloc` promises -/

/-- The allocator's own doublewords in a heap: its control block, every block's back link and
    every free block whole. `alloc` changes nothing else. -/
def Mine (self : Word) (bs : List Tlsf.Blk) (a : Word) : Prop :=
  (self.toNat ≤ a.toNat ∧ a.toNat < self.toNat + Tlsf.ctlSize) ∨
  ∃ b ∈ bs, a = b.a + 8#64 ∨
    (b.used = false ∧ b.a.toNat ≤ a.toNat ∧ a.toNat < b.a.toNat + b.sz.toNat)

/-- The result of `alloc(align, size)`: null, or a pointer into a block that was free and is
    now used — past its header, aligned, with `size` bytes before the block's end, and, for a
    large alignment, the block's address just below it (what `dealloc` reads back). -/
def Grant (align size : Word) (bs bs' : List Tlsf.Blk) (M' : Word → Word) (r : Word) : Prop :=
  r = 0#64 ∨ ∃ b ∈ bs', b.used = true ∧ b.last = false ∧
    (∃ S, (⟨b.a, S, false, false⟩ : Tlsf.Blk) ∈ bs ∧ b.sz ≤ S) ∧
    b.a + 16#64 ≤ r ∧ r ≤ r + size ∧ r + size ≤ b.a + b.sz ∧ r &&& (align - 1#64) = 0#64 ∧
    (align < 32#64 → r = b.a + 16#64) ∧ (32#64 ≤ align → M' (r + 0xfffffffffffffff8#64) = b.a)

/-- **What the caller gets back from `alloc`**: the return (`Out`) with memory `M'` and the
    result `r`; the heap well formed again, with every used block kept; nothing but the
    allocator's own doublewords changed; and the result granted. -/
def Done (s0 : MachineState) (base : Word) (bs : List Tlsf.Blk) (t : MachineState) : Prop :=
  ∃ M' r, Out s0 M' r t ∧ ∃ bs' L', Tlsf.Rep (s0.getReg .x10) base M' bs' L' ∧
    (∀ b ∈ bs, b.used = true → b ∈ bs') ∧
    (∀ a, ¬ Mine (s0.getReg .x10) bs a → M' a = s0.getMem a) ∧
    Grant (s0.getReg .x11) (s0.getReg .x12) bs bs' M' r

/-! ## Memory the segments leave alone -/

theorem popMem_other {self f s nx a : Word} {m : Word → Word} (h1 : a ≠ Tlsf.headAddr self f s)
    (h2 : a ≠ Tlsf.slBm self f) (h3 : a ≠ Tlsf.flBm self) (h4 : nx ≠ 0#64 → a ≠ nx + 0x18#64) :
    Tlsf.popMem self m f s nx a = m a := by
  unfold Tlsf.popMem
  by_cases hz : nx = 0#64
  · simp only [if_pos hz]
    split <;> simp only [Tlsf.upd, if_neg h1, if_neg h2, if_neg h3]
  · simp only [if_neg hz, Tlsf.upd, if_neg h1, if_neg (h4 hz)]

theorem splitPre_other {self x S N a : Word} {m : Word → Word}
    (d1 : a ≠ x + S + 8#64)
    (d2 : a ≠ Tlsf.headAddr self (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)))
    (d3 : a ≠ x + N) (d4 : a ≠ x + N + 8#64) (d5 : a ≠ x + N + 0x10#64)
    (d6 : a ≠ x + N + 0x18#64)
    (d7 : Tlsf.upd m (x + S + 8#64) (x + N)
        (Tlsf.headAddr self (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) ≠ 0#64 →
      a ≠ Tlsf.upd m (x + S + 8#64) (x + N)
        (Tlsf.headAddr self (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) + 0x18#64)
    (d8 : a ≠ Tlsf.flBm self) (d9 : a ≠ Tlsf.slBm self (Tlsf.flOf (S - N))) :
    splitPre self m x S N a = m a := by
  unfold splitPre
  generalize Tlsf.upd m (x + S + 8#64) (x + N)
    (Tlsf.headAddr self (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) = h2 at *
  by_cases hz : h2 = 0#64
  · simp only [if_pos hz, Tlsf.upd, if_neg d1, if_neg d2, if_neg d3, if_neg d4, if_neg d5,
      if_neg d6, if_neg d8, if_neg d9]
  · simp only [if_neg hz, Tlsf.upd, if_neg d1, if_neg d2, if_neg d3, if_neg d4, if_neg d5,
      if_neg d6, if_neg (d7 hz), if_neg d8, if_neg d9]

/-- The lock is none of the shape's doublewords. -/
theorem key_ne_self {self base : Word} {m : Word → Word} {bs : List Tlsf.Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Tlsf.Shape self base m bs L out)
    {a : Word} (ha : Tlsf.Key self bs a) : a ≠ self := by
  intro e
  subst e
  have hl := h.layout.1
  rcases ha with ha | ⟨b, hb, ha⟩
  · have := ha.1; omega
  · have hA := h.blkA hb
    have h8 : ∀ c : Word, c.toNat < 32 → (b.a + c).toNat = b.a.toNat + c.toNat := fun c hc => by
      rw [BitVec.toNat_add]; omega
    simp only [Tlsf.ctlSize] at hl
    rcases ha with ha | ha | ⟨_, ha | ha⟩
    · rw [ha] at hl; omega
    · have := h8 8#64 (by decide); rw [← ha] at this; simp at this; omega
    · have := h8 0x10#64 (by decide); rw [← ha] at this; simp at this; omega
    · have := h8 0x18#64 (by decide); rw [← ha] at this; simp at this; omega

/-- After the header: the back pointer and the lock's release leave a well-formed heap. -/
theorem finRep {self base x N ptr align : Word} {Mpre : Word → Word} {bsF : List Tlsf.Blk}
    {LF : Word → Word → List Word}
    (hsh : Tlsf.Shape self base (Tlsf.upd Mpre x (N + 1#64)) bsF LF (fun _ => False))
    (hlock : Mpre self = 0xffffffffffffffff#64) (hxs : x ≠ self)
    (hp : 32#64 ≤ align → ¬ Tlsf.Key self bsF (ptr + 0xfffffffffffffff8#64) ∧
      ptr + 0xfffffffffffffff8#64 ≠ self) :
    Tlsf.Rep self base (finMem self Mpre x N ptr align) bsF LF := by
  have h3 : Tlsf.Shape self base (if align < 32#64 then Tlsf.upd Mpre x (N + 1#64) else
      Tlsf.upd (Tlsf.upd Mpre x (N + 1#64)) (ptr + 0xfffffffffffffff8#64) x) bsF LF
      (fun _ => False) ∧
      (if align < 32#64 then Tlsf.upd Mpre x (N + 1#64) else
        Tlsf.upd (Tlsf.upd Mpre x (N + 1#64)) (ptr + 0xfffffffffffffff8#64) x) self =
        0xffffffffffffffff#64 := by
    split
    · exact ⟨hsh, by rw [Tlsf.upd_ne hxs.symm]; exact hlock⟩
    · rename_i ha
      have ha : 32#64 ≤ align := by
        have : ∀ a : BitVec 64, ¬ a < 32#64 → 32#64 ≤ a := by intro a h; bv_decide
        exact this align ha
      obtain ⟨hk, hne⟩ := hp ha
      refine ⟨hsh.congr fun a hka => Tlsf.upd_ne (fun e => hk (e ▸ hka)), ?_⟩
      rw [Tlsf.upd_ne hne.symm, Tlsf.upd_ne hxs.symm]; exact hlock
  simp only [finMem]
  generalize (if align < 32#64 then Tlsf.upd Mpre x (N + 1#64) else
      Tlsf.upd (Tlsf.upd Mpre x (N + 1#64)) (ptr + 0xfffffffffffffff8#64) x) = M3 at h3 ⊢
  obtain ⟨h3, h3l⟩ := h3
  rw [Tlsf.rep_iff]
  refine ⟨by rw [Tlsf.upd_same, h3l]; rfl, h3.congr fun a ha => Tlsf.upd_ne (key_ne_self h3 ha)⟩

/-- Each block's header is in memory. -/
theorem chain_hdr {m : Word → Word} :
    ∀ {bs a p}, Tlsf.Chain m a p bs → ∀ b ∈ bs, m b.a = b.hdr
  | [], _, _, h, _, _ => h.elim
  | b :: bs, a, p, ⟨h1, h2, _, _, _, h6⟩, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [h1]; exact h2
    · split at h6
      · rw [h6.1] at hc; simp at hc
      · exact chain_hdr h6 c hc

/-- The block after a free one begins where it ends. -/
theorem chain_next {m : Word → Word} {pre post : List Tlsf.Blk} {x S : Word} {base : Word}
    (h : Tlsf.Chain m base 0#64 (pre ++ ⟨x, S, false, false⟩ :: post)) :
    ∃ c post', post = c :: post' ∧ c.a = x + S := by
  obtain ⟨a', p', _, hc⟩ := (Tlsf.chain_append (List.cons_ne_nil _ _)).mp h
  obtain ⟨h1, _, _, _, _, h6⟩ := hc
  simp only [Bool.false_eq_true, if_false] at h1 h6
  subst h1
  cases post with
  | nil => exact h6.elim
  | cons c post' => exact ⟨c, post', rfl, h6.1⟩

theorem req_ok {size align : Word}
    (hov1 : ¬ size + (if 16#64 < align then align else 16#64) < size)
    (hov2 : ¬ 0xffffffffffffffe0#64 < size + (if 16#64 < align then align else 16#64)) :
    32#64 ≤ reqOf (size + (if 16#64 < align then align else 16#64)) ∧
      reqOf (size + (if 16#64 < align then align else 16#64)) &&& 31#64 = 0#64 ∧
      16#64 ≤ size + (if 16#64 < align then align else 16#64) := by
  have : ∀ size align : BitVec 64,
      ¬ size + (if 16#64 < align then align else 16#64) < size →
      ¬ 0xffffffffffffffe0#64 < size + (if 16#64 < align then align else 16#64) →
      32#64 ≤ (size + (if 16#64 < align then align else 16#64) + 31#64) &&& 0xffffffffffffffe0#64 ∧
      ((size + (if 16#64 < align then align else 16#64) + 31#64) &&& 0xffffffffffffffe0#64) &&&
        31#64 = 0#64 ∧
      16#64 ≤ size + (if 16#64 < align then align else 16#64) := by
    intro size align h1 h2; bv_decide
  exact this size align hov1 hov2

/-- From the found list to the return: pop, place, mark or split, leave; the heap well formed
    again and the request granted. -/
theorem afterFound {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word} {fl sl : Word}
    (hs : St s0 (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) y)
    (hpc : y.pc = 0x7801c378#64)
    (hrep : Tlsf.Rep (s0.getReg .x10) base s0.getMem bs L)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat) (hstk : (s0.getReg .x2).toNat ≤ 0x78000000)
    (hspc : 0x78000000 ≤ (s0.getReg .x10).toNat)
    (hp : s0.getReg .x11 &&& (s0.getReg .x11 - 1#64) = 0#64) (hp0 : s0.getReg .x11 ≠ 0#64)
    (hov1 : ¬ s0.getReg .x12 + (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64) <
      s0.getReg .x12)
    (hov2 : ¬ 0xffffffffffffffe0#64 <
      s0.getReg .x12 + (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64))
    (q10 : y.getReg .x10 = s0.getReg .x10 + 0x8000#64) (q12 : y.getReg .x12 = fl)
    (q13 : y.getReg .x13 = sl) (hfl : fl < 64#64) (hsl : sl < 64#64) (hL : L fl sl ≠ [])
    (hlex : Tlsf.flSearch (reqOf (s0.getReg .x12 +
        (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64))) < fl ∨
      (Tlsf.flSearch (reqOf (s0.getReg .x12 +
          (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64))) = fl ∧
        (Tlsf.searchRaw (reqOf (s0.getReg .x12 +
          (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64))) &&& 63#64) ≤ sl))
    (hk : ∀ t, Done s0 base bs t → SafeN G n P t) : SafeN G n P y := by
  obtain ⟨hlock0, hsh0⟩ := Tlsf.rep_iff.mp hrep
  have hsh1 := hsh0.congr (m' := Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64)
    fun a ha => Tlsf.upd_ne (key_ne_self hsh0 ha)
  have hself' : ¬ InFrame (s0.getReg .x2) (s0.getReg .x10) := off_frame (by omega)
  obtain ⟨x, xs, hLx⟩ : ∃ x xs, L fl sl = x :: xs := by
    cases h : L fl sl with
    | nil => exact (hL h).elim
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hx : x ∈ L fl sl := by rw [hLx]; exact List.mem_cons_self ..
  obtain ⟨-, b, hb, hbx, hbu, hbf, hbs⟩ := hsh0.members fl sl x hx
  have hbl : b.last = false := by
    cases h : b.last
    · rfl
    · have := hsh0.chain.last_used b hb h; rw [hbu] at this; simp at this
  have hbeq : b = ⟨x, b.sz, false, false⟩ := by
    cases b; simp only at hbx hbu hbl; subst hbx; subst hbu; subst hbl; rfl
  -- The block, its size and where it lies.
  have hxs : x ≠ s0.getReg .x10 := by
    have := (hsh0.blkA hb).2.1; have := hsh0.layout.1; rw [hbx] at *
    exact Tlsf.ne_nat (by simp only [Tlsf.ctlSize] at *; omega)
  obtain ⟨hxA, hxb, hx40, hS31, hSok⟩ := hsh0.blk hb
  rw [hbx] at hxA hxb hx40
  generalize hS : b.sz = S at *
  subst hbeq
  have hhdr : Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64 x = S := by
    rw [Tlsf.upd_ne hxs, chain_hdr hsh0.chain _ hb]
    exact (Tlsf.hdr_free).symm
  obtain ⟨pre, post, hbs'⟩ := List.append_of_mem hb
  -- The request fits.
  obtain ⟨hr32, hr31, ha16⟩ := req_ok hov1 hov2
  have hreq := Tlsf.search_ok' hSok hr32 hr31 (by
    rw [hbf, hbs]; simpa only [Tlsf.slSearch] using hlex)
  have hx40' : x < 1#64 <<< 40 := by
    rw [BitVec.lt_def]; simp; have := hSok.2; omega
  have hxS40 : x + S < 1#64 <<< 40 := by
    rw [BitVec.lt_def, BitVec.toNat_add]; simp; omega
  obtain ⟨hNS, hN32, hN31, hp16, hpw, hpN, hpal, hsmall, hbig⟩ :=
    place hxA hx40' hxS40 hSok.2 hp hp0 hov1 hov2 hreq
  have hlay := hsh0.layout.1
  simp only [Tlsf.ctlSize] at hlay
  -- Numbers for the pointer.
  have hN2 : (needOf x (s0.getReg .x11) (s0.getReg .x12)).toNat ≤ S.toNat := by
    rw [BitVec.le_def] at hNS; exact hNS
  have hpN' : (ptrOf x (s0.getReg .x11)).toNat ≤ x.toNat + S.toNat := by
    have h1 : (x + needOf x (s0.getReg .x11) (s0.getReg .x12)).toNat =
        x.toNat + (needOf x (s0.getReg .x11) (s0.getReg .x12)).toNat := by
      rw [BitVec.toNat_add]; omega
    have h2 := hpN; have h3 := hpw
    rw [BitVec.le_def] at h2 h3; rw [h1] at h2; omega
  have hp16' : x.toNat + 16 ≤ (ptrOf x (s0.getReg .x11)).toNat := by
    have := hp16; rw [BitVec.le_def, BitVec.toNat_add] at this; simp at this; omega
  have offx : ¬ InFrame (s0.getReg .x2) x := off_frame (by omega)
  have hp8 : 32#64 ≤ s0.getReg .x11 →
      (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64).toNat =
        (ptrOf x (s0.getReg .x11)).toNat - 8 ∧ x.toNat + 24 ≤ (ptrOf x (s0.getReg .x11)).toNat - 8 := by
    intro ha
    have := hbig ha; rw [BitVec.le_def, BitVec.toNat_add] at this; simp at this
    refine ⟨?_, by omega⟩
    rw [BitVec.toNat_add]; simp; omega
  have offp : 32#64 ≤ s0.getReg .x11 →
      ¬ InFrame (s0.getReg .x2) (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64) :=
    fun ha => off_frame (by have := hp8 ha; omega)
  refine found hs hpc hsh1 hsp (by omega) q10 q12 q13 hfl hsl hLx ?_
  intro y' hs' hpc' r10 r11 r14 r15
  rw [hhdr] at r14
  have hsh2 := hsh1.pop hfl hsl hLx
  refine tail hs' hpc' hsh2 hbs' hN31 hNS hsp (by omega) hself' offx offp r10 r11 r14 r15 ?_
  intro M' t hcase ht
  apply hk t
  refine ⟨_, _, ht, ?_⟩
  -- What is the allocator's.
  have mineC : ∀ k, Tlsf.InCtl (s0.getReg .x10) k → Mine (s0.getReg .x10) bs k :=
    fun k hk => .inl ⟨by have := hk.1; omega, hk.2⟩
  have mineSelf : Mine (s0.getReg .x10) bs (s0.getReg .x10) :=
    .inl ⟨Nat.le_refl _, by simp only [Tlsf.ctlSize]; omega⟩
  have mineX : ∀ k : Word, x.toNat ≤ k.toNat → k.toNat < x.toNat + S.toNat →
      Mine (s0.getReg .x10) bs k := fun k h1 h2 => .inr ⟨_, hb, .inr ⟨rfl, h1, h2⟩⟩
  have mineNode : ∀ f s z (c : Word), z ∈ L f s → c.toNat < 32 →
      Mine (s0.getReg .x10) bs (z + c) := by
    intro f s z c hz hc
    obtain ⟨-, d, hd, rfl, hdu, -⟩ := hsh0.members f s z hz
    obtain ⟨_, _, hd40, _, hdok⟩ := hsh0.blk hd
    have := Tlsf.Shape.sz_ge hdok
    refine .inr ⟨d, hd, .inr ⟨hdu, ?_, ?_⟩⟩ <;> rw [BitVec.toNat_add] <;> omega
  -- The pop leaves the lock and everything not the allocator's.
  have hnx : xs.headD 0#64 ≠ 0#64 → xs.headD 0#64 ∈ L fl sl := by
    intro hz
    cases xs with
    | nil => exact (hz rfl).elim
    | cons z zs => rw [hLx]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hc := hsh0.ctlOk
  have hHc := Tlsf.headAddr_inCtl hc hfl hsl
  have hSLc := Tlsf.slBm_inCtl hc hfl
  have hFLc := Tlsf.flBm_inCtl hc
  have popOther : ∀ a, ¬ Mine (s0.getReg .x10) bs a →
      Tlsf.popMem (s0.getReg .x10) (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64)
        fl sl (xs.headD 0#64) a = s0.getMem a := by
    intro a ha
    rw [popMem_other (fun e => ha (by rw [e]; exact mineC _ hHc))
      (fun e => ha (by rw [e]; exact mineC _ hSLc)) (fun e => ha (by rw [e]; exact mineC _ hFLc))
      (fun hz e => ha (by rw [e]; exact mineNode _ _ _ 0x18#64 (hnx hz) (by decide))),
      Tlsf.upd_ne (fun e => ha (by rw [e]; exact mineSelf))]
  have popSelf : Tlsf.popMem (s0.getReg .x10)
      (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) fl sl (xs.headD 0#64)
      (s0.getReg .x10) = 0xffffffffffffffff#64 := by
    have hne : ∀ k, Tlsf.InCtl (s0.getReg .x10) k → s0.getReg .x10 ≠ k :=
      fun k hk e => by have := hk.1; rw [← e] at this; omega
    rw [popMem_other (hne _ hHc) (hne _ hSLc) (hne _ hFLc) (fun hz e => by
      obtain ⟨_, hzb, hz40⟩ := hsh0.nodeA (hnx hz)
      have := Tlsf.toNat_add_lt (c := 0x18#64) hz40 (by decide)
      rw [← e, show (0x18#64 : Word).toNat = 24 from rfl] at this; omega), Tlsf.upd_same]
  have hx40n : x.toNat < 2 ^ 40 := by omega
  have hptrN : ptrOf x (s0.getReg .x11) ≤ x + needOf x (s0.getReg .x11) (s0.getReg .x12) :=
    BitVec.le_trans hpw hpN
  -- The back pointer's doubleword, as a number.
  have hpb : ∀ N : Word, ptrOf x (s0.getReg .x11) ≤ x + N → N.toNat ≤ S.toNat →
      32#64 ≤ s0.getReg .x11 →
      x.toNat + 24 ≤ (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64).toNat ∧
        (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64).toNat < x.toNat + N.toNat := by
    intro N h hN ha
    obtain ⟨t8, hge⟩ := hp8 ha
    rw [BitVec.le_def, BitVec.toNat_add] at h
    rw [t8]; omega
  -- No key of the new heap is the back pointer's doubleword.
  have notKey : ∀ (N : Word) (bsF : List Tlsf.Blk) (LF : Word → Word → List Word) (MF : Word → Word),
      Tlsf.Shape (s0.getReg .x10) base MF bsF LF (fun _ => False) →
      (⟨x, N, true, false⟩ : Tlsf.Blk) ∈ bsF → N.toNat ≤ S.toNat →
      ptrOf x (s0.getReg .x11) ≤ x + N → 32#64 ≤ s0.getReg .x11 →
      ¬ Tlsf.Key (s0.getReg .x10) bsF (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64) ∧
        ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64 ≠ s0.getReg .x10 := by
    intro N bsF LF MF hshF hb1 hN hle ha
    obtain ⟨h1, h2⟩ := hpb N hle hN ha
    refine ⟨fun hk => ?_, Tlsf.ne_nat (by omega)⟩
    rcases hk with hk | ⟨c, hc, hk⟩
    · have := hk.2; simp only [Tlsf.ctlSize] at this; omega
    · by_cases hcb : c = ⟨x, N, true, false⟩
      · subst hcb
        simp only at hk
        rcases hk with e | e | ⟨e, _⟩
        · rw [e] at h1; omega
        · rw [e, Tlsf.toNat_add_lt hx40n (by decide)] at h1; simp at h1
        · simp at e
      · have hk' : (⟨x, N, true, false⟩ : Tlsf.Blk).a.toNat ≤
            (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64).toNat ∧
            (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64).toNat <
              (⟨x, N, true, false⟩ : Tlsf.Blk).a.toNat + (⟨x, N, true, false⟩ : Tlsf.Blk).sz.toNat :=
          ⟨by simp only; omega, by simp only; omega⟩
        have hne : (⟨x, N, true, false⟩ : Tlsf.Blk) ≠ c := fun e => hcb e.symm
        rcases hk with e | e | ⟨_, e | e⟩
        · exact hshF.blk_ne hb1 hc hne hk' (d := 0#64) (by decide) (by simpa using e)
        · exact hshF.blk_ne hb1 hc hne hk' (by decide) e
        · exact hshF.blk_ne hb1 hc hne hk' (by decide) e
        · exact hshF.blk_ne hb1 hc hne hk' (by decide) e
  -- Used blocks stay.
  have keepUsed : ∀ c ∈ bs, c.used = true → c ∈ pre ∨ c ∈ post := by
    intro c hc hu
    rw [hbs'] at hc
    rcases List.mem_append.mp hc with h | h
    · exact .inl h
    · rcases List.mem_cons.mp h with rfl | h
      · simp at hu
      · exact .inr h
  have mineP : ∀ a, ¬ Mine (s0.getReg .x10) bs a → 32#64 ≤ s0.getReg .x11 →
      a ≠ ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64 := fun a ha hal e => by
    obtain ⟨h1, h2⟩ := hpb _ hptrN hN2 hal
    exact ha (by rw [e]; exact mineX _ (by omega) (by omega))
  have mineXa : ∀ a, ¬ Mine (s0.getReg .x10) bs a → a ≠ x := fun a ha e =>
    ha (by rw [e]; exact mineX _ (Nat.le_refl _) (by have := Tlsf.Shape.sz_ge hSok; omega))
  have finOther : ∀ (Mpre : Word → Word) (N : Word) a, ¬ Mine (s0.getReg .x10) bs a →
      finMem (s0.getReg .x10) Mpre x N (ptrOf x (s0.getReg .x11)) (s0.getReg .x11) a = Mpre a := by
    intro Mpre N a ha
    simp only [finMem]
    rw [Tlsf.upd_ne (fun e => ha (by rw [e]; exact mineSelf))]
    split
    · rw [Tlsf.upd_ne (mineXa a ha)]
    · rename_i hal
      have hal : 32#64 ≤ s0.getReg .x11 := by
        have : ∀ a : BitVec 64, ¬ a < 32#64 → 32#64 ≤ a := by intro a h; bv_decide
        exact this _ hal
      rw [Tlsf.upd_ne (mineP a ha hal), Tlsf.upd_ne (mineXa a ha)]
  have finPtr : ∀ (Mpre : Word → Word) (N : Word), 32#64 ≤ s0.getReg .x11 →
      finMem (s0.getReg .x10) Mpre x N (ptrOf x (s0.getReg .x11)) (s0.getReg .x11)
        (ptrOf x (s0.getReg .x11) + 0xfffffffffffffff8#64) = x := by
    intro Mpre N hal
    have hn : ¬ s0.getReg .x11 < 32#64 := by
      have : ∀ a : BitVec 64, 32#64 ≤ a → ¬ a < 32#64 := by intro a h; bv_decide
      exact this _ hal
    obtain ⟨h1, _⟩ := hpb _ hptrN hN2 hal
    simp only [finMem]
    rw [Tlsf.upd_ne (Tlsf.ne_nat (by omega)), if_neg hn, Tlsf.upd_same]
  rcases hcase with ⟨rfl, hNeq⟩ | ⟨rfl, hlt⟩
  · -- Exact fit: the block is used whole.
    have hshF := hsh2.mark hbs'
    have hb1 : (⟨x, S, true, false⟩ : Tlsf.Blk) ∈ pre ++ ⟨x, S, true, false⟩ :: post :=
      List.mem_append_right _ (List.mem_cons_self ..)
    rw [hNeq] at hpN ⊢
    refine ⟨_, _, finRep hshF popSelf hxs (notKey S _ _ _ hshF hb1 (Nat.le_refl _)
      (BitVec.le_trans hpw hpN)), fun c hc hu => ?_, fun a ha => ?_, .inr ⟨_, hb1, rfl, rfl,
      ⟨S, hb, BitVec.le_refl _⟩, hp16, hpw, hpN, hpal, hsmall, fun hal => finPtr _ _ hal⟩⟩
    · rcases keepUsed c hc hu with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    · rw [finOther _ _ a ha]; exact popOther a ha
  · -- Split: the front is used, the rest filed.
    generalize hNe : needOf x (s0.getReg .x11) (s0.getReg .x12) = N at *
    have hshF := hsh2.split hbs' hN31 hN32 hlt
    rw [splitMem_eq] at hshF
    have hb1 : (⟨x, N, true, false⟩ : Tlsf.Blk) ∈
        pre ++ ⟨x, N, true, false⟩ :: ⟨x + N, S - N, false, false⟩ :: post :=
      List.mem_append_right _ (List.mem_cons_self ..)
    obtain ⟨_, hRok⟩ := Tlsf.rem_ok hS31 hSok hN31 hlt
    have hR1 := Tlsf.Shape.sz_ge hRok
    have hRn : (S - N).toNat = S.toNat - N.toNat := by
      rw [BitVec.toNat_sub]; rw [BitVec.lt_def] at hlt; omega
    -- The split's doublewords: the allocator's, and not the lock.
    obtain ⟨c, post', hpost, hca⟩ := chain_next (hbs' ▸ hsh0.chain)
    have hcb : c ∈ bs := by rw [hbs', hpost]; simp
    have tS8 : (x + S + 8#64).toNat = x.toNat + S.toNat + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
    have tN : ∀ d : Word, d.toNat < 32 → (x + N + d).toNat = x.toNat + N.toNat + d.toNat := by
      intro d hd; rw [BitVec.toNat_add, BitVec.toNat_add]; omega
    have hH2c := Tlsf.headAddr_inCtl hc (Tlsf.flOf_lt hRok) (Tlsf.slOf_lt (S - N))
    have hSL2c := Tlsf.slBm_inCtl hc (Tlsf.flOf_lt hRok)
    have hH2 : Tlsf.upd (Tlsf.popMem (s0.getReg .x10)
        (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) fl sl (xs.headD 0#64))
        (x + S + 8#64) (x + N)
        (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) ≠ 0#64 →
        ∃ d ∈ bs, d.used = false ∧ d.a = Tlsf.upd (Tlsf.popMem (s0.getReg .x10)
          (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) fl sl (xs.headD 0#64))
          (x + S + 8#64) (x + N)
          (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) := by
      intro hz
      rw [Tlsf.upd_ne (Tlsf.ne_nat (by have := hH2c.2; simp only [Tlsf.ctlSize] at this; omega)),
        hsh2.heads _ _ (Tlsf.flOf_lt hRok) (Tlsf.slOf_lt (S - N))] at hz ⊢
      cases hl : Tlsf.Lset L fl sl xs (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)) with
      | nil => rw [hl] at hz; exact (hz rfl).elim
      | cons z zs =>
        have hzm : z ∈ Tlsf.Lset L fl sl xs (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)) := by
          rw [hl]; exact List.mem_cons_self ..
        obtain ⟨_, d, hd, hda, hdu, _⟩ := hsh2.members _ _ z hzm
        exact ⟨d, hd, hdu, hda⟩
    -- Each written doubleword is the allocator's and not the lock.
    have k1 : Mine (s0.getReg .x10) bs (x + S + 8#64) ∧ x + S + 8#64 ≠ s0.getReg .x10 :=
      ⟨.inr ⟨c, hcb, .inl (by rw [hca])⟩, Tlsf.ne_nat (by omega)⟩
    have k2 : Mine (s0.getReg .x10) bs
        (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N))) ∧
        Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf (S - N)) (Tlsf.slOf (S - N)) ≠
          s0.getReg .x10 :=
      ⟨mineC _ hH2c, Tlsf.ne_nat (by have := hH2c.1; omega)⟩
    have kN : ∀ d : Word, d.toNat < 32 →
        Mine (s0.getReg .x10) bs (x + N + d) ∧ x + N + d ≠ s0.getReg .x10 := fun d hd =>
      ⟨mineX _ (by rw [tN d hd]; omega) (by rw [tN d hd]; omega),
        Tlsf.ne_nat (by rw [tN d hd]; omega)⟩
    have k7 : ∀ h2 : Word, h2 ≠ 0#64 → (∃ d ∈ bs, d.used = false ∧ d.a = h2) →
        Mine (s0.getReg .x10) bs (h2 + 0x18#64) ∧ h2 + 0x18#64 ≠ s0.getReg .x10 := by
      rintro h2 - ⟨d, hd, hdu, rfl⟩
      obtain ⟨_, hdb, hd40⟩ := hsh0.blkA hd
      have := Tlsf.Shape.sz_ge (hsh0.blk hd).2.2.2.2
      have := (hsh0.blk hd).2.2.1
      have t := Tlsf.toNat_add_lt (c := 0x18#64) hd40 (by decide)
      rw [show (0x18#64 : Word).toNat = 24 from rfl] at t
      exact ⟨.inr ⟨d, hd, .inr ⟨hdu, by omega, by omega⟩⟩, Tlsf.ne_nat (by omega)⟩
    have k0 : Mine (s0.getReg .x10) bs (x + N) ∧ x + N ≠ s0.getReg .x10 := by
      have := kN 0#64 (by decide); simpa using this
    have k8 := mineC _ hFLc
    have k9 := mineC _ hSL2c
    have ne8 : Tlsf.flBm (s0.getReg .x10) ≠ s0.getReg .x10 :=
      Tlsf.ne_nat (by have := hFLc.1; omega)
    have ne9 : Tlsf.slBm (s0.getReg .x10) (Tlsf.flOf (S - N)) ≠ s0.getReg .x10 :=
      Tlsf.ne_nat (by have := hSL2c.1; omega)
    have splitSelf : splitPre (s0.getReg .x10) (Tlsf.popMem (s0.getReg .x10)
        (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) fl sl (xs.headD 0#64)) x S N
        (s0.getReg .x10) = 0xffffffffffffffff#64 := by
      rw [splitPre_other k1.2.symm k2.2.symm k0.2.symm
        (kN 8#64 (by decide)).2.symm (kN 0x10#64 (by decide)).2.symm (kN 0x18#64 (by decide)).2.symm
        (fun hz => (k7 _ hz (hH2 hz)).2.symm) ne8.symm ne9.symm]
      · exact popSelf
    refine ⟨_, _, finRep hshF splitSelf hxs (notKey N _ _ _ hshF hb1 hN2 hptrN),
      fun c hc hu => ?_, fun a ha => ?_, .inr ⟨_, hb1, rfl, rfl,
      ⟨S, hb, by rw [BitVec.le_def]; rw [BitVec.lt_def] at hlt; omega⟩, hp16, hpw, hpN, hpal,
      hsmall, fun hal => finPtr _ _ hal⟩⟩
    · rcases keepUsed c hc hu with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    · have ne : ∀ k, Mine (s0.getReg .x10) bs k → a ≠ k := fun k hk e => ha (by rw [e]; exact hk)
      rw [finOther _ _ a ha, splitPre_other (ne _ k1.1) (ne _ k2.1) (ne _ k0.1)
        (ne _ (kN 8#64 (by decide)).1) (ne _ (kN 0x10#64 (by decide)).1)
        (ne _ (kN 0x18#64 (by decide)).1) (fun hz => ne _ (k7 _ hz (hH2 hz)).1) (ne _ k8)
        (ne _ k9)]
      exact popOther a ha

/-- **rlsf's `alloc` (`0x7801c18c`).** Entered with a well-formed heap at `a0`, the de Bruijn
    table in place, a power-of-two alignment in `a1` and a size in `a2`, a frame of 48 bytes
    on the stack: it returns, with the callee-saved registers and the code as they were, the
    heap well formed again with every used block kept, nothing changed outside the allocator's
    own doublewords, and either null or a granted block. It never panics: the lock is free. -/
theorem spec {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 : MachineState} {base : Word}
    {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    (hpc : s0.pc = 0x7801c18c#64) (hcode : s0.code = C)
    (hrep : Tlsf.Rep (s0.getReg .x10) base s0.getMem bs L) (hro : RoOk s0.getMem)
    (hsp : 0x30 ≤ (s0.getReg .x2).toNat) (hstk : (s0.getReg .x2).toNat ≤ 0x78000000)
    (hspc : 0x78002000 ≤ (s0.getReg .x10).toNat)
    (hp : s0.getReg .x11 &&& (s0.getReg .x11 - 1#64) = 0#64) (hp0 : s0.getReg .x11 ≠ 0#64)
    (hk : ∀ t, Done s0 base bs t → SafeN G n P t) : SafeN G n P s0 := by
  have hself' : ¬ InFrame (s0.getReg .x2) (s0.getReg .x10) := off_frame (by omega)
  obtain ⟨hlock, hsh0⟩ := Tlsf.rep_iff.mp hrep
  -- With the lock taken.
  have hsh1 := hsh0.congr (m' := Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64)
    fun a ha => Tlsf.upd_ne (key_ne_self hsh0 ha)
  have hro1 : RoOk (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) := by
    refine ⟨by rw [Tlsf.upd_ne (Tlsf.ne_nat (by simp; omega))]; exact hro.1, fun j hj => ?_⟩
    have : (0x78001540#64 + j <<< 3).toNat < 0x78002000 := by
      have : ∀ j : BitVec 64, j < 8#64 → 0x78001540#64 + j <<< 3 < 0x78002000#64 := by
        intro j h; bv_decide
      have := this j hj; rw [BitVec.lt_def] at this; simpa using this
    rw [Tlsf.upd_ne (Tlsf.ne_nat (by omega))]; exact hro.2 j hj
  -- Null: the lock released, memory as it was.
  have hnull : ∀ y, St s0 (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) y →
      y.pc = 0x7801c2ec#64 → y.getReg .x19 = 0#64 → SafeN G n P y := by
    intro y hy hpcy h19
    refine exit hy hpcy hsp hself' fun t ht => hk t ⟨_, _, ht, bs, L, ?_, fun b hb _ => hb, ?_,
      .inl h19⟩
    · refine (congrArg (fun m => Tlsf.Rep (s0.getReg .x10) base m bs L)
        (funext fun a => ?_ : _ = s0.getMem)).mpr hrep
      by_cases e : a = s0.getReg .x10
      · rw [e, Tlsf.upd_same, Tlsf.upd_same, hlock]; rfl
      · rw [Tlsf.upd_ne e, Tlsf.upd_ne e]
    · intro a _
      by_cases e : a = s0.getReg .x10
      · rw [e, Tlsf.upd_same, Tlsf.upd_same, hlock]; rfl
      · rw [Tlsf.upd_ne e, Tlsf.upd_ne e]
  refine entrySeg hpc hcode hlock hsp hself' hnull ?_
  intro y a hs hpcy h10 h19 ha hov1 hov2
  subst ha
  obtain ⟨hr32, _, ha16⟩ := req_ok hov1 hov2
  have hfs : Tlsf.flSearch (reqOf (s0.getReg .x12 +
      if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64)) < 64#64 := by
    have : ∀ v : BitVec 64, v < 60#64 → v < 64#64 := by intro v h; bv_decide
    exact this _ (Tlsf.flSearch_lt hr32)
  have hfound : ∀ y' fl sl, St s0 (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64) y' →
      y'.pc = 0x7801c378#64 → y'.getReg .x10 = s0.getReg .x10 + 0x8000#64 →
      y'.getReg .x12 = fl → y'.getReg .x13 = sl → fl < 64#64 → sl < 64#64 → L fl sl ≠ [] →
      (Tlsf.flSearch (reqOf (s0.getReg .x12 +
          (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64))) < fl ∨
        (Tlsf.flSearch (reqOf (s0.getReg .x12 +
            (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64))) = fl ∧
          (Tlsf.searchRaw (reqOf (s0.getReg .x12 +
            (if 16#64 < s0.getReg .x11 then s0.getReg .x11 else 16#64))) &&& 63#64) ≤ sl)) →
      SafeN G n P y' :=
    fun y' fl sl hs' hpc' q10 q12 q13 hfl hsl hL hlex =>
      afterFound hs' hpc' hrep hsp hstk (by omega) hp hp0 hov1 hov2 q10 q12 q13 hfl hsl hL hlex hk
  refine classSearch hs hpcy h10 ha16 (by
    have : ∀ v : BitVec 64, ¬ 0xffffffffffffffe0#64 < v → v ≤ 0xffffffffffffffe0#64 := by
      intro v h; bv_decide
    exact this _ hov2) h19 hnull ?_
  intro y2 hs2 hpc2 q11 q12 q13 q14
  exact slLookup hs2 hpc2 hsh1 hro1 hstk (by omega) hfs q11 q12 q13 q14 hfound
    fun y3 hs3 hpc3 r10 r11 r14 =>
      flLookup hs3 hpc3 hsh1 hro1 hstk (by omega) r10 r11 r14 hnull hfound

end Cases.Zip2005.Runtime.Alloc
