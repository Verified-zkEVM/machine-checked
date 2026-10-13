/-
  Cases.Zip2005.Runtime.Tlsf.Model

  rlsf's TLSF heap, as memory holds it (phase D4).

  The arena is a chain of blocks in address order, ending in a sentinel. A block's first
  doubleword is its header — its size (a multiple of 32) with bit 0 set when it is used and
  bit 1 on the sentinel — and its second points at the physically previous block (zero for
  the first). A free block also links into the free list of its size class: the doubleword
  at `+0x10` is the next free block, at `+0x18` the previous (zero at the ends). The
  heap's control block (`self`, `INNER_HEAP`) holds a lock word, the 64 × 64 list heads and
  two levels of bitmaps saying which lists are non-empty.

  `Rep self base m bs L`: memory `m` holds the heap whose blocks, from `base`, are `bs`, with
  free lists `L`. `HeapOk` hides `bs` and `L`.
-/

import Cases.Zip2005.Runtime.Tlsf.Class

namespace Cases.Zip2005.Runtime.Tlsf

abbrev Word := BitVec 64

/-- A block: its address, its size, and whether it is used or the sentinel. -/
structure Blk where
  a : Word
  sz : Word
  used : Bool
  last : Bool := false
  deriving DecidableEq, Repr

/-- The header word: the size with the used and sentinel bits. -/
def Blk.hdr (b : Blk) : Word :=
  b.sz ||| (if b.used then 1#64 else 0#64) ||| (if b.last then 2#64 else 0#64)

/-- The physical chain from address `a`, whose predecessor is `p`, ending in the sentinel. -/
def Chain (m : Word → Word) : Word → Word → List Blk → Prop
  | _, _, [] => False
  | a, p, b :: bs => b.a = a ∧ m a = b.hdr ∧ m (a + 8#64) = p ∧ b.sz &&& 31#64 = 0#64 ∧
      SizeOk b.sz ∧
      if b.last then bs = [] ∧ b.sz = 32#64 ∧ b.used = true
      else Chain m (a + b.sz) a bs

/-- A free list's links, from a predecessor `p`. -/
def Dll (m : Word → Word) : Word → List Word → Prop
  | _, [] => True
  | p, x :: xs => m (x + 0x18#64) = p ∧ m (x + 0x10#64) = xs.headD 0 ∧ Dll m x xs

/-- Where the control block keeps a list head and the bitmaps. -/
def headAddr (self f s : Word) : Word := self + 8#64 + f * 0x200#64 + s * 8#64
def slBm (self f : Word) : Word := self + 0x8008#64 + f * 8#64
def flBm (self : Word) : Word := self + 0x8208#64

/-- The control block's extent. -/
def ctlSize : Nat := 0x8210

/-- **The heap is well formed.** -/
structure Rep (ctl base : Word) (m : Word → Word) (bs : List Blk)
    (L : Word → Word → List Word) : Prop where
  lock : m ctl = 0
  chain : Chain m base 0 bs
  /-- The arena lies above the control block, below `2^40`, and does not wrap. -/
  layout : ctl.toNat + ctlSize ≤ base.toNat ∧ base &&& 31#64 = 0#64 ∧
    ∀ b ∈ bs, b.a.toNat + b.sz.toNat < 2 ^ 40
  heads : ∀ f s, f < 64#64 → s < 64#64 → m (headAddr ctl f s) = (L f s).headD 0
  links : ∀ f s, Dll m 0 (L f s)
  /-- Every free block is filed in its class, and only free blocks are. -/
  filed : ∀ b ∈ bs, b.used = false → b.a ∈ L (flOf b.sz) (slOf b.sz)
  members : ∀ f s x, x ∈ L f s →
    ∃ b ∈ bs, b.a = x ∧ b.used = false ∧ flOf b.sz = f ∧ slOf b.sz = s
  /-- Outside the 64 × 64 classes there are no lists. -/
  range : ∀ f s, (L f s ≠ []) → f < 64#64 ∧ s < 64#64
  nodup : ∀ f s, (L f s).Nodup
  slbm : ∀ f s, f < 64#64 → s < 64#64 →
    (m (slBm ctl f)).getLsbD s.toNat = !(L f s).isEmpty
  flbm : ∀ f, f < 64#64 →
    (m (flBm ctl)).getLsbD f.toNat = !(m (slBm ctl f) == 0)

/-- The heap at `self`, with arena from `base`, is well formed. -/
def HeapOk (self base : Word) (m : Word → Word) : Prop :=
  ∃ bs L, Rep self base m bs L

end Cases.Zip2005.Runtime.Tlsf
