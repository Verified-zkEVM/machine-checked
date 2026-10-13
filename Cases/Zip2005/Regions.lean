/-
  Cases.Zip2005.Regions

  The zip-2005 guest's address space, named and proved disjoint (phase C1).

  The sections, from the loaded image's program headers (`llvm-readelf -S`):

    * stack      below  0x78000000  (grows down; `__start` sets `sp` from the image)
    * .rodata    0x78000190  size 0x141cb   (read-only constants)
    * .eh_frame  0x78014360  size 0x15d8    (unwind tables; read-only)
    * .text      0x78016938  size 0x28cdc   (code)
    * .data      0x78040618  size 0x8        (one initialised static)
    * .bss       0x78040620  size 0x8360     (zero-initialised statics, up to `_end`)
    * heap       0x78048980  up to 0x1C00000000 (the TLSF arena; `__start` hands
                 `Heap::init` exactly `[_end, 7 << 34)`)
    * beyond     0x1C00000000 up to SP1_MAX_MEMORY (unused by the image)

  `.rodata` and `.eh_frame` are one contiguous protected region `[0x78000190, 0x78015938)`,
  the `Env.prot` the checker runs against. The statics `.data`/`.bss` are `[0x78040618,
  0x78048980)`. The theorem below is that stack, program, statics and heap occupy separate,
  non-wrapping parts of the address space, all below `SP1_MAX_MEMORY`.
-/

import AsmVerif.RiscV.Check.Region

namespace Cases.Zip2005.Regions

open RiscvZkvm.Rv64 AsmVerif.RiscV.Check

/-- Where the stack lives: `[0, 0x78000000)`, below everything the image places. -/
def stack : Region := { base := 0, len := 0x78000000 }

/-- Read-only data and unwind tables: the checker's protected region. -/
def rodata : Region := { base := 0x78000190, len := 0x157a8 }

/-- The code. -/
def text : Region := { base := 0x78016938, len := 0x28cdc }

/-- The mutable statics, `.data` and `.bss` together, up to `_end`. -/
def statics : Region := { base := 0x78040618, len := 0x8368 }

/-- The heap arena: what `__start` gives `Heap::init`, `[_end, 7 << 34)`. -/
def heap : Region := { base := 0x78048980, len := 0x1B87FB7680 }

/-- The layout, in address order. -/
def all : List Region := [stack, rodata, text, statics, heap]

/-- The protected region matches the `rodata` region. -/
theorem prot_eq_rodata : (rodata.base, rodata.len) = (0x78000190#64, 0x157a8) := rfl

/-- **C1: the regions are pairwise disjoint and non-wrapping.** -/
theorem all_ok : Region.pairwiseOk all = true := by decide

/-- Every region ends at or below SP1's memory bound. -/
theorem all_within : all.all (fun r => decide (r.hi ≤ SP1_MAX_MEMORY)) = true := by decide

/-- The heap ends at `7 << 34`, the bound `__start` passes to `Heap::init`, below SP1's. -/
theorem heap_top : heap.hi = 7 <<< 34 ∧ heap.hi < SP1_MAX_MEMORY := by decide

/-- The statics lie directly below the heap, with no gap. -/
theorem statics_abuts_heap : statics.hi = heap.base.toNat := by decide

/-- Any two distinct regions of the layout are disjoint: a usable form of `all_ok`. -/
theorem disjoint {r s : Region} (hr : r ∈ all) (hs : s ∈ all) (hne : r ≠ s) :
    r.Disjoint s = true :=
  Region.pairwiseOk_disjoint all_ok hr hs hne

/-- No address lies in two different regions. -/
theorem no_overlap {r s : Region} (hr : r ∈ all) (hs : s ∈ all) (hne : r ≠ s) {a : Word}
    (har : r.Mem a) (has : s.Mem a) : False :=
  Region.not_mem_of_disjoint (disjoint hr hs hne) har has

end Cases.Zip2005.Regions
