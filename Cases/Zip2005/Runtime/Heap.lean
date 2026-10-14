import AsmVerif.RiscV.Sym.Ro
import Cases.Zip2005.Image.Ro

/-!
# The allocator's footprint

The guest's global allocator is `embedded_alloc`'s TLSF heap (`sp1_zkvm::allocators::embedded`):
its control block is the static `INNER_HEAP` at `0x78040620` (`0x8210` bytes) and its arena runs
from `_end = 0x78048980` to `7 << 34` (`embedded::init`). An allocation or deallocation writes the
control block, the block's own header and footer, and the headers of physically adjacent blocks
(the arena's sentinel included), so a caller's frame condition names the whole range
`[0x78040620, 0x1c00000000)` as the allocator's write set. Nothing a function proves about the
heap's *contents* survives such a call unless it is the call's own postcondition.

`alloc`/`dealloc` are not stepped by the executor: each caller states the contract it needs as a
hypothesis in continuation form (ledger finding T2), to be discharged against the TLSF code over
the concrete heap state of the run.
-/

namespace Cases.Zip2005

open Cases.Zip2005.Image

open RiscvZkvm.Rv64 AsmVerif.RiscV.Sym

/-- `INNER_HEAP`, the start of the allocator's write set. Statements use the literals
`0x78040620#64` and `14780694332` (cells to the arena's end `0x1c00000000`) so that the executor's
arithmetic sees them; these names are documentation. -/
def heapBase : Word := 0x78040620#64

/-- Cells from `heapBase` to the arena's end `0x1c00000000`. -/
def heapCells : Nat := 14780694332

theorem heapCells_eq : 0x78040620 + 8 * heapCells = 0x1c00000000 := by decide

/-- The allocator's write set, as a frame entry. -/
theorem heapOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

/-- A stack frame lies below the image, the heap above it. -/
theorem Disjoint.heap_frame {sp : Word} {room n : Nat} (h : StackOk Ro.layout room sp) (hn : 8 * n ≤ room) :
    Disjoint 0x78040620#64 14780694332 (sp - BitVec.ofNat 64 (8 * n)) n := by
  obtain ⟨_, h2, h3⟩ := h
  rw [Ro.layout_stackTop] at h3
  have hsp := sp.isLt
  have hn' : 8 * n < 2 ^ 64 := by omega
  have e : (sp - BitVec.ofNat 64 (8 * n)).toNat = sp.toNat - 8 * n := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn']; omega
  have hb : (0x78040620#64).toNat = 0x78040620 := rfl
  refine ⟨Or.inr ?_, ?_, ?_⟩
  · rw [e, hb]; omega
  · rw [hb]; decide
  · rw [e]; omega

/-! ## The write set without the statics

The allocator writes its control block (`0x78040620`, 4162 cells) and its arena (`0x78048980` to
`0x1c00000000`, 14780690128 cells), never the statics between them (`[0x78048830, 0x78048980)`:
the public-values hasher, `FP_TABLES`, the panic hooks and counts). A frame names the two pieces,
so that a caller keeps what it knows about the statics across the call. `FP_TABLES`
(`0x780488a8`, 10 cells) is written once, by its lazy initialisation from `main`; `main`'s frames
name it as a third piece. -/

theorem ctlOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

theorem arenaOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

theorem fpTablesOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 10 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

/-- A block off the whole heap range is off the control block. -/
theorem _root_.Asm.Disjoint.ctl_of_heap {b : Word} {n : Nat} (h : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n) :
    AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 4162 b n := by
  unfold AsmVerif.RiscV.Sym.Disjoint at *
  simp only [BitVec.toNat_ofNat] at *
  omega

/-- A block off the whole heap range is off the arena. -/
theorem _root_.Asm.Disjoint.arena_of_heap {b : Word} {n : Nat} (h : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n) :
    AsmVerif.RiscV.Sym.Disjoint 0x78048980#64 14780690128 b n := by
  unfold AsmVerif.RiscV.Sym.Disjoint at *
  simp only [BitVec.toNat_ofNat] at *
  omega

/-- A block in the arena is covered by the arena entry. -/
theorem covers_arena {b : Word} {n : Nat} (hlo : 0x78048980 ≤ b.toNat)
    (hhi : b.toNat + 8 * n ≤ 0x1c00000000) : Covers 0x78048980#64 14780690128 b n := by
  unfold Covers
  simp only [BitVec.toNat_ofNat]
  omega

end Cases.Zip2005
