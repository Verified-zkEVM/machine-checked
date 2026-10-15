import Cases.Zip2005.Top.Assumptions
import Cases.Zip2005.Top.Load
import Cases.Zip2005.Runtime.Entry
import Cases.Zip2005.Run.Heap

/-!
# From the ELF entry

`guest_elf_run`: a run of the loaded image (`start I`) from the ELF's entry point (`_start`,
`0x7801bcd0`) is `SafeN G n (GuestAccepts I)`. The run to `main` is `Runtime.Entry.entry` (phase
D1), which fixes all of memory at `main`'s entry: the image's, with `__start`'s 31 stores. So
`main`'s entry state (ledger A2) is no longer assumed but read off it: its return address and
stack, the hint area's bump pointer `0x1c00000000` and `FP_TABLES` uninitialised (`.data`/`.bss`,
which no store touches), `.rodata`, and the heap invariant, `HeapAt []`: one free block over the
arena, the hooks unset, the hasher set up (`Run.mainEntry_heapAt`). What stays assumed is
`RunContracts` (code and runtime contracts), and of the input that it fits the hint area
(`hIfit`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.Top

set_option autoImplicit false

/-- The cells `_start` and `__start` write before `main`, one doubleword each. -/
noncomputable def entryWrites : List (Word × Nat) := Runtime.Entry.stores.map fun p => (p.1, 1)

/-- At `main`'s entry, memory is the loaded image's but for `__start`'s stores. -/
theorem entry_unchanged {I : List (BitVec 8)} {t : MachineState} (h : Runtime.Entry.MainEntry I t) :
    Unchanged entryWrites (start I) t := fun a ha => by
  rw [h.2.2.2.2.2.1 a, Runtime.Entry.initMem, Runtime.Entry.lookup_none]
  · rfl
  · intro p hp e
    refine ha (p.1, 1) (List.mem_map_of_mem hp) ?_
    show p.1.toNat ≤ a.toNat ∧ a.toNat < p.1.toNat + 8 * 1
    rw [e]; omega

/-- The stores miss `.rodata`, the hint-area pointer and `FP_TABLES`, and none wraps. -/
theorem entryWrites_apart : ∀ r ∈ entryWrites,
    (r.1.toNat + 8 * r.2 ≤ 0x78000000 ∨ 0x78015938 ≤ r.1.toNat) ∧
    (r.1.toNat + 8 * r.2 ≤ 0x78040618 ∨ 0x78040620 ≤ r.1.toNat) ∧
    (r.1.toNat + 8 * r.2 ≤ 0x780488a8 ∨ 0x780488f8 ≤ r.1.toNat) ∧ r.1.toNat + 8 * r.2 ≤ 2 ^ 64 := by
  simp only [entryWrites, Runtime.Entry.stores, List.map_cons, List.map_nil, List.mem_cons,
    List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, BitVec.toNat_ofNat]
  norm_num

set_option maxRecDepth 20000 in
theorem guest_elf_run {G : MachineState → Prop} {n : Nat} (I : List (BitVec 8))
    (hR : RunContracts G n (start I) I) (hIl : I.length < 2 ^ 60)
    (hIfit : I.length + 1416 ≤ 0x400000000) :
    SafeN G n (Cases.Zip2005.Top.GuestAccepts I) (start I) :=
  Runtime.Entry.entry I fun t h => by
    have hu := entry_unchanged h
    have hW := entryWrites_apart
    have hB : Region 0x78040618#64 [0x1c00000000#64] t :=
      (data2_word I 0 (by decide +kernel) (by decide) (by decide +kernel)).of_unchanged' hu (n := 1) rfl
        fun r hr => by
          have := (hW r hr).2.1; have := (hW r hr).2.2.2; unfold AsmVerif.RiscV.Sym.Disjoint; simp only [BitVec.toNat_ofNat]; omega
    have hT0 : Region 0x780488a8#64 [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] t :=
      (data2_fp_tables I).of_unchanged' hu (n := 10) rfl fun r hr => by
        have := (hW r hr).2.2.1; have := (hW r hr).2.2.2; unfold AsmVerif.RiscV.Sym.Disjoint; simp only [BitVec.toNat_ofNat]; omega
    exact guest_accepting_run' t 0x7801bea0#64 0x77fffff0#64 0x1c00000000#64 I
      { toRunContracts := hR.of_code_eq h.2.1
        hpc := h.1
        hro := (roImage (start_getMem I)).of_unchanged hu fun r hr => by
          have := (hW r hr).1; simp only [Ro.layout_roBase, Ro.layout_roBytes]; omega
        hheap := Run.mainEntry_heapAt h
        hra := h.2.2.1
        hra1 := by decide
        hsp := h.2.2.2.1
        hstk := ⟨by decide, by decide, by decide⟩
        hI := h.2.2.2.2.2.2
        hIl := hIl
        hB := hB
        hT0 := hT0
        hb := by decide
        hokJ := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
        hbI := by simp only [BitVec.toNat_ofNat]; omega }

end Cases.Zip2005
