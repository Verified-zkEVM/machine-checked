/-
  Cases.Zip2005.Run.Ro

  What the run's carried facts give the runtime's preconditions (milestone M1): the image's
  words in the read-only segment (`ro_memAt`, from `RoImage`), so the frame checker's
  protected regions at their load values (`prot`, with the hooks from `HeapAt`), and the
  allocator's de Bruijn table (`roOk`).
-/

import Cases.Zip2005.Run.Heap
import MachineChecked.RiscV.Sym.LoadRo
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.RiscV.Check Cases.Zip2005
  Cases.Zip2005.Image

/-- **The read-only segment, word by word**, from the carried `RoImage`. -/
theorem ro_memAt {s : MachineState} (h : RoImage Ro.layout s) {a : Word} (ha8 : a.toNat % 8 = 0)
    (h1 : 0x78000000 ≤ a.toNat) (h2 : a.toNat < 0x78015938) : s.getMem a = Layout.image.memAt a :=
  memAt_of_roImage Loaded.dataWF Ro.layout (k := Ro.roIdx) rfl rfl Ro.roChunk_eq
    (by decide +kernel) (by decide +kernel) h ha8 h1 h2

/-- A word of `.rodata` (data chunk 0), by its index. -/
theorem ro_word {s : MachineState} (h : RoImage Ro.layout s) (j : Nat) (hj : 8 * j < 0x15938)
    {a v : Word} (ha : Data_0.chunk.base + BitVec.ofNat 64 (8 * j) = a)
    (hv : Data_0.chunk.wordAt j = v) (hjs : j < Data_0.chunk.size) : s.getMem a = v := by
  have hb : Data_0.chunk.base.toNat = 0x78000000 := rfl
  have hat : a.toNat = 0x78000000 + 8 * j := by
    rw [← ha, BitVec.toNat_add, hb, BitVec.toNat_ofNat]; omega
  rw [ro_memAt h (by omega) (by omega) (by omega), ← ha,
    Image.memAt_chunk (k := 0) Loaded.dataWF rfl hjs, hv]

/-- **The allocator's table** (`Alloc.RoOk`): the de Bruijn constant and its eight words. -/
theorem roOk {s : MachineState} (h : RoImage Ro.layout s) : Runtime.Alloc.RoOk s.getMem := by
  refine ⟨ro_word h 127 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    fun j hj => ?_⟩
  have : j = 0#64 ∨ j = 1#64 ∨ j = 2#64 ∨ j = 3#64 ∨ j = 4#64 ∨ j = 5#64 ∨ j = 6#64 ∨ j = 7#64 := by
    bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ro_word h 680 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ro_word h 681 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ro_word h 682 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ro_word h 683 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ro_word h 684 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ro_word h 685 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ro_word h 686 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact ro_word h 687 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The protected regions at their load values**: `.rodata` from `RoImage`, the two hooks
    from `HeapAt`. -/
theorem prot {L : List (Word × Nat)} {s : MachineState} (hro : RoImage Ro.layout s)
    (hh : HeapAt L s) {a : Word} (hal : Aligned a) (hp : Contract.env.InProt a) :
    s.getMem a = Contract.env.init a := by
  have h8 : a.toNat % 8 = 0 := by
    unfold Aligned at hal
    have := congrArg BitVec.toNat hal
    rw [BitVec.toNat_and] at this
    have h7 : (7#64 : Word).toNat = 2 ^ 3 - 1 := rfl
    rw [h7, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  have hk := hh.holds.1
  rcases Runtime.Entry.prot_range hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ro_memAt hro h8 (by omega) h2
  · have : a = 0x78048920#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this; exact hk _ (by simp [hookKeys])
  · have : a = 0x78048948#64 ∨ a = 0x78048950#64 ∨ a = 0x78048958#64 := by
      have : a.toNat = 0x78048948 ∨ a.toNat = 0x78048950 ∨ a.toNat = 0x78048958 := by omega
      rcases this with e | e | e
      · exact .inl (BitVec.eq_of_toNat_eq (by simp [e]))
      · exact .inr (.inl (BitVec.eq_of_toNat_eq (by simp [e])))
      · exact .inr (.inr (BitVec.eq_of_toNat_eq (by simp [e])))
    rcases this with rfl | rfl | rfl <;> exact hk _ (by simp [hookKeys])

end Cases.Zip2005.Run
