/-
  Cases.Zip2005.Statics

  zip-2005's protected statics (phase C3).

  The `Env` the table is checked against protects `.rodata`/`.eh_frame` and two statics the
  guest never writes: `std::alloc::HOOK` and `std::panicking::HOOK`, set only by
  `set_alloc_error_hook` and `set_hook`/`take_hook`, which nothing calls (`Runtime/STATICS.tsv`;
  `infer-contracts` refuses any interface whose footprint would write them). Both sit in
  `.bss`, so their load value is zero: no hook installed, the default ones run.

  `HooksUnset` is that part of `StaticsOk`. It holds at load, at the entry of every call that
  meets its precondition, and at the return of every verified call: the generic
  `Pre.regionOk`/`Post.regionOk` with the load values below.
-/

import Cases.Zip2005.Loaded
import Cases.Zip2005.Regions
import Cases.Zip2005.Contract.Table
import AsmVerif.RiscV.Check.Statics

namespace Cases.Zip2005.Statics

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Check Cases.Zip2005

/-- `std::alloc::HOOK`: one doubleword. -/
def allocHook : Region := { base := 0x78048920, len := 8 }

/-- `std::panicking::HOOK`: three doublewords. -/
def panicHook : Region := { base := 0x78048948, len := 0x18 }

theorem allocHook_prot : (allocHook.base, allocHook.len) ∈ Contract.env.prot := by
  simp [Contract.env, allocHook]

theorem panicHook_prot : (panicHook.base, panicHook.len) ∈ Contract.env.prot := by
  simp [Contract.env, panicHook]

/-- Both hooks are statics: inside the `.data`/`.bss` region of the layout. -/
theorem hooks_in_statics :
    Regions.statics.base.toNat ≤ allocHook.base.toNat ∧ allocHook.hi ≤ Regions.statics.hi ∧
    Regions.statics.base.toNat ≤ panicHook.base.toNat ∧ panicHook.hi ≤ Regions.statics.hi := by
  decide

/-! ## Load values: zero, from `.bss` -/

/-- A doubleword of the statics chunk's zero tail reads back as zero. -/
theorem memAt_bss {j : Nat} (hj1 : Image.Data_2.chunk.words.length ≤ j)
    (hj2 : j < Image.Data_2.chunk.size) :
    Loaded.image.memAt (Image.Data_2.chunk.base + BitVec.ofNat 64 (8 * j)) = 0 := by
  rw [Image.memAt_chunk (k := 2) (c := Image.Data_2.chunk) Loaded.dataWF rfl hj2]
  simp [DataChunk.wordAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj1]

theorem words_len : Image.Data_2.chunk.words.length = 1 := by decide +kernel
theorem chunk_size : Image.Data_2.chunk.size = 4205 := by decide +kernel
theorem chunk_base : Image.Data_2.chunk.base = 0x78040618#64 := rfl

/-- An aligned key of a region lies on its doubleword grid. -/
theorem key_eq {R : Region} {a : Word} (hal : Aligned a) (hm : R.Mem a) (hb : R.base.toNat % 8 = 0) :
    ∃ i, i < (R.len + 7) / 8 ∧ a = R.base + BitVec.ofNat 64 (8 * i) := by
  rw [aligned_iff] at hal
  obtain ⟨hlo, hhi⟩ := hm
  unfold Region.hi at hhi
  refine ⟨(a.toNat - R.base.toNat) / 8, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Every key of a hook region is a zero of the `.bss` tail. -/
theorem hook_zero {R : Region} (hb : R.base.toNat % 8 = 0)
    (hR : ∀ i, i < (R.len + 7) / 8 → ∃ j, 1 ≤ j ∧ j < 4205 ∧
      R.base + BitVec.ofNat 64 (8 * i) = Image.Data_2.chunk.base + BitVec.ofNat 64 (8 * j))
    {a : Word} (hal : Aligned a) (hm : R.Mem a) : Loaded.image.memAt a = 0 := by
  obtain ⟨i, hi, rfl⟩ := key_eq hal hm hb
  obtain ⟨j, hj1, hj2, he⟩ := hR i hi
  rw [he]
  exact memAt_bss (by rw [words_len]; exact hj1) (by rw [chunk_size]; exact hj2)

theorem allocHook_zero {a : Word} (hal : Aligned a) (hm : allocHook.Mem a) :
    Loaded.image.memAt a = 0 :=
  hook_zero (by decide) (fun i hi => by
    have hi : i = 0 := by simp [allocHook] at hi; omega
    subst hi
    exact ⟨4193, by omega, by omega, by simp only [allocHook, chunk_base]; decide⟩) hal hm

theorem panicHook_zero {a : Word} (hal : Aligned a) (hm : panicHook.Mem a) :
    Loaded.image.memAt a = 0 :=
  hook_zero (by decide) (fun i hi => by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by simp [panicHook] at hi; omega
    rcases hi with rfl | rfl | rfl
    · exact ⟨4198, by omega, by omega, by simp only [panicHook, chunk_base]; decide⟩
    · exact ⟨4199, by omega, by omega, by simp only [panicHook, chunk_base]; decide⟩
    · exact ⟨4200, by omega, by omega, by simp only [panicHook, chunk_base]; decide⟩) hal hm

/-! ## `HooksUnset`: at load, and across every verified call -/

/-- No hook is installed: both hook statics hold zero. -/
def HooksUnset (s : MachineState) : Prop :=
  RegionOk allocHook (fun _ => 0) s ∧ RegionOk panicHook (fun _ => 0) s

/-- At load. -/
theorem hooksUnset_load (input : List (BitVec 8)) : HooksUnset (Loaded.image.state input) :=
  ⟨fun _ hal hm => allocHook_zero hal hm, fun _ hal hm => panicHook_zero hal hm⟩

/-- At the entry of every call whose precondition holds. -/
theorem hooksUnset_of_pre {C : Word → Option Instr} {σ : Iface} {s : MachineState}
    (hpre : Pre Contract.env C σ s) : HooksUnset s :=
  ⟨fun a hal hm => (Pre.regionOk allocHook_prot hpre a hal hm).trans (allocHook_zero hal hm),
   fun a hal hm => (Pre.regionOk panicHook_prot hpre a hal hm).trans (panicHook_zero hal hm)⟩

/-- At the return of every verified call. -/
theorem hooksUnset_of_post {C : Word → Option Instr} {σ : Iface} {s t : MachineState}
    (hpre : Pre Contract.env C σ s) (hpost : Post Contract.env σ s t) : HooksUnset t :=
  ⟨fun a hal hm => (Post.regionOk Contract.env_wf allocHook_prot hpre hpost a hal hm).trans
      (allocHook_zero hal hm),
   fun a hal hm => (Post.regionOk Contract.env_wf panicHook_prot hpre hpost a hal hm).trans
      (panicHook_zero hal hm)⟩

end Cases.Zip2005.Statics
