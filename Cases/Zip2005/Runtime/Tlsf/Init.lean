/-
  Cases.Zip2005.Runtime.Tlsf.Init

  The heap `main` starts with is well formed (phase D4): `Heap::init` left one free block
  covering the arena, filed in class (31, 46), and the sentinel at `7 << 34 - 32`. This is
  the satisfiability witness for `HeapOk`: the run reaches it.
-/

import Cases.Zip2005.Runtime.Tlsf.Model
import Cases.Zip2005.Runtime.Entry

namespace Cases.Zip2005.Runtime.Tlsf

open RiscvZkvm.Rv64 Cases.Zip2005.Runtime.Entry

/-- `INNER_HEAP`, and the arena's first block. -/
def self0 : Word := 0x78040620#64
def base0 : Word := 0x78048980#64

/-- The blocks after `Heap::init`: one free block, then the sentinel. -/
def bs0 : List Blk :=
  [⟨0x78048980#64, 0x1b87fb7660#64, false, false⟩, ⟨0x1bffffffe0#64, 0x20#64, true, true⟩]

/-- Its one free list. -/
def L0 (f s : Word) : List Word := if f = 31#64 ∧ s = 46#64 then [0x78048980#64] else []

/-- Inside the control block. -/
def inCtl (k : Word) : Bool := decide (0x78040620 ≤ k.toNat) && decide (k.toNat < 0x78048830)

/-- The control-block doublewords the run wrote: the lock, one head, two bitmap words. -/
def ctlKeys : List Word := [0x78040620#64, 0x78044598#64, 0x78048720#64, 0x78048828#64]

theorem stores_ctl : (stores.map Prod.fst).all (fun k => !inCtl k || ctlKeys.contains k) = true := by
  decide +kernel

/-- An untouched doubleword of the control block reads zero at `main`'s entry. -/
theorem initMem_ctl {a : Word} (hlo : 0x78040620 ≤ a.toNat) (hhi : a.toNat < 0x78048830)
    (h8 : a.toNat % 8 = 0) (hk : a ∉ ctlKeys) : initMem a = 0 := by
  have hl : stores.lookup a = none := by
    apply lookup_none
    intro p hp he
    have := List.all_eq_true.mp stores_ctl p.1 (List.mem_map_of_mem hp)
    rw [← he] at this
    simp only [inCtl, Bool.not_and, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.contains_iff_mem] at this
    rcases this with (h | h) | h
    · omega
    · omega
    · exact hk h
  rw [initMem, hl]
  exact bss0 a ⟨by omega, by omega, by omega⟩

/-- Where the list heads and second-level bitmaps of the control block sit. -/
theorem headAddr_range {f s : Word} (hf : f < 64#64) (hs : s < 64#64) :
    0x78040628#64 ≤ headAddr self0 f s ∧ headAddr self0 f s < 0x78048628#64 ∧
      headAddr self0 f s &&& 7#64 = 0#64 := by
  simp only [headAddr, self0]; bv_decide

theorem headAddr_eq {f s : Word} (hf : f < 64#64) (hs : s < 64#64) :
    headAddr self0 f s = 0x78044598#64 ↔ (f = 31#64 ∧ s = 46#64) := by
  simp only [headAddr, self0]; bv_decide

theorem slBm_range {f : Word} (hf : f < 64#64) :
    0x78048628#64 ≤ slBm self0 f ∧ slBm self0 f < 0x78048828#64 ∧ slBm self0 f &&& 7#64 = 0#64 ∧
      (slBm self0 f = 0x78048720#64 ↔ f = 31#64) := by
  simp only [slBm, self0]; bv_decide

/-- A control-block doubleword at a position given by bounds. -/
theorem initMem_ctl' {a : Word} (hlo : 0x78040620#64 ≤ a) (hhi : a < 0x78048830#64)
    (h8 : a &&& 7#64 = 0#64) (hk : a ∉ ctlKeys) : initMem a = 0 := by
  have h8' : a.toNat % 8 = 0 := by
    have := congrArg BitVec.toNat h8
    rw [BitVec.toNat_and] at this
    rw [show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  exact initMem_ctl (by rw [BitVec.le_def] at hlo; simpa using hlo)
    (by rw [BitVec.lt_def] at hhi; simpa using hhi) h8' hk

theorem testBit_pow {k n : Nat} : (2 ^ k).testBit n = decide (k = n) := by
  rw [Nat.testBit_two_pow]

/-- **The heap at `main`'s entry is well formed.** -/
theorem rep_init {m : Word → Word} (hm : ∀ a, m a = initMem a) : Rep self0 base0 m bs0 L0 := by
  have hsl : ∀ f, f < 64#64 → m (slBm self0 f) = if f = 31#64 then 0x400000000000#64 else 0 := by
    intro f hf
    obtain ⟨h1, h2, h3, h4⟩ := slBm_range hf
    by_cases h : f = 31#64
    · subst h; rw [hm]; rfl
    · rw [if_neg h, hm]
      refine initMem_ctl' (by bv_decide) (by bv_decide) h3 ?_
      simp only [ctlKeys, List.mem_cons, List.mem_nil_iff, or_false, not_or]
      refine ⟨by bv_decide, by bv_decide, fun he => h (h4.mp he), by bv_decide⟩
  refine ⟨by rw [hm]; rfl, ?_, by decide, fun f s hf hs => ?_, fun f s => ?_, ?_, ?_, ?_, ?_,
    fun f s hf hs => ?_, fun f hf => ?_⟩
  · simp only [Chain, bs0, hm, SizeOk]
    decide +kernel
  · obtain ⟨h1, h2, h3⟩ := headAddr_range hf hs
    by_cases h : f = 31#64 ∧ s = 46#64
    · rw [(headAddr_eq hf hs).mpr h, hm]
      simp [L0, h]; rfl
    · rw [hm, initMem_ctl' (by bv_decide) (by bv_decide) h3]
      · simp [L0, h]
      · simp only [ctlKeys, List.mem_cons, List.mem_nil_iff, or_false, not_or]
        exact ⟨by bv_decide, fun he => h ((headAddr_eq hf hs).mp he), by bv_decide, by bv_decide⟩
  · unfold L0
    split
    · simp only [Dll, List.headD, hm]
      exact ⟨by rfl, by rfl, trivial⟩
    · trivial
  · intro b hb hu
    simp only [bs0, List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl
    · simp [L0]; decide
    · simp at hu
  · intro f s x hx
    unfold L0 at hx
    split at hx
    · rename_i h
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨_, List.mem_cons_self .., rfl, rfl, by rw [h.1]; decide, by rw [h.2]; decide⟩
    · simp at hx
  · intro f s h
    unfold L0 at h
    split at h
    · rename_i h'; rw [h'.1, h'.2]; decide
    · simp at h
  · intro f s
    unfold L0; split <;> simp
  · rw [hsl f hf]
    unfold L0
    by_cases h : f = 31#64
    · subst h
      simp only [if_true, true_and]
      rw [show (0x400000000000#64) = BitVec.ofNat 64 (2 ^ 46) from rfl, BitVec.getLsbD_ofNat,
        testBit_pow]
      have hs' : s.toNat < 64 := by rw [BitVec.lt_def] at hs; simpa using hs
      by_cases h46 : s = 46#64
      · subst h46; simp
      · have : s.toNat ≠ 46 := fun e => h46 (BitVec.eq_of_toNat_eq (by simpa using e))
        simp [h46, hs']; omega
    · simp [h]
  · rw [hsl f hf, show flBm self0 = 0x78048828#64 from rfl, hm]
    rw [show initMem 0x78048828#64 = BitVec.ofNat 64 (2 ^ 31) from rfl, BitVec.getLsbD_ofNat,
      testBit_pow]
    have hf' : f.toNat < 64 := by rw [BitVec.lt_def] at hf; simpa using hf
    by_cases h : f = 31#64
    · subst h; simp
    · have : f.toNat ≠ 31 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      simp [h, hf']; omega

/-- At `main`'s entry the heap is well formed. -/
theorem mainEntry_heapOk {input : List (BitVec 8)} {t : MachineState} (h : MainEntry input t) :
    HeapOk self0 base0 t.getMem :=
  ⟨bs0, L0, rep_init h.2.2.2.2.2.1⟩

end Cases.Zip2005.Runtime.Tlsf
