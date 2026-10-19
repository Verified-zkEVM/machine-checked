/-
  Cases.Zip2005.Runtime.Alloc.Search

  `alloc`'s search for a free block (phase D4): the request's class (`classSearch`, the
  code's arithmetic is `Tlsf.flSearch`/`searchRaw`), then the second-level bitmap of that
  class (`slLookup`) or the first-level bitmap above it (`flLookup`), each lowest set bit by
  the de Bruijn table. A list found is non-empty and at or above the search class; the
  branches that would index past the bitmaps are dead by the heap's bitmap invariants.
-/

import Cases.Zip2005.Runtime.Alloc.Exec
import Cases.Zip2005.Runtime.Alloc.Ctz

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Alloc

open RiscvZkvm.Rv64
open MachineChecked.RiscV MachineChecked.RiscV.Frame MachineChecked.RiscV.Check MachineChecked.RiscV.Exec
  Cases.Zip2005.Image

/-- The request's granules: `size + max(align, 16)`, rounded up. -/
def reqOf (a : Word) : Word := (a + 31#64) &&& 0xffffffffffffffe0#64

/-- The search class, `0x7801c1ec`–`0x7801c2e4`: registers only. -/
theorem classSearch {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {a : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c1ec#64)
    (r10 : y.getReg .x10 = a) (ha1 : 16#64 ≤ a) (ha2 : a ≤ 0xffffffffffffffe0#64)
    (r19 : y.getReg .x19 = 0#64)
    (hnull : ∀ y', St s0 M y' → y'.pc = 0x7801c2ec#64 → y'.getReg .x19 = 0#64 → SafeN G n P y')
    (hk : ∀ y', St s0 M y' → y'.pc = 0x7801c320#64 →
      y'.getReg .x11 = Tlsf.flSearch (reqOf a) - 0x3a#64 →
      y'.getReg .x12 = Tlsf.flSearch (reqOf a) → y'.getReg .x13 = Tlsf.searchRaw (reqOf a) →
      y'.getReg .x14 = Tlsf.flSearch (reqOf a) → SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  rw [← setPC_self hpc]
  -- The branch at `0x7801c2e4`, on abstract registers.
  have br : ∀ y', St s0 M y' → y'.pc = 0x7801c2e4#64 → y'.getReg .x10 = 0x3f#64 →
      y'.getReg .x11 = Tlsf.flSearch (reqOf a) - 0x3a#64 →
      y'.getReg .x12 = Tlsf.flSearch (reqOf a) → y'.getReg .x13 = Tlsf.searchRaw (reqOf a) →
      y'.getReg .x14 = Tlsf.flSearch (reqOf a) → SafeN G n P y' := by
    intro y' hs' hpc' q10 q11 q12 q13 q14
    have hcode' := hs'.code
    rw [← setPC_self hpc']
    xstep code
    · exact hk _ (by xst) rfl (by xregs; exact q11) (by xregs; exact q12) (by xregs; exact q13)
        (by xregs; exact q14)
    · xstep code
      exact hnull _ (by xst) rfl (by xregs; rfl)
  iterate 3 xstep code
  · exfalso
    rw [r10] at hb
    simp only [beq_iff_eq] at hb
    xag0
    revert hb ha1 ha2
    generalize a = a
    intro ha1 ha2 hb
    bv_decide
  iterate 42 xstep code
  iterate 16 xstep code
  refine br _ (by xst) rfl (by xregs) ?_ ?_ ?_ ?_ <;> xregs <;>
    simp only [r10, reqOf, Tlsf.flSearch, Tlsf.searchRaw, Tlsf.rotr, Tlsf.subw, Tlsf.clz,
      shr_mod, shl_mod'] <;> xag0 <;> bv_decide

/-- A set bit of a masked word is a set bit of the word, at or above the mask's start. -/
theorem mask_bit {v s i : Word} (hi : i < 64#64)
    (h : ((v &&& (0xffffffffffffffff#64 <<< (s &&& 63#64))) >>> i) &&& 1#64 = 1#64) :
    (v >>> i) &&& 1#64 = 1#64 ∧ (s &&& 63#64) ≤ i := by
  have : ∀ v s i : BitVec 64, i < 64#64 →
      ((v &&& (0xffffffffffffffff#64 <<< (s &&& 63#64))) >>> i) &&& 1#64 = 1#64 →
      (v >>> i) &&& 1#64 = 1#64 ∧ (s &&& 63#64) ≤ i := by
    intro v s i hi h; bv_decide
  exact this v s i hi h

/-- A set bit, as `getLsbD` states it. -/
theorem bit_lsb {v i : Word} (h : (v >>> i) &&& 1#64 = 1#64) : v.getLsbD i.toNat = true := by
  have := congrArg (fun w => w.getLsbD 0) h
  simp only [BitVec.getLsbD_and] at this
  simpa using this

theorem ctz_ok' (w : Word) (hw : w ≠ 0#64) :
    tbl (((w &&& 0 - w) * K) >>> 58) < 64#64 ∧
      (w >>> tbl (((w &&& 0 - w) * K) >>> 58)) &&& 1#64 = 1#64 := ctz_ok w hw

theorem idx_lt (w k : Word) : (w * k) >>> 58 < 64#64 := by
  have : ∀ w k : BitVec 64, (w * k) >>> 58 < 64#64 := by intro w k; bv_decide
  exact this w k

theorem tbl_addr {idx : Word} (h : idx < 64#64) :
    0x78000000 ≤ (alignToDword (0x78001540#64 + idx)).toNat := by
  have : ∀ idx : BitVec 64, idx < 64#64 →
      0x78000000#64 ≤ (0x78001540#64 + idx) &&& ~~~7#64 := by intro idx h; bv_decide
  have h' := this idx h
  unfold alignToDword
  rw [BitVec.le_def] at h'
  simpa using h'

/-- The second-level search, `0x7801c320`: the lowest non-empty list at or above the search
    class in its first-level class, or on to the first level. -/
theorem slLookup {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {fs sr : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c320#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M bs L (fun _ => False)) (hro : RoOk M)
    (hstk : (s0.getReg .x2).toNat ≤ 0x78000000) (hspc : 0x78000000 ≤ (s0.getReg .x10).toNat)
    (hfs : fs < 64#64)
    (q11 : y.getReg .x11 = fs - 0x3a#64) (q12 : y.getReg .x12 = fs) (q13 : y.getReg .x13 = sr)
    (q14 : y.getReg .x14 = fs)
    (hfound : ∀ y' fl sl, St s0 M y' → y'.pc = 0x7801c378#64 →
      y'.getReg .x10 = s0.getReg .x10 + 0x8000#64 → y'.getReg .x12 = fl → y'.getReg .x13 = sl →
      fl < 64#64 → sl < 64#64 → L fl sl ≠ [] → (fs < fl ∨ (fs = fl ∧ (sr &&& 63#64) ≤ sl)) →
      SafeN G n P y')
    (hfl : ∀ y', St s0 M y' → y'.pc = 0x7801c3a8#64 →
      y'.getReg .x10 = s0.getReg .x10 + 0x8000#64 → y'.getReg .x11 = fs - 0x3a#64 →
      y'.getReg .x14 = fs → SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  have hc := hsh.ctlOk
  have offS : ∀ a : Word, 0x78000000 ≤ a.toNat → ¬ InFrame (s0.getReg .x2) a :=
    fun a h => off_frame (by omega)
  have hSL : ¬ InFrame (s0.getReg .x2) (Tlsf.slBm (s0.getReg .x10) fs) :=
    offS _ (by have := (Tlsf.slBm_inCtl hc hfs).1; omega)
  rw [← setPC_self hpc]
  iterate 11 xstep code
  · -- nothing at or above the search class here
    xstep code
    · exact hfl _ (by xst) rfl (by xregs; rw [hs.self]; rfl) (by xregs; exact q11)
        (by xregs; exact q14)
    · exfalso; simp at hb
  · simp only [q12, q13, hs.self, shl_mod'] at hb ⊢
    xag0
    simp only [BitVec.reduceSignExtend, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft,
      BitVec.reduceToNat] at hb
    simp only [sl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC, hs.mem _ hSL] at hb ⊢
    generalize hw : M (Tlsf.slBm (s0.getReg .x10) fs) &&&
      0xffffffffffffffff#64 <<< (sr &&& 63#64) = w at hb
    have hw0 : w ≠ 0#64 := by
      intro h0; apply hb; rw [h0]; rfl
    iterate 10 xstep code
    xag0
    simp only [MachineState.getByte, MachineState.getMem_setReg, MachineState.getMem_setPC,
      hs.mem _ (offS (0x780003f8#64) (by decide)), hro.1]
    generalize hi : ((w &&& 0 - w) * K) >>> 58 = idx
    have hidx : idx < 64#64 := hi ▸ idx_lt _ _
    have hct := ctz_ok' w hw0
    rw [hi] at hct
    rw [hs.mem _ (offS _ (tbl_addr hidx)), load_tbl hro hidx]
    xstep code
    · exfalso
      simp only [BitVec.ult_iff_lt] at hb
      exact hb hct.1
    · -- found: list `(fs, tbl idx)`
      have hb2 := mask_bit hct.1 (hw ▸ hct.2)
      have hbit := bit_lsb hb2.1
      rw [hsh.slbm fs _ hfs hct.1] at hbit
      refine hfound _ fs (tbl idx) (by xst) rfl (by xregs) (by xregs; exact q12) (by xregs)
        hfs hct.1 ?_ (.inr ⟨rfl, hb2.2⟩)
      intro he; rw [he] at hbit; simp at hbit

theorem above_fs {fs j : Word} (h62 : ¬ 62#64 < fs) (h : ((fs - 0x3a#64 + 0x3b#64) &&& 63#64) ≤ j) :
    fs < j := by
  have : ∀ fs j : BitVec 64, ¬ 62#64 < fs → ((fs - 0x3a#64 + 0x3b#64) &&& 63#64) ≤ j → fs < j := by
    intro fs j h62 h; bv_decide
  exact this fs j h62 h

/-- The first-level search, `0x7801c3a8`: the lowest non-empty class above the search
    class, then its lowest list; or nothing. -/
theorem flLookup {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L : Word → Word → List Word}
    {fs sr : Word} (hs : St s0 M y) (hpc : y.pc = 0x7801c3a8#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M bs L (fun _ => False)) (hro : RoOk M)
    (hstk : (s0.getReg .x2).toNat ≤ 0x78000000) (hspc : 0x78000000 ≤ (s0.getReg .x10).toNat)
    (q10 : y.getReg .x10 = s0.getReg .x10 + 0x8000#64) (q11 : y.getReg .x11 = fs - 0x3a#64)
    (q14 : y.getReg .x14 = fs)
    (hnull : ∀ y', St s0 M y' → y'.pc = 0x7801c2ec#64 → y'.getReg .x19 = 0#64 → SafeN G n P y')
    (hfound : ∀ y' fl sl, St s0 M y' → y'.pc = 0x7801c378#64 →
      y'.getReg .x10 = s0.getReg .x10 + 0x8000#64 → y'.getReg .x12 = fl → y'.getReg .x13 = sl →
      fl < 64#64 → sl < 64#64 → L fl sl ≠ [] → (fs < fl ∨ (fs = fl ∧ (sr &&& 63#64) ≤ sl)) →
      SafeN G n P y') : SafeN G n P y := by
  have hcode := hs.code
  have hc := hsh.ctlOk
  have offS : ∀ a : Word, 0x78000000 ≤ a.toNat → ¬ InFrame (s0.getReg .x2) a :=
    fun a h => off_frame (by omega)
  have hFL : ¬ InFrame (s0.getReg .x2) (Tlsf.flBm (s0.getReg .x10)) :=
    offS _ (by have := (Tlsf.flBm_inCtl hc).1; omega)
  rw [← setPC_self hpc]
  iterate 2 xstep code
  · -- the search class is the last: nothing above it
    iterate 1 xstep code
    exact hnull _ (by xst) rfl (by xregs; rfl)
  have h62 : ¬ 62#64 < fs := by rw [q14] at hb; simpa [BitVec.ult_iff_lt] using hb
  iterate 8 xstep code
  · -- no class above: nothing
    iterate 3 xstep code
    · xstep code
      exact hnull _ (by xst) rfl (by xregs; rfl)
    · exfalso; simp at hb
  simp only [q11, hs.self, shl_mod'] at hb ⊢
  xag0
  simp only [BitVec.reduceSignExtend, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft] at hb
  simp only [fl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC, hs.mem _ hFL] at hb ⊢
  generalize hw : M (Tlsf.flBm (s0.getReg .x10)) &&&
    0xffffffffffffffff#64 <<< (fs - 0x3a#64 + 0x3b#64 &&& 63#64) = w at hb
  have hw0 : w ≠ 0#64 := by intro h0; apply hb; rw [h0]; rfl
  iterate 10 xstep code
  xag0
  simp only [MachineState.getByte, MachineState.getMem_setReg, MachineState.getMem_setPC,
    hs.mem _ (offS (0x780003f8#64) (by decide)), hro.1]
  generalize hi : ((w &&& 0 - w) * K) >>> 58 = idx
  have hidx : idx < 64#64 := hi ▸ idx_lt _ _
  have hct := ctz_ok' w hw0
  rw [hi] at hct
  rw [hs.mem _ (offS _ (tbl_addr hidx)), load_tbl hro hidx]
  have hb2 := mask_bit hct.1 (hw ▸ hct.2)
  have hfj := above_fs h62 hb2.2
  have hbit := bit_lsb hb2.1
  rw [hsh.flbm _ hct.1] at hbit
  -- `tbl idx` is the class `j`; its second-level bitmap is not empty.
  generalize tbl idx = j at hct hbit hfj ⊢
  have hSLj : ¬ InFrame (s0.getReg .x2) (Tlsf.slBm (s0.getReg .x10) j) :=
    offS _ (by have := (Tlsf.slBm_inCtl hc hct.1).1; omega)
  xstep code
  xstep code
  · exfalso; simp only [BitVec.ult_iff_lt] at hb; have := hct.1; bv_omega
  xstep code
  simp only [signExtend21, BitVec.reduceSignExtend, BitVec.reduceAdd]
  iterate 3 xstep code
  simp only [q10]
  xag0
  simp only [sl_addr2, MachineState.getMem_setReg, MachineState.getMem_setPC, hs.mem _ hSLj] at hb ⊢
  xstep code
  · exfalso
    have : M (Tlsf.slBm (s0.getReg .x10) j) = 0#64 := by simpa using hb
    rw [this] at hbit; simp at hbit
  have hv0 : M (Tlsf.slBm (s0.getReg .x10) j) ≠ 0#64 := by
    intro h0; apply hb; rw [h0]; rfl
  iterate 11 xstep code
  xag0
  simp only [signExtend21, BitVec.reduceSignExtend, BitVec.reduceAdd]
  simp only [MachineState.getByte, MachineState.getMem_setReg, MachineState.getMem_setPC,
    hs.mem _ (offS (0x780003f8#64) (by decide)), hro.1]
  generalize hi2 : ((M (Tlsf.slBm (s0.getReg .x10) j) &&& 0 - M (Tlsf.slBm (s0.getReg .x10) j)) *
    K) >>> 58 = idx2
  have hidx2 : idx2 < 64#64 := hi2 ▸ idx_lt _ _
  have hct2 := ctz_ok' _ hv0
  rw [hi2] at hct2
  rw [hs.mem _ (offS _ (tbl_addr hidx2)), load_tbl hro hidx2]
  have hbit2 := bit_lsb hct2.2
  rw [hsh.slbm _ _ hct.1 hct2.1] at hbit2
  refine hfound _ j (tbl idx2) (by xst) rfl (by xregs; exact q10) (by xregs) (by xregs) hct.1
    hct2.1 ?_ (.inl hfj)
  intro he; rw [he] at hbit2; simp at hbit2

end Cases.Zip2005.Runtime.Alloc
