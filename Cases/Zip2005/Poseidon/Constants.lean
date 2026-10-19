import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemcpyLoop
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Poseidon.PoseidonPerm
import Cases.Zip2005.Sinsemilla.SinsemillaModel
import Cases.Zip2005.Image.F_78023cbc
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `P128Pow5T3::constants()` (0x78023cbc)

`(ROUND_CONSTANTS.to_vec(), MDS, MDS_INV)`: `__rust_alloc(0x1800, 8)` (a **contract**, ledger
A4, the instance at this call) and a `memcpy` of the 64 × 3 round constants out of the read-only
segment into it, the `Vec` header `[64, ptr, 64]`, then the two 3 × 3 matrices copied into the
output struct. The read-only words are `Poseidon.rcWords` and `Poseidon.mdsWords` (as the
Poseidon permutation's proofs read them); the inverse matrix is `mdsInvWords`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- `MDS_INV`, row-major, as the read-only segment holds it (the tail of chunk 154 and the head
    of 155). -/
def mdsInvWords : List Word := ((roChunksFrom 154 2).drop 36).take 36

theorem rcWords_length : Poseidon.rcWords.length = 768 := by decide +kernel
theorem mdsWords_length : Poseidon.mdsWords.length = 36 := by decide +kernel
theorem mdsInvWords_length : mdsInvWords.length = 36 := by decide +kernel

theorem rcOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78011c00#64 768 := ⟨by decide, by decide, Or.inl (by decide)⟩
theorem mdsOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78013400#64 36 := ⟨by decide, by decide, Or.inl (by decide)⟩
theorem mdsInvOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78013520#64 36 := ⟨by decide, by decide, Or.inl (by decide)⟩

/-- The round constants in the read-only segment. -/
theorem RoImage.rcWords {s : MachineState} (h : RoImage Ro.layout s) : Region 0x78011c00#64 Poseidon.rcWords s :=
  RoImage.chunksFrom h 142 12 (by decide) (by decide +kernel)

/-- The matrix in the read-only segment. -/
theorem RoImage.mdsWords {s : MachineState} (h : RoImage Ro.layout s) : Region 0x78013400#64 Poseidon.mdsWords s :=
  (RoImage.chunksFrom h 154 2 (by decide) (by decide +kernel)).sub 0 36 rfl rfl

/-- Its inverse in the read-only segment. -/
theorem RoImage.mdsInvWords {s : MachineState} (h : RoImage Ro.layout s) : Region 0x78013520#64 mdsInvWords s :=
  (RoImage.chunksFrom h 154 2 (by decide) (by decide +kernel)).sub 36 36 rfl rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem constants_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out : Word) (O : List Word)
    (hOl : O.length = 75)
    (hpc : s.pc = 0x78023cbc#64) (hcode : CodeAt F_78023cbc.base F_78023cbc.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 75)
    (hdj : Disjoint (sp - 0x50#64) 10 out 75) (houtHp : Disjoint 0x78040620#64 14780694332 out 75)
    -- `__rust_alloc(0x1800, 8)` at its call site here (ledger A4)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78023cf4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x1800#64 →
      u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78023cf4#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 768 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x1800 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 768) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hk : ∀ (t : MachineState) (ptr : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out ([64#64, ptr, 64#64] ++ Poseidon.mdsWords ++ mdsInvWords) t →
      Region ptr Poseidon.rcWords t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 768 →
      0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 768) :: L) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hstk.frame 10 (by decide)
  have hu := Unchanged.refl [(sp - 0x50#64, 10), (out, 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hRC := RoImage.rcWords hro
  have hM1 := RoImage.mdsWords hro
  have hM2 := RoImage.mdsInvWords hro
  have hRCl := rcWords_length
  have hM1l := mdsWords_length
  have hM2l := mdsInvWords_length
  have hokRC := rcOk
  have hokM1 := mdsOk
  have hokM2 := mdsInvOk
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokS.sub' 6 4 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  sym_exec [halloc, hhandle_rv, memcpy6144_spec, memcpy288_spec]
  sym_close hk _ post15_0
  · -- the struct's 75 cells are the header and the two matrices
    rfl
  · exact ‹RegionOk Ro.layout.roBase Ro.layout.textHi post15_0 768›.weaken (by decide) (by decide)

end Cases.Zip2005
