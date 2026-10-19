import Cases.Zip2005.Sinsemilla.FromIterKit
import Cases.Zip2005.Image.Ro

/-!
# The hasher's six regions, kept across `from_iter`

`cached_commit_domain`'s static (`0x780488a8`, 10 words: the table `Vec` header, the four
generator tables' pointers, the modulus and the `Once` state) and the five heap blocks it
points to (`IV`, 138 words; `G0`, `G1`, `G2`, 1024 words; `G3`, 516 words). `from_iter`'s
allocator calls (ledger A4, A5) keep them and return blocks off them; the loop keeps them
because its own writes (its frame, the `Vec` buffer) are off them.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- The six regions: bases and contents, with the hasher's lengths. -/
structure HasherT where
  b1 : Word
  b2 : Word
  b3 : Word
  b4 : Word
  b5 : Word
  b6 : Word
  L1 : List Word
  L2 : List Word
  L3 : List Word
  L4 : List Word
  L5 : List Word
  L6 : List Word
  l1 : L1.length = 10
  l2 : L2.length = 138
  l3 : L3.length = 1024
  l4 : L4.length = 1024
  l5 : L5.length = 1024
  l6 : L6.length = 516

/-- The five heap blocks among the run's live buffers (`Run.HeapAt`), then `L`. -/
abbrev HasherT.live (T : HasherT) (L : List (Word × Nat)) : List (Word × Nat) :=
  (T.b2, 138) :: (T.b3, 1024) :: (T.b4, 1024) :: (T.b5, 1024) :: (T.b6, 516) :: L

/-- The six regions hold. -/
structure Kept6 (T : HasherT) (t : MachineState) : Prop where
  r1 : Region T.b1 T.L1 t
  r2 : Region T.b2 T.L2 t
  r3 : Region T.b3 T.L3 t
  r4 : Region T.b4 T.L4 t
  r5 : Region T.b5 T.L5 t
  r6 : Region T.b6 T.L6 t

/-- The six lie in the arena. -/
structure Arena6 (T : HasherT) : Prop where
  lo1 : 0x78040620 ≤ T.b1.toNat
  hi1 : T.b1.toNat + 8 * 10 ≤ 0x1c00000000
  lo2 : 0x78040620 ≤ T.b2.toNat
  hi2 : T.b2.toNat + 8 * 138 ≤ 0x1c00000000
  lo3 : 0x78040620 ≤ T.b3.toNat
  hi3 : T.b3.toNat + 8 * 1024 ≤ 0x1c00000000
  lo4 : 0x78040620 ≤ T.b4.toNat
  hi4 : T.b4.toNat + 8 * 1024 ≤ 0x1c00000000
  lo5 : 0x78040620 ≤ T.b5.toNat
  hi5 : T.b5.toNat + 8 * 1024 ≤ 0x1c00000000
  lo6 : 0x78040620 ≤ T.b6.toNat
  hi6 : T.b6.toNat + 8 * 516 ≤ 0x1c00000000

/-- The six are readable and writable (ledger A2's memory range, off the read-only image). -/
structure Ok6 (T : HasherT) : Prop where
  ok1 : RegionOk Ro.layout.roBase Ro.layout.textHi T.b1 10
  ok2 : RegionOk Ro.layout.roBase Ro.layout.textHi T.b2 138
  ok3 : RegionOk Ro.layout.roBase Ro.layout.textHi T.b3 1024
  ok4 : RegionOk Ro.layout.roBase Ro.layout.textHi T.b4 1024
  ok5 : RegionOk Ro.layout.roBase Ro.layout.textHi T.b5 1024
  ok6 : RegionOk Ro.layout.roBase Ro.layout.textHi T.b6 516

/-- The block `[b, b + 8n)` is off the six. -/
structure Away6 (b : Word) (n : Nat) (T : HasherT) : Prop where
  d1 : MachineChecked.RiscV.Sym.Disjoint T.b1 10 b n
  d2 : MachineChecked.RiscV.Sym.Disjoint T.b2 138 b n
  d3 : MachineChecked.RiscV.Sym.Disjoint T.b3 1024 b n
  d4 : MachineChecked.RiscV.Sym.Disjoint T.b4 1024 b n
  d5 : MachineChecked.RiscV.Sym.Disjoint T.b5 1024 b n
  d6 : MachineChecked.RiscV.Sym.Disjoint T.b6 516 b n

/-- A block off the heap is off the six. -/
theorem Away6.of_heap {T : HasherT} (hA : Arena6 T) {b : Word} {n : Nat}
    (h : MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n) : Away6 b n T :=
  ⟨h.of_heap hA.lo1 hA.hi1, h.of_heap hA.lo2 hA.hi2, h.of_heap hA.lo3 hA.hi3,
   h.of_heap hA.lo4 hA.hi4, h.of_heap hA.lo5 hA.hi5, h.of_heap hA.lo6 hA.hi6⟩

/-- A sub-block of a block off the six. -/
theorem Away6.sub {T : HasherT} {b : Word} {N : Nat} (h : Away6 b N T) {a : Word} {i n : Nat}
    (ha : a = b + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ N) : Away6 a n T :=
  ⟨h.d1.sub_right ha hin, h.d2.sub_right ha hin, h.d3.sub_right ha hin, h.d4.sub_right ha hin,
   h.d5.sub_right ha hin, h.d6.sub_right ha hin⟩

theorem Away6.len {T : HasherT} {b : Word} {n m : Nat} (h : Away6 b n T) (e : n = m) : Away6 b m T :=
  e ▸ h

/-- The six survive writes off them. -/
theorem Kept6.of_unchanged {T : HasherT} {s t : MachineState} (hK : Kept6 T s)
    {W : List (Word × Nat)} (hu : Unchanged W s t) (hd : ∀ r ∈ W, Away6 r.1 r.2 T) : Kept6 T t :=
  ⟨hK.r1.of_unchanged' hu T.l1 (fun r hr => (hd r hr).d1),
   hK.r2.of_unchanged' hu T.l2 (fun r hr => (hd r hr).d2),
   hK.r3.of_unchanged' hu T.l3 (fun r hr => (hd r hr).d3),
   hK.r4.of_unchanged' hu T.l4 (fun r hr => (hd r hr).d4),
   hK.r5.of_unchanged' hu T.l5 (fun r hr => (hd r hr).d5),
   hK.r6.of_unchanged' hu T.l6 (fun r hr => (hd r hr).d6)⟩

/-- Offsets in `from_iter`'s loop frame `[sp - 0x100, sp + 0xb0)` (`commit_ivk`'s instance). -/
theorem fl_0 (sp : Word) : sp = sp - 0x100#64 + BitVec.ofNat 64 (8 * 32) :=
  (BitVec.sub_add_cancel sp 0x100#64).symm

theorem fl_18 (sp : Word) : sp + 0x18#64 = sp - 0x100#64 + BitVec.ofNat 64 (8 * 35) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end Cases.Zip2005
