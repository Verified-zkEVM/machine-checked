import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.Ro

/-!
# `memcpy` on aligned doubleword regions

The compiler-builtins `memcpy` (byte prologue until the source is aligned, 32-byte
`ld/sd` loop, 16/8/4/2/1-byte tails, and seven shifting variants for a misaligned
destination). For 8-aligned source and destination and a length that is a multiple of 8,
only the aligned path runs, and the executor unrolls it for each concrete length. One
specification per length the guest uses: the destination holds the source's words.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 16)` on 8-aligned, disjoint regions of 2 doublewords. -/
theorem memcpy16_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 2) (hSl : S.length = 2)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 16#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 2)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 2)
    (hdj : Disjoint dst 2 src 2)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 2)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 2)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 32)` on 8-aligned, disjoint regions of 4 doublewords. -/
theorem memcpy32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 4) (hSl : S.length = 4)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 32#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 4)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 4)
    (hdj : Disjoint dst 4 src 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 4)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 4)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 64)` on 8-aligned, disjoint regions of 8 doublewords. -/
theorem memcpy64_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 8) (hSl : S.length = 8)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 64#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 8)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 8)
    (hdj : Disjoint dst 8 src 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 8)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 8)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 72)` on 8-aligned, disjoint regions of 9 doublewords. -/
theorem memcpy72_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 9) (hSl : S.length = 9)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 72#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 9)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 9)
    (hdj : Disjoint dst 9 src 9)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 9)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 9)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 96)` on 8-aligned, disjoint regions of 12 doublewords. -/
theorem memcpy96_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 12) (hSl : S.length = 12)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 96#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 12)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 12)
    (hdj : Disjoint dst 12 src 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 12)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 12)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 104)` on 8-aligned, disjoint regions of 13 doublewords. -/
theorem memcpy104_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 13) (hSl : S.length = 13)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 104#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 13)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 13)
    (hdj : Disjoint dst 13 src 13)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 13)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 13)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 112)` on 8-aligned, disjoint regions of 14 doublewords. -/
theorem memcpy112_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 14) (hSl : S.length = 14)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 112#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 14)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 14)
    (hdj : Disjoint dst 14 src 14)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 14)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 14)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 120)` on 8-aligned, disjoint regions of 15 doublewords. -/
theorem memcpy120_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 15) (hSl : S.length = 15)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 120#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 15)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 15)
    (hdj : Disjoint dst 15 src 15)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 15)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 15)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 128)` on 8-aligned, disjoint regions of 16 doublewords. -/
theorem memcpy128_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 16) (hSl : S.length = 16)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 128#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 16)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 16)
    (hdj : Disjoint dst 16 src 16)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 16)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 16)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 144)` on 8-aligned, disjoint regions of 18 doublewords. -/
theorem memcpy144_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 18) (hSl : S.length = 18)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 144#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 18)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 18)
    (hdj : Disjoint dst 18 src 18)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 18)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 18)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 160)` on 8-aligned, disjoint regions of 20 doublewords. -/
theorem memcpy160_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 20) (hSl : S.length = 20)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 160#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 20)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 20)
    (hdj : Disjoint dst 20 src 20)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 20)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 20)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 288)` on 8-aligned, disjoint regions of 36 doublewords. -/
theorem memcpy288_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 36) (hSl : S.length = 36)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 288#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 36)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 36)
    (hdj : Disjoint dst 36 src 36)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 36)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 36)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 1000)` on 8-aligned, disjoint regions of 125 doublewords. -/
theorem memcpy1000_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 125) (hSl : S.length = 125)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 1000#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 125)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 125)
    (hdj : Disjoint dst 125 src 125)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 125)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 125)] s
  sym_exec
  sym_close hk
  sym_subst
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hSl).symm

end Cases.Zip2005
