import Cases.Zip2005.Runtime.MemcpyBytes
import Cases.Zip2005.Image.Ro

/-!
# `memcpy` by the byte, for `RandomSeed::rcm_v3`'s hasher

`rcm_v3` hashes 169 bytes, so its buffer takes the fields at offsets one past alignment (the value
`v` at 97, 23 bytes of `rho` at 105 to fill the first block), the rest of `rho` from seven bytes
past alignment of its source, and `finalize` copies a 41-byte partial block.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- A pointer seven bytes into an aligned doubleword. -/
theorem and7_of_sub7 {p : Word} (h : (p - 7#64).toNat % 8 = 0) : p &&& 7#64 = 7#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 8)`, `dst` one byte past alignment, `src` aligned. -/
theorem memcpy8_off1_spec {P : Prop} (s : MachineState) (ra dst src d0 d1 s0 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 8#64)
    (hD : Region (dst - 1#64) [d0, d1] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (dst - 1#64) 2)
    (hS : Region src [s0] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 1)
    (hdj : Disjoint (dst - 1#64) 2 src 1)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 1#64, 2)] s t →
      Region (dst - 1#64) [(s0 <<< 8) ||| (d0 &&& 0xff#64), (d1 &&& 0xffffffffffffff00#64) ||| (s0 >>> 56)] t →
      Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(dst - 1#64, 2)] s
  have hm : dst &&& 7#64 = 1#64 := and7_of_sub1 hokD.aligned
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext, up1_first, up1_last]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 23)`, `dst` one byte past alignment, `src` aligned: fills `dst - 1`'s three cells
    above their low byte. -/
theorem memcpy23_off1_spec {P : Prop} (s : MachineState) (ra dst src d0 d1 d2 s0 s1 s2 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 23#64)
    (hD : Region (dst - 1#64) [d0, d1, d2] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (dst - 1#64) 3)
    (hS : Region src [s0, s1, s2] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 3)
    (hdj : Disjoint (dst - 1#64) 3 src 3)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 1#64, 3)] s t →
      Region (dst - 1#64) [(s0 <<< 8) ||| (d0 &&& 0xff#64), (s1 <<< 8) ||| (s0 >>> 56), (s2 <<< 8) ||| (s1 >>> 56)] t →
      Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(dst - 1#64, 3)] s
  have hm : dst &&& 7#64 = 1#64 := and7_of_sub1 hokD.aligned
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext, up1_first, up1_last, and_ff_of_up1]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 9)`, `dst` aligned, `src` seven bytes past alignment. -/
theorem memcpy9_src7_spec {P : Prop} (s : MachineState) (ra dst src d0 d1 a2 a3 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 9#64)
    (hD : Region dst [d0, d1] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi dst 2)
    (hS : Region (src - 7#64) [a2, a3] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (src - 7#64) 2)
    (hdj : Disjoint dst 2 (src - 7#64) 2)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 2)] s t →
      Region dst [(a3 <<< 8) ||| (a2 >>> 56), (d1 &&& 0xffffffffffffff00#64) ||| (a3 >>> 56)] t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(dst, 2)] s
  have hm : src &&& 7#64 = 7#64 := and7_of_sub7 hokS.aligned
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext, up1_first, up1_last, and_ff_of_up1]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 41)`, both 8-aligned. -/
theorem memcpy41_spec {P : Prop} (s : MachineState) (ra dst src : Word) (d0 d1 d2 d3 d4 d5 s0 s1 s2 s3 s4 s5 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 41#64)
    (hD : Region dst [d0, d1, d2, d3, d4, d5] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 6)
    (hS : Region src [s0, s1, s2, s3, s4, s5] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 6)
    (hdj : Disjoint dst 6 src 6)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 6)] s t →
      Region dst [s0, s1, s2, s3, s4, replaceByte d5 0 (extractByte s5 0)] t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(dst, 6)] s
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext]

end Cases.Zip2005
