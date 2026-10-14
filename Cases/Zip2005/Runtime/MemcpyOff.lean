import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.Ro

/-!
# `memcpy` across a 7-byte offset

Rust moves a 128-byte value through a buffer at `sp + 7` (`parse_rk`,
`SpendValidatingKey::from_bytes`): `memcpy(base + 7, src, 128)` then
`memcpy(dst, base + 7, 128)`. Both run `memcpy`'s misaligned-destination variants (a
byte prologue, the jump table, a shifting 32-byte loop, byte tails); the executor unrolls
them. The specifications state the resulting cells in a canonical shift form, and the
round trip is the identity on the 16 words.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- A pointer 7 bytes into an aligned doubleword. -/
theorem and7_of_sub7 {p : Word} (h : (p - 7#64).toNat % 8 = 0) : p &&& 7#64 = 7#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

/-! ### Cells written byte by byte -/

/-- After `chain_up_last` on the first seven stores, byte 0 of `b` into the top byte: the
    doubleword one byte up. -/
theorem chain_up_fin (d a b : Word) :
    replaceByte ((a >>> 8) ||| (d &&& 0xff00000000000000#64)) 7 (extractByte b 0) = (b <<< 56) ||| (a >>> 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- Bytes 1–7 of `a` into the low seven bytes; the top byte stays. -/
theorem chain_up_last (d a : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (d) 0 (extractByte a 1)) 1 (extractByte a 2)) 2 (extractByte a 3)) 3 (extractByte a 4)) 4 (extractByte a 5)) 5 (extractByte a 6)) 6 (extractByte a 7) = (a >>> 8) ||| (d &&& 0xff00000000000000#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- Byte 7 of `c0` then the low seven bytes of `c1` (as `srli`/`sb` store them). -/
theorem chain_down0 (d c0 c1 : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte d 0 (extractByte c0 7)) 1 (BitVec.truncate 8 c1)) 2 (BitVec.truncate 8 (c1 >>> 8))) 3 (BitVec.truncate 8 (c1 >>> 16))) 4 (BitVec.truncate 8 (c1 >>> 24))) 5 (BitVec.truncate 8 (c1 >>> 32))) 6 (BitVec.truncate 8 (c1 >>> 40))) 7 (BitVec.truncate 8 (c1 >>> 48)) = (c1 <<< 8) ||| (c0 >>> 56) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- Byte 7 of `a` then bytes 0–6 of `b`. -/
theorem chain_down (d a b : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte d 0 (extractByte a 7)) 1 (extractByte b 0)) 2 (extractByte b 1)) 3 (extractByte b 2)) 4 (extractByte b 3)) 5 (extractByte b 4)) 6 (extractByte b 5)) 7 (extractByte b 6) = (b <<< 8) ||| (a >>> 56) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-! ### The shifted layouts and their round trip -/

/-- The 17 cells at `base` after `memcpy(base + 7, src, 128)`: `D` the old cells, `S` the
    16 source words. -/
def shiftUp7 (D S : List Word) : List Word :=
  [replaceByte D[0]! 7 (BitVec.truncate 8 S[0]!),
    (S[1]! <<< 56) ||| (S[0]! >>> 8),
    (S[2]! <<< 56) ||| (S[1]! >>> 8),
    (S[3]! <<< 56) ||| (S[2]! >>> 8),
    (S[4]! <<< 56) ||| (S[3]! >>> 8),
    (S[5]! <<< 56) ||| (S[4]! >>> 8),
    (S[6]! <<< 56) ||| (S[5]! >>> 8),
    (S[7]! <<< 56) ||| (S[6]! >>> 8),
    (S[8]! <<< 56) ||| (S[7]! >>> 8),
    (S[9]! <<< 56) ||| (S[8]! >>> 8),
    (S[10]! <<< 56) ||| (S[9]! >>> 8),
    (S[11]! <<< 56) ||| (S[10]! >>> 8),
    (S[12]! <<< 56) ||| (S[11]! >>> 8),
    (S[13]! <<< 56) ||| (S[12]! >>> 8),
    (S[14]! <<< 56) ||| (S[13]! >>> 8),
    (S[15]! <<< 56) ||| (S[14]! >>> 8),
    (S[15]! >>> 8) ||| (D[16]! &&& 0xff00000000000000#64)]

/-- The 16 words at `dst` after `memcpy(dst, base + 7, 128)`: `C` the 17 cells at `base`. -/
def shiftDown7 (C : List Word) : List Word :=
  [(C[1]! <<< 8) ||| (C[0]! >>> 56),
    (C[2]! <<< 8) ||| (C[1]! >>> 56),
    (C[3]! <<< 8) ||| (C[2]! >>> 56),
    (C[4]! <<< 8) ||| (C[3]! >>> 56),
    (C[5]! <<< 8) ||| (C[4]! >>> 56),
    (C[6]! <<< 8) ||| (C[5]! >>> 56),
    (C[7]! <<< 8) ||| (C[6]! >>> 56),
    (C[8]! <<< 8) ||| (C[7]! >>> 56),
    (C[9]! <<< 8) ||| (C[8]! >>> 56),
    (C[10]! <<< 8) ||| (C[9]! >>> 56),
    (C[11]! <<< 8) ||| (C[10]! >>> 56),
    (C[12]! <<< 8) ||| (C[11]! >>> 56),
    (C[13]! <<< 8) ||| (C[12]! >>> 56),
    (C[14]! <<< 8) ||| (C[13]! >>> 56),
    (C[15]! <<< 8) ||| (C[14]! >>> 56),
    (C[16]! <<< 8) ||| (C[15]! >>> 56)]

theorem rt_first (d a b : Word) :
    (((b <<< 56) ||| (a >>> 8)) <<< 8) ||| (replaceByte d 7 (BitVec.truncate 8 a) >>> 56) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

theorem rt_mid (a b c : Word) :
    (((c <<< 56) ||| (b >>> 8)) <<< 8) ||| (((b <<< 56) ||| (a >>> 8)) >>> 56) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem rt_last (d a b : Word) :
    (((b >>> 8) ||| (d &&& 0xff00000000000000#64)) <<< 8) ||| (((b <<< 56) ||| (a >>> 8)) >>> 56) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

/-- Up by seven bytes and down again: the 16 words. -/
theorem shiftDown7_shiftUp7 (D S : List Word) (hS : S.length = 16) :
    shiftDown7 (shiftUp7 D S) = S := by
  have e : shiftDown7 (shiftUp7 D S) =
    [(((S[1]! <<< 56) ||| (S[0]! >>> 8)) <<< 8) ||| ((replaceByte D[0]! 7 (BitVec.truncate 8 S[0]!)) >>> 56),
      (((S[2]! <<< 56) ||| (S[1]! >>> 8)) <<< 8) ||| (((S[1]! <<< 56) ||| (S[0]! >>> 8)) >>> 56),
      (((S[3]! <<< 56) ||| (S[2]! >>> 8)) <<< 8) ||| (((S[2]! <<< 56) ||| (S[1]! >>> 8)) >>> 56),
      (((S[4]! <<< 56) ||| (S[3]! >>> 8)) <<< 8) ||| (((S[3]! <<< 56) ||| (S[2]! >>> 8)) >>> 56),
      (((S[5]! <<< 56) ||| (S[4]! >>> 8)) <<< 8) ||| (((S[4]! <<< 56) ||| (S[3]! >>> 8)) >>> 56),
      (((S[6]! <<< 56) ||| (S[5]! >>> 8)) <<< 8) ||| (((S[5]! <<< 56) ||| (S[4]! >>> 8)) >>> 56),
      (((S[7]! <<< 56) ||| (S[6]! >>> 8)) <<< 8) ||| (((S[6]! <<< 56) ||| (S[5]! >>> 8)) >>> 56),
      (((S[8]! <<< 56) ||| (S[7]! >>> 8)) <<< 8) ||| (((S[7]! <<< 56) ||| (S[6]! >>> 8)) >>> 56),
      (((S[9]! <<< 56) ||| (S[8]! >>> 8)) <<< 8) ||| (((S[8]! <<< 56) ||| (S[7]! >>> 8)) >>> 56),
      (((S[10]! <<< 56) ||| (S[9]! >>> 8)) <<< 8) ||| (((S[9]! <<< 56) ||| (S[8]! >>> 8)) >>> 56),
      (((S[11]! <<< 56) ||| (S[10]! >>> 8)) <<< 8) ||| (((S[10]! <<< 56) ||| (S[9]! >>> 8)) >>> 56),
      (((S[12]! <<< 56) ||| (S[11]! >>> 8)) <<< 8) ||| (((S[11]! <<< 56) ||| (S[10]! >>> 8)) >>> 56),
      (((S[13]! <<< 56) ||| (S[12]! >>> 8)) <<< 8) ||| (((S[12]! <<< 56) ||| (S[11]! >>> 8)) >>> 56),
      (((S[14]! <<< 56) ||| (S[13]! >>> 8)) <<< 8) ||| (((S[13]! <<< 56) ||| (S[12]! >>> 8)) >>> 56),
      (((S[15]! <<< 56) ||| (S[14]! >>> 8)) <<< 8) ||| (((S[14]! <<< 56) ||| (S[13]! >>> 8)) >>> 56),
      (((S[15]! >>> 8) ||| (D[16]! &&& 0xff00000000000000#64)) <<< 8) ||| (((S[15]! <<< 56) ||| (S[14]! >>> 8)) >>> 56)] := rfl
  rw [e]
  simp only [rt_first, rt_mid, rt_last]
  exact (AsmVerif.RiscV.Sym.List.eq_map_range S hS).symm

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 128)` with `dst` seven bytes into an aligned doubleword: the 17 cells
    from `dst - 7` become `shiftUp7 D S`. -/
theorem memcpy128_to7_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 17) (hSl : S.length = 16)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 128#64)
    (hD : Region (dst - 7#64) D s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (dst - 7#64) 17)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 16)
    (hdj : Disjoint (dst - 7#64) 17 src 16)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 7#64, 17)] s t →
      Region (dst - 7#64) (shiftUp7 D S) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst - 7#64, 17)] s
  have hm : dst &&& 7#64 = 7#64 := and7_of_sub7 hokD.aligned
  sym_exec
  sym_close hk
  sym_subst
  rw [show shiftUp7 D S = [replaceByte D[0]! 7 (BitVec.truncate 8 S[0]!),
    (S[1]! <<< 56) ||| (S[0]! >>> 8),
    (S[2]! <<< 56) ||| (S[1]! >>> 8),
    (S[3]! <<< 56) ||| (S[2]! >>> 8),
    (S[4]! <<< 56) ||| (S[3]! >>> 8),
    (S[5]! <<< 56) ||| (S[4]! >>> 8),
    (S[6]! <<< 56) ||| (S[5]! >>> 8),
    (S[7]! <<< 56) ||| (S[6]! >>> 8),
    (S[8]! <<< 56) ||| (S[7]! >>> 8),
    (S[9]! <<< 56) ||| (S[8]! >>> 8),
    (S[10]! <<< 56) ||| (S[9]! >>> 8),
    (S[11]! <<< 56) ||| (S[10]! >>> 8),
    (S[12]! <<< 56) ||| (S[11]! >>> 8),
    (S[13]! <<< 56) ||| (S[12]! >>> 8),
    (S[14]! <<< 56) ||| (S[13]! >>> 8),
    (S[15]! <<< 56) ||| (S[14]! >>> 8),
    (S[15]! >>> 8) ||| (D[16]! &&& 0xff00000000000000#64)] from rfl]
  simp only [trunc8_zext, chain_up_last, chain_up_fin]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 128)` with `src` seven bytes into an aligned doubleword: `dst` holds
    `shiftDown7 C`, `C` the 17 cells from `src - 7`. -/
theorem memcpy128_from7_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D C : List Word)
    (hDl : D.length = 16) (hCl : C.length = 17)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 128#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi dst 16)
    (hC : Region (src - 7#64) C s) (hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (src - 7#64) 17)
    (hdj : Disjoint dst 16 (src - 7#64) 17)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 16)] s t →
      Region dst (shiftDown7 C) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 16)] s
  have hm : src &&& 7#64 = 7#64 := and7_of_sub7 hokC.aligned
  sym_exec
  sym_close hk
  sym_subst
  rw [show shiftDown7 C = [(C[1]! <<< 8) ||| (C[0]! >>> 56),
    (C[2]! <<< 8) ||| (C[1]! >>> 56),
    (C[3]! <<< 8) ||| (C[2]! >>> 56),
    (C[4]! <<< 8) ||| (C[3]! >>> 56),
    (C[5]! <<< 8) ||| (C[4]! >>> 56),
    (C[6]! <<< 8) ||| (C[5]! >>> 56),
    (C[7]! <<< 8) ||| (C[6]! >>> 56),
    (C[8]! <<< 8) ||| (C[7]! >>> 56),
    (C[9]! <<< 8) ||| (C[8]! >>> 56),
    (C[10]! <<< 8) ||| (C[9]! >>> 56),
    (C[11]! <<< 8) ||| (C[10]! >>> 56),
    (C[12]! <<< 8) ||| (C[11]! >>> 56),
    (C[13]! <<< 8) ||| (C[12]! >>> 56),
    (C[14]! <<< 8) ||| (C[13]! >>> 56),
    (C[15]! <<< 8) ||| (C[14]! >>> 56),
    (C[16]! <<< 8) ||| (C[15]! >>> 56)] from rfl]
  simp only [trunc8_zext, chain_down0, chain_down]

end Cases.Zip2005
