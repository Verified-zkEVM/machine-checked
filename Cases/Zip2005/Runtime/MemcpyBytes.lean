import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.Ro

/-!
# `memcpy` by the byte

The BLAKE2b hasher's buffer takes its input in pieces (`State::update` / `fill_buf`): 32
bytes at the start, a single domain-separator byte at offset 32, then 32-byte fields at
offset 33 (and 65). `compress1_loop` copies the partial block (33, 65 or 97 bytes) into a
zeroed frame buffer. `memcpy`'s byte paths run for these; the destination cells are stated in
a canonical shift form, as `Proof/Runtime/MemcpyOff.lean` does for the 7-byte offset.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-! ### Cells written byte by byte, one byte up -/

/-- Bytes 0–6 of `s` into bytes 1–7 of `d`: `s` shifted up one byte over `d`'s low byte. -/
theorem up1_first (d s : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte d
      1 (extractByte s 0)) 2 (extractByte s 1)) 3 (extractByte s 2)) 4 (extractByte s 3))
      5 (extractByte s 4)) 6 (extractByte s 5)) 7 (extractByte s 6) = (s <<< 8) ||| (d &&& 0xff#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- Byte 7 of `a` into byte 0 of `d`. -/
theorem up1_last (d a : Word) :
    replaceByte d 0 (extractByte a 7) = (d &&& 0xffffffffffffff00#64) ||| (a >>> 56) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- A byte into the low byte of a zero word is its zero-extension. -/
theorem replaceByte_zero0 (b : BitVec 8) : replaceByte 0#64 0 b = BitVec.zeroExtend 64 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
  interval_cases i <;> simp

/-- The low byte of a cell whose byte 0 was just written from `a`'s top byte. -/
theorem and_ff_of_up1 (d a : Word) :
    ((d &&& 0xffffffffffffff00#64) ||| (a >>> 56)) &&& 0xff#64 = a >>> 56 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

/-- A byte into the low byte of any word, masked to that byte: its zero extension. -/
theorem replaceByte0_and_ff (z : Word) (b : BitVec 8) : replaceByte z 0 b &&& 0xff#64 = BitVec.zeroExtend 64 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- The low byte of a cell whose byte 0 was written from `a`'s top byte, zero-extended: `a >>> 56`. -/
theorem zext_extract_up1_last (d a : Word) :
    BitVec.zeroExtend 64 (extractByte ((d &&& 0xffffffffffffff00#64) ||| (a >>> 56)) 0) = a >>> 56 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

/-- 32 bytes copied to one byte past an aligned doubleword: the five cells touched. -/
def shiftUp1 (d0 d4 s0 s1 s2 s3 : Word) : List Word :=
  [(s0 <<< 8) ||| (d0 &&& 0xff#64),
   (s1 <<< 8) ||| (s0 >>> 56),
   (s2 <<< 8) ||| (s1 >>> 56),
   (s3 <<< 8) ||| (s2 >>> 56),
   (d4 &&& 0xffffffffffffff00#64) ||| (s3 >>> 56)]

/-- A pointer one byte into an aligned doubleword. -/
theorem and7_of_sub1 {p : Word} (h : (p - 1#64).toNat % 8 = 0) : p &&& 7#64 = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

/-! ### Words re-read from their bytes -/

set_option maxHeartbeats 4000000 in
/-- Eight bytes of a word, zero-extended, shifted and or-ed back in the order the machine does. -/
theorem pack_word (k : Word) :
    ((((BitVec.zeroExtend 64 (extractByte k 7) <<< 24) ||| (BitVec.zeroExtend 64 (extractByte k 6) <<< 16)) |||
        ((BitVec.zeroExtend 64 (extractByte k 5) <<< 8) ||| BitVec.zeroExtend 64 (extractByte k 4))) <<< 32) |||
      (((BitVec.zeroExtend 64 (extractByte k 3) <<< 24) ||| (BitVec.zeroExtend 64 (extractByte k 2) <<< 16)) |||
        ((BitVec.zeroExtend 64 (extractByte k 1) <<< 8) ||| BitVec.zeroExtend 64 (extractByte k 0))) = k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

/-- Eight bytes `w >>> 8·j` of a word, zero-extended, shifted and or-ed back in the machine's order. -/
theorem pack_shift (w : Word) :
    ((((BitVec.zeroExtend 64 (BitVec.truncate 8 (w >>> 56)) <<< 24) |||
          (BitVec.zeroExtend 64 (BitVec.truncate 8 (w >>> 48)) <<< 16)) |||
        ((BitVec.zeroExtend 64 (BitVec.truncate 8 (w >>> 40)) <<< 8) |||
          BitVec.zeroExtend 64 (BitVec.truncate 8 (w >>> 32)))) <<< 32) |||
      (((BitVec.zeroExtend 64 (BitVec.truncate 8 (w >>> 24)) <<< 24) |||
          (BitVec.zeroExtend 64 (BitVec.truncate 8 (w >>> 16)) <<< 16)) |||
        ((BitVec.zeroExtend 64 (BitVec.truncate 8 (w >>> 8)) <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 w))) =
      w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp

/-! ### The specifications -/

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 1)`, both 8-aligned: the low byte of the destination cell. -/
theorem memcpy1_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src d0 s0 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 1#64)
    (hD : Region dst [d0] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 1)
    (hS : Region src [s0] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 1)
    (hdj : Disjoint dst 1 src 1)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 1)] s t →
      Region dst [replaceByte d0 0 (extractByte s0 0)] t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 1)] s
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 0)`: nothing is read or written. -/
theorem memcpy0_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 0#64)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [] s
  sym_exec
  all_goals sym_close hk

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 32)` with `dst` one byte into an aligned doubleword, `src` aligned:
    byte by byte, the four words land shifted up one byte across five cells. -/
theorem memcpy32_off1_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src d0 d1 d2 d3 d4 s0 s1 s2 s3 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 32#64)
    (hD : Region (dst - 1#64) [d0, d1, d2, d3, d4] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (dst - 1#64) 5)
    (hS : Region src [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 4)
    (hdj : Disjoint (dst - 1#64) 5 src 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 1#64, 5)] s t →
      Region (dst - 1#64) (shiftUp1 d0 d4 s0 s1 s2 s3) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst - 1#64, 5)] s
  have hm : dst &&& 7#64 = 1#64 := and7_of_sub1 hokD.aligned
  sym_exec
  sym_close hk
  sym_subst
  simp only [shiftUp1, trunc8_zext, up1_first, up1_last, and_ff_of_up1]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 33)`, both 8-aligned: four words and the low byte of the fifth cell. -/
theorem memcpy33_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (d0 d1 d2 d3 d4 s0 s1 s2 s3 s4 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 33#64)
    (hD : Region dst [d0, d1, d2, d3, d4] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 5)
    (hS : Region src [s0, s1, s2, s3, s4] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 5)
    (hdj : Disjoint dst 5 src 5)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 5)] s t →
      Region dst [s0, s1, s2, s3, replaceByte d4 0 (extractByte s4 0)] t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 5)] s
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 65)`, both 8-aligned: eight words and the low byte of the ninth cell. -/
theorem memcpy65_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (d0 d1 d2 d3 d4 d5 d6 d7 d8 s0 s1 s2 s3 s4 s5 s6 s7 s8 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 65#64)
    (hD : Region dst [d0, d1, d2, d3, d4, d5, d6, d7, d8] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 9)
    (hS : Region src [s0, s1, s2, s3, s4, s5, s6, s7, s8] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 9)
    (hdj : Disjoint dst 9 src 9)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 9)] s t →
      Region dst [s0, s1, s2, s3, s4, s5, s6, s7, replaceByte d8 0 (extractByte s8 0)] t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 9)] s
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 97)`, both 8-aligned: twelve words and the low byte of the thirteenth cell. -/
theorem memcpy97_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 97#64)
    (hD : Region dst [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 13)
    (hS : Region src [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 13)
    (hdj : Disjoint dst 13 src 13)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 13)] s t →
      Region dst [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, replaceByte d12 0 (extractByte s12 0)] t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 13)] s
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext]

end Cases.Zip2005
