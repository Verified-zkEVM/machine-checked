import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Runtime.MemcpyBytes
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.Ro

/-!
# `memcpy` between differently misaligned buffers

`ArrayVisitor<Bytes32, 32>` moves its 32 elements out of the frame, where each sits two bytes
into a doubleword, into its `Ok` value, where each sits one byte in:
`memcpy(dst, src, 32)` with `dst ≡ 1`, `src ≡ 2` (mod 8). Six 17-byte copies between aligned
buffers move the rest. The cells are stated byte by byte (`mcpyW`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- Byte `k` of cell `i` of a destination window `D` after copying `n` bytes to byte offset
    `dOff` from the source window `S` at byte offset `sOff`. -/
def mcByte (D S : List Word) (dOff sOff n i k : Nat) : BitVec 8 :=
  if dOff ≤ 8 * i + k ∧ 8 * i + k < dOff + n then
    extractByte S[(8 * i + k - dOff + sOff) / 8]! ((8 * i + k - dOff + sOff) % 8)
  else extractByte D[i]! k

/-- The `nw` destination cells after the copy. -/
def mcpyW (D S : List Word) (dOff sOff n nw : Nat) : List Word :=
  (List.range nw).map fun i => word8 (mcByte D S dOff sOff n i 0) (mcByte D S dOff sOff n i 1)
    (mcByte D S dOff sOff n i 2) (mcByte D S dOff sOff n i 3) (mcByte D S dOff sOff n i 4)
    (mcByte D S dOff sOff n i 5) (mcByte D S dOff sOff n i 6) (mcByte D S dOff sOff n i 7)

@[simp] theorem mcpyW_length (D S : List Word) (dOff sOff n nw : Nat) :
    (mcpyW D S dOff sOff n nw).length = nw := by simp [mcpyW]

theorem mcpyW_getElem! (D S : List Word) (dOff sOff n nw i : Nat) (h : i < nw) :
    (mcpyW D S dOff sOff n nw)[i]! = word8 (mcByte D S dOff sOff n i 0) (mcByte D S dOff sOff n i 1)
      (mcByte D S dOff sOff n i 2) (mcByte D S dOff sOff n i 3) (mcByte D S dOff sOff n i 4)
      (mcByte D S dOff sOff n i 5) (mcByte D S dOff sOff n i 6) (mcByte D S dOff sOff n i 7) := by
  simp [mcpyW, h]

attribute [byte_simp] mcpyW_getElem! mcByte Nat.reduceLeDiff and_self and_true and_false true_and false_and

theorem and7_of_sub2 {p : Word} (h : (p - 2#64).toNat % 8 = 0) : p &&& 7#64 = 2#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub] at h
  have := p.isLt
  simp only [BitVec.toNat_ofNat] at h ⊢
  omega

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 32)`, `dst` one byte and `src` two bytes into a doubleword. -/
theorem memcpy32_d1s2_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word)
    (d0 d1 d2 d3 d4 s0 s1 s2 s3 s4 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 32#64)
    (hD : Region (dst - 1#64) [d0, d1, d2, d3, d4] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (dst - 1#64) 5)
    (hS : Region (src - 2#64) [s0, s1, s2, s3, s4] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (src - 2#64) 5)
    (hdj : Disjoint (dst - 1#64) 5 (src - 2#64) 5)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 1#64, 5)] s t →
      Region (dst - 1#64) (mcpyW [d0, d1, d2, d3, d4] [s0, s1, s2, s3, s4] 1 2 32 5) t →
      SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst - 1#64, 5)] s
  have hm : dst &&& 7#64 = 1#64 := and7_of_sub1 hokD.aligned
  have hm2 : src &&& 7#64 = 2#64 := and7_of_sub2 hokS.aligned
  sym_exec
  have e : [v80, v97, v118, v136, v137] = mcpyW [d0, d1, d2, d3, d4] [s0, s1, s2, s3, s4] 1 2 32 5 := by
    sym_subst
    simp only [mcpyW, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
  rw [e] at hR0
  sym_close hk

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 17)`, both 8-aligned: two words and the low byte of the third cell. -/
theorem memcpy17_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (d0 d1 d2 s0 s1 s2 : Word)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 17#64)
    (hD : Region dst [d0, d1, d2] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 3)
    (hS : Region src [s0, s1, s2] s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 3)
    (hdj : Disjoint dst 3 src 3)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 3)] s t →
      Region dst [s0, s1, replaceByte d2 0 (extractByte s2 0)] t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst, 3)] s
  sym_exec
  sym_close hk
  sym_subst
  simp only [trunc8_zext]

end Cases.Zip2005
