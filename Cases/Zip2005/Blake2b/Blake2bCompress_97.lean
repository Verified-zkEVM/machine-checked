import Cases.Zip2005.Blake2b.Seg1_97
import Cases.Zip2005.Blake2b.Seg2
import Cases.Zip2005.Blake2b.Seg3
import Cases.Zip2005.Image.Ro

/-!
# `blake2b_simd::portable::compress1_loop`, a partial block of 97 bytes (12 words and one byte, zero-padded to the block)

The portable BLAKE2b compression loop on a 97-byte input with the serial stride (`a7 = 0`):
one iteration over the final block, which `memset`/`memcpy97` assemble in the frame buffer: the input's 12 words, its byte 96 in the low byte of word 12, zeros above, the eight state words replaced by `Cases.Zip2005.B2b.compress` of the state, the block, the counter
advanced by 97 and the two flag words (`finalize` and `last_node`, each `0` for yes and `1` for no as the
`Finalize`/`LastNode` enums are laid out, so the flag *word* is the enum minus one).

Three segments (`Proof/Blake2b/Seg1_97.lean`, `Seg2.lean`, `Seg3.lean`; generated from the executor trace)
meet at the ends of rounds 3 and 7 with the sixteen work-vector words, the sixteen message words and the
frame passed cell by cell, together with the model equation for the rounds done so far.
`Proof/Blake2b/Blake2bSpec.lean` relates `Cases.Zip2005.B2b.compress` to `Zip2005.Blake2b.compress`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

/-- `compress1_loop(input, words, count, last_node, finalize, Serial)` with a 97-byte input. -/
theorem compress1_97_spec {P : Prop} (s : MachineState) (ra sp blk wp c0 c1 ln fz : Word)
    (h0 h1 h2 h3 h4 h5 h6 h7 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 : Word) (F : List Word) (hF : F.length = 74)
    (hpc : s.pc = 0x78033260#64) (hcode : CodeAt F_78033260.base F_78033260.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x250 sp)
    (ha0 : s.getReg .x10 = blk) (ha1 : s.getReg .x11 = 97#64) (ha2 : s.getReg .x12 = wp)
    (ha3 : s.getReg .x13 = c0) (ha4 : s.getReg .x14 = c1) (ha5 : s.getReg .x15 = ln)
    (ha6 : s.getReg .x16 = fz) (ha7 : s.getReg .x17 = 0#64)
    (hRF : Region (sp - 0x250#64) F s)
    (hRB : Region blk [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi blk 13)
    (hRH : Region wp [h0, h1, h2, h3, h4, h5, h6, h7] s) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi wp 8)
    (hd1 : Disjoint (sp - 0x250#64) 74 blk 13) (hd2 : Disjoint (sp - 0x250#64) 74 wp 8)
    (hd3 : Disjoint wp 8 blk 13)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(sp - 0x250#64, 74), (wp, 8)] s t →
      (compress [h0, h1, h2, h3, h4, h5, h6, h7] [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, (BitVec.zeroExtend 64 (extractByte i12 0)), 0#64, 0#64, 0#64] (c0 + 97#64) (c1 + (if (c0 + 97#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64)).length = 8 →
      Region wp (compress [h0, h1, h2, h3, h4, h5, h6, h7] [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, (BitVec.zeroExtend 64 (extractByte i12 0)), 0#64, 0#64, 0#64] (c0 + 97#64) (c1 + (if (c0 + 97#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64)) t → Safe P t) :
    Safe P s := by
  refine compress1_seg1_97 s ra sp blk wp c0 c1 ln fz h0 h1 h2 h3 h4 h5 h6 h7 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 F hF hpc hcode hcodeS hcodeC hcw hro hra hsp hstk
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hRF hRB hokB hRH hokH hd1 hd2 hd3 ?_
  intro u w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 upc ucode ucA ucw ux2 ux3 ux4 ux1 ux5 ux6 ux7 ux8 ux9 ux10 ux11 ux12 ux13 ux14 ux15 ux16 ux17 ux18 ux19 ux20 ux21 ux22 ux23 ux24 ux25 ux26 ux27 ux28 ux29 ux30 ux31 uU uF uH hV4
  refine compress1_seg2 u ra sp wp (c0 + 97#64) (c1 + (if (c0 + 97#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64) h0 h1 h2 h3 h4 h5 h6 h7 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 (BitVec.zeroExtend 64 (extractByte i12 0)) 0#64 0#64 0#64 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 (s.getReg .x27) (s.getReg .x26) (s.getReg .x25) (s.getReg .x24) (s.getReg .x23) (s.getReg .x22) (s.getReg .x21) (s.getReg .x20) (s.getReg .x19) (s.getReg .x18) (s.getReg .x9) (s.getReg .x8)
    upc ucA ucw hstk (ux2.trans (by bv_omega : sp + 18446744073709551024#64 = sp - 0x250#64))
    ux1 ux5 ux6 ux7 ux8 ux9 ux10 ux11 ux12 ux13 ux14 ux15 ux16 ux17 ux18 ux19 ux20 ux21 ux22 ux23 ux24 ux25 ux26 ux27 ux28 ux29 ux30 ux31 uF uH hokH hd2 hV4 ?_
  intro v w0' w1' w2' w3' w4' w5' w6' w7' w8' w9' w10' w11' w12' w13' w14' w15' g0' g1' g2' g3' g4' g5' g6' g7' g8' g9' g10' g11' g12' g13' g14' g15' g16' g17' g18' g19' g20' g21' g22' g23' g24' g25' g26' g27' vpc vcode vcA vcw vx2 vx3 vx4 vx1 vx5 vx6 vx7 vx8 vx9 vx10 vx11 vx12 vx13 vx14 vx15 vx16 vx17 vx18 vx19 vx20 vx21 vx22 vx23 vx24 vx25 vx26 vx27 vx28 vx29 vx30 vx31 vU vF vH hV8
  refine compress1_seg3 v ra sp wp (c0 + 97#64) (c1 + (if (c0 + 97#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64) h0 h1 h2 h3 h4 h5 h6 h7 i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 (BitVec.zeroExtend 64 (extractByte i12 0)) 0#64 0#64 0#64 w0' w1' w2' w3' w4' w5' w6' w7' w8' w9' w10' w11' w12' w13' w14' w15' g0' g1' g2' g3' g4' g5' g6' g7' g8' g9' g10' g11' g12' g13' g14' g15' g16' g17' g18' g19' g20' g21' g22' g23' g24' g25' g26' g27' (s.getReg .x27) (s.getReg .x26) (s.getReg .x25) (s.getReg .x24) (s.getReg .x23) (s.getReg .x22) (s.getReg .x21) (s.getReg .x20) (s.getReg .x19) (s.getReg .x18) (s.getReg .x9) (s.getReg .x8)
    vpc vcA vcw hra1 hstk (vx2.trans (by bv_omega : sp + 18446744073709551024#64 = sp - 0x250#64))
    vx1 vx5 vx6 vx7 vx8 vx9 vx10 vx11 vx12 vx13 vx14 vx15 vx16 vx17 vx18 vx19 vx20 vx21 vx22 vx23 vx24 vx25 vx26 vx27 vx28 vx29 vx30 vx31 vF vH hokH hd2 hV8 ?_
  intro z o0 o1 o2 o3 o4 o5 o6 o7 zpc zcode zx2 zx3 zx4 zx8 zx9 zx18 zx19 zx20 zx21 zx22 zx23 zx24 zx25 zx26 zx27 zU zO hC
  exact hk z zpc
    (CalleeSaved.intro (zx2.trans hsp.symm) (zx3.trans (vx3.trans ux3)) (zx4.trans (vx4.trans ux4))
      zx8 zx9 zx18 zx19 zx20 zx21 zx22 zx23 zx24 zx25 zx26 zx27)
    (zcode.trans (vcode.trans ucode)) (uU.trans (vU.trans zU)) (compress_length _ _ _ _ _ _) (by rw [hC]; exact zO)

end Cases.Zip2005
