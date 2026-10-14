import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Runtime.MemsetMore
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemcpyBytes
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Blake2b.Blake2bCompress_97
import Cases.Zip2005.Blake2b.PrfExpandSpec
import Cases.Zip2005.Image.F_7801d3d4
import Cases.Zip2005.Image.F_78032c1c
import Cases.Zip2005.Image.F_78032db4
import Cases.Zip2005.Image.F_78032fa4
import Cases.Zip2005.Image.Ro

/-!
# `zcash_spec::PrfExpand::apply`, two 32-byte inputs

`PrfExpand::<([u8; 32], [u8; 32])>::apply(sk, &[a, b])` for a 32-byte `sk`
(`ORCHARD_RIVK_INTERNAL`: `k`, `ak`, `nk`): 97 bytes, one block. As `Proof/Blake2b/PrfExpandWith.lean`, with
`update` of each input through `memcpy32_off1` (the buffer is one byte past alignment after the
domain separator) and the compression `Cases.Zip2005.compress1_97_spec`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

set_option asmverif.sym.foldBytes true in
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem prf_expand_apply2_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out d sk ts pa pb s0 s1 s2 s3 a0 a1 a2 a3
    b0 b1 b2 b3 : Word)
    (F1 F2 O : List Word) (hF1 : F1.length = 74) (hF2 : F2.length = 72) (hO : O.length = 8)
    (hpc : s.pc = 0x7801d3d4#64) (hcW : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x490 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = d) (ha2 : s.getReg .x12 = sk)
    (ha3 : s.getReg .x13 = 32#64) (ha4 : s.getReg .x14 = ts) (ha5 : s.getReg .x15 = 2#64)
    (hRF1 : Region (sp - 0x490#64) F1 s) (hRF2 : Region (sp - 0x240#64) F2 s)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hRT : Region ts [pa, 32#64, pb, 32#64] s) (hokT : RegionOk Ro.layout.roBase Ro.layout.textHi ts 4)
    (hRA : Region pa [a0, a1, a2, a3] s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi pa 4)
    (hRB : Region pb [b0, b1, b2, b3] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi pb 4)
    (hRO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 8)
    (hd1 : Disjoint (sp - 0x490#64) 146 sk 4) (hd2 : Disjoint (sp - 0x490#64) 146 out 8)
    (hd3 : Disjoint (sp - 0x490#64) 146 ts 4) (hd4 : Disjoint (sp - 0x490#64) 146 pa 4)
    (hd5 : Disjoint (sp - 0x490#64) 146 pb 4)
    (he1 : Disjoint out 8 sk 4) (he2 : Disjoint out 8 ts 4) (he3 : Disjoint out 8 pa 4) (he4 : Disjoint out 8 pb 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x490#64, 146), (out, 8)] s t →
      (compress prfH [s0, s1, s2, s3, (a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (a1 <<< 8) ||| (a0 >>> 56), (a2 <<< 8) ||| (a1 >>> 56), (a3 <<< 8) ||| (a2 >>> 56), (b0 <<< 8) ||| (a3 >>> 56), (b1 <<< 8) ||| (b0 >>> 56), (b2 <<< 8) ||| (b1 >>> 56), (b3 <<< 8) ||| (b2 >>> 56), b3 >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64).length = 8 →
      Region out (compress prfH [s0, s1, s2, s3, (a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (a1 <<< 8) ||| (a0 >>> 56), (a2 <<< 8) ||| (a1 >>> 56), (a3 <<< 8) ||| (a2 >>> 56), (b0 <<< 8) ||| (a3 >>> 56), (b1 <<< 8) ||| (b0 >>> 56), (b2 <<< 8) ||| (b1 >>> 56), (b3 <<< 8) ||| (b2 >>> 56), b3 >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x490#64) 146 := hstk.frame 146 (by decide)
  have hokW1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x490#64) 74 := hokW.sub' 0 74 (by decide) (by bv_omega)
  have hokW2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x240#64) 72 := hokW.sub' 74 72 (by decide) (by bv_omega)
  have hstkC : StackOk Ro.layout 0x250 (sp - 0x240#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0x240#64).toNat = sp.toNat - 0x240 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  have hlo := hstk.lo
  have hPers : Region 0x78001608#64 [0x78455f687361635a#64, 0x64656553646e6170#64] s :=
    (hro.get 11 (by decide)).sub 1 2 (by decide) rfl
  have hokPers : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001608#64 2 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 1 2 (by decide) (by decide)
  have hts : (ts + 16#64 == ts + 32#64) = false := by
    rw [beq_eq_false_iff_ne, ne_eq, BitVec.add_right_inj]; decide
  have hts2 : (ts + 32#64 == ts + 32#64) = true := beq_self_eq_true _
  have hu := Unchanged.refl [(sp - 0x490#64, 146), (out, 8)] s
  sym_exec [memset144_spec, memset128_spec, memcpy16_spec, memcpy32_spec, memcpy1_spec, memcpy0_spec,
    memcpy32_off1_spec, memcpy64_spec, compress1_97_spec]
  sym_close hk
  · exact compress_length _ _ _ _ _ _
  · simp only [← v479_def, ← v473_def, ← v478_def, ← v474_def, ← v477_def, ← v475_def, ← v476_def, ← v472_def, ← v465_def, ← v471_def, ← v466_def, ← v470_def, ← v467_def, ← v469_def, ← v468_def, ← v494_def, ← v488_def, ← v493_def, ← v489_def, ← v492_def, ← v490_def, ← v491_def, ← v487_def, ← v480_def, ← v486_def, ← v481_def, ← v485_def, ← v482_def, ← v484_def, ← v483_def, ← v509_def, ← v503_def, ← v508_def, ← v504_def, ← v507_def, ← v505_def, ← v506_def, ← v502_def, ← v495_def, ← v501_def, ← v496_def, ← v500_def, ← v497_def, ← v499_def, ← v498_def, ← v524_def, ← v518_def, ← v523_def, ← v519_def, ← v522_def, ← v520_def, ← v521_def, ← v517_def, ← v510_def, ← v516_def, ← v511_def, ← v515_def, ← v512_def, ← v514_def, ← v513_def, ← v539_def, ← v533_def, ← v538_def, ← v534_def, ← v537_def, ← v535_def, ← v536_def, ← v532_def, ← v525_def, ← v531_def, ← v526_def, ← v530_def, ← v527_def, ← v529_def, ← v528_def, ← v554_def, ← v548_def, ← v553_def, ← v549_def, ← v552_def, ← v550_def, ← v551_def, ← v547_def, ← v540_def, ← v546_def, ← v541_def, ← v545_def, ← v542_def, ← v544_def, ← v543_def, ← v569_def, ← v563_def, ← v568_def, ← v564_def, ← v567_def, ← v565_def, ← v566_def, ← v562_def, ← v555_def, ← v561_def, ← v556_def, ← v560_def, ← v557_def, ← v559_def, ← v558_def, ← v584_def, ← v578_def, ← v583_def, ← v579_def, ← v582_def, ← v580_def, ← v581_def, ← v577_def, ← v570_def, ← v576_def, ← v571_def, ← v575_def, ← v572_def, ← v574_def, ← v573_def, replaceBytes_word]
    rw [← v456_def, ← v457_def, ← v458_def, ← v459_def, ← v460_def, ← v461_def, ← v462_def, ← v463_def]
    have e89 : v89 = 0x510E527FADE682D1#64 := by rw [← v89_def, ← v85_def, ← acc22_0_def]; decide
    have e96 : v96 = 0x9B05688C2B3E6C1F#64 := by rw [← v96_def, ← v86_def, ← acc22_0_def]; decide
    have e4 : replaceByte acc105_0[4]! 0 (extractByte v191 0) &&& 255#64 = BitVec.zeroExtend 64 (BitVec.truncate 8 d) := by
      rw [← v191_def, AsmVerif.RiscV.Sym.extract1_replace1_self _ _ _ (by decide), replaceByte0_and_ff]
    have eH : [7640891576939301192#64, 13503953896175478587#64, 4354685564936845355#64, 11912009170470909681#64,
        0x510E527FADE682D1#64, 0x9B05688C2B3E6C1F#64, 7477812405655887409#64, 4577249634070577161#64] = prfH := by
      decide
    rw [e89, e96, e4, and_ff_of_up1, zext_extract_up1_last, eH]
    rfl

/-- `PrfExpand::apply(sk, &[a, b])` against `Zip2005.prfExpand`: the output bytes are
    `PRF^expand_sk([d] ‖ a ‖ b)`. -/
theorem prf_expand_apply2_correct {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out d sk ts pa pb s0 s1 s2 s3 a0 a1 a2 a3
    b0 b1 b2 b3 : Word)
    (F1 F2 O : List Word) (hF1 : F1.length = 74) (hF2 : F2.length = 72) (hO : O.length = 8)
    (hpc : s.pc = 0x7801d3d4#64) (hcW : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x490 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = d) (ha2 : s.getReg .x12 = sk)
    (ha3 : s.getReg .x13 = 32#64) (ha4 : s.getReg .x14 = ts) (ha5 : s.getReg .x15 = 2#64)
    (hRF1 : Region (sp - 0x490#64) F1 s) (hRF2 : Region (sp - 0x240#64) F2 s)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hRT : Region ts [pa, 32#64, pb, 32#64] s) (hokT : RegionOk Ro.layout.roBase Ro.layout.textHi ts 4)
    (hRA : Region pa [a0, a1, a2, a3] s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi pa 4)
    (hRB : Region pb [b0, b1, b2, b3] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi pb 4)
    (hRO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 8)
    (hd1 : Disjoint (sp - 0x490#64) 146 sk 4) (hd2 : Disjoint (sp - 0x490#64) 146 out 8)
    (hd3 : Disjoint (sp - 0x490#64) 146 ts 4) (hd4 : Disjoint (sp - 0x490#64) 146 pa 4)
    (hd5 : Disjoint (sp - 0x490#64) 146 pb 4)
    (he1 : Disjoint out 8 sk 4) (he2 : Disjoint out 8 ts 4) (he3 : Disjoint out 8 pa 4) (he4 : Disjoint out 8 pb 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x490#64, 146), (out, 8)] s t → ∀ O' : List Word, Region out O' t →
      Zip2005.Blake2b.stateBytes (O'.map BitVec.toNat) =
        Zip2005.prfExpand (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
          ([UInt8.ofNat d.toNat] ++ Zip2005.Blake2b.stateBytes ([a0, a1, a2, a3].map BitVec.toNat) ++
            Zip2005.Blake2b.stateBytes ([b0, b1, b2, b3].map BitVec.toNat)) →
      SafeN G n P t) :
    SafeN G n P s :=
  prf_expand_apply2_spec s ra sp out d sk ts pa pb s0 s1 s2 s3 a0 a1 a2 a3 b0 b1 b2 b3 F1 F2 O hF1 hF2 hO hpc
    hcW hcT hcU hcF hcL hcM hcC hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 ha4 ha5 hRF1 hRF2 hRS hokS hRT hokT
    hRA hokA hRB hokB hRO hokO hd1 hd2 hd3 hd4 hd5 he1 he2 he3 he4
    (fun t tpc tcs tcode tU _ tR => hk t tpc tcs tcode tU _ tR (prfExpand97_eq s0 s1 s2 s3 a0 a1 a2 a3 b0 b1 b2 b3 d))

end Cases.Zip2005
