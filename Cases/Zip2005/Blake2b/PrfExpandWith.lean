import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Runtime.MemsetMore
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemcpyBytes
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Blake2b.Blake2bCompress_33
import Cases.Zip2005.Blake2b.PrfExpandSpec
import Cases.Zip2005.Image.F_78023308
import Cases.Zip2005.Image.F_78032c1c
import Cases.Zip2005.Image.F_78032db4
import Cases.Zip2005.Image.F_78032fa4
import Cases.Zip2005.Image.Ro

/-!
# `zcash_spec::PrfExpand::with`, no extra inputs

`PrfExpand::<()>::with(sk, &[])` for a 32-byte `sk` (`ORCHARD_ASK`, `ORCHARD_NK`, `ORCHARD_RIVK`):
`Params::new().hash_length(64).personal("Zcash_ExpandSeed").to_state()`, `update(sk)`,
`update(&[d])`, `finalize()`, the 64-byte hash copied out. `to_state`, both `update`s (which only
buffer: 32 and then 33 bytes) and `finalize` run inline; the compression is
`Cases.Zip2005.compress1_33_spec`. The output is `Cases.Zip2005.B2b.compress prfH M 33 0 (all ones) 0`, which
`Cases.Zip2005.B2b.prfExpand33_eq` serialises to `Zip2005.prfExpand sk [d]`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

set_option asmverif.sym.foldBytes true in
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem prf_expand_with_spec {P : Prop} (s : MachineState) (ra sp out d sk s0 s1 s2 s3 : Word)
    (F1 F2 O : List Word) (hF1 : F1.length = 74) (hF2 : F2.length = 70) (hO : O.length = 8)
    (hpc : s.pc = 0x78023308#64) (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x480 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = d) (ha2 : s.getReg .x12 = sk)
    (ha3 : s.getReg .x13 = 32#64)
    (hRF1 : Region (sp - 0x480#64) F1 s) (hRF2 : Region (sp - 0x230#64) F2 s)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hRO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 8)
    (hd1 : Disjoint (sp - 0x480#64) 144 sk 4) (hd2 : Disjoint (sp - 0x480#64) 144 out 8)
    (hd3 : Disjoint out 8 sk 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x480#64, 144), (out, 8)] s t →
      (compress prfH [s0, s1, s2, s3, BitVec.zeroExtend 64 (BitVec.truncate 8 d),
        0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]
        33#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64).length = 8 →
      Region out (compress prfH [s0, s1, s2, s3, BitVec.zeroExtend 64 (BitVec.truncate 8 d),
        0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]
        33#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x480#64) 144 := hstk.frame 144 (by decide)
  have hokW1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x480#64) 74 := hokW.sub' 0 74 (by decide) (by bv_omega)
  have hokW2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x230#64) 70 := hokW.sub' 74 70 (by decide) (by bv_omega)
  have hstkC : StackOk Ro.layout 0x250 (sp - 0x230#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0x230#64).toNat = sp.toNat - 0x230 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  have hlo := hstk.lo
  have hPers : Region 0x78001608#64 [0x78455f687361635a#64, 0x64656553646e6170#64] s :=
    (hro.get 11 (by decide)).sub 1 2 (by decide) rfl
  have hokPers : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001608#64 2 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 1 2 (by decide) (by decide)
  have hu := Unchanged.refl [(sp - 0x480#64, 144), (out, 8)] s
  sym_exec [memset144_spec, memset128_spec, memcpy16_spec, memcpy32_spec, memcpy1_spec, memcpy0_spec,
    memcpy64_spec, compress1_33_spec]
  sym_close hk
  · exact compress_length _ _ _ _ _ _
  · simp only [← v322_def, ← v316_def, ← v321_def, ← v317_def, ← v320_def, ← v318_def, ← v319_def, ← v315_def, ← v308_def, ← v314_def, ← v309_def, ← v313_def, ← v310_def, ← v312_def, ← v311_def, ← v337_def, ← v331_def, ← v336_def, ← v332_def, ← v335_def, ← v333_def, ← v334_def, ← v330_def, ← v323_def, ← v329_def, ← v324_def, ← v328_def, ← v325_def, ← v327_def, ← v326_def, ← v352_def, ← v346_def, ← v351_def, ← v347_def, ← v350_def, ← v348_def, ← v349_def, ← v345_def, ← v338_def, ← v344_def, ← v339_def, ← v343_def, ← v340_def, ← v342_def, ← v341_def, ← v367_def, ← v361_def, ← v366_def, ← v362_def, ← v365_def, ← v363_def, ← v364_def, ← v360_def, ← v353_def, ← v359_def, ← v354_def, ← v358_def, ← v355_def, ← v357_def, ← v356_def, ← v382_def, ← v376_def, ← v381_def, ← v377_def, ← v380_def, ← v378_def, ← v379_def, ← v375_def, ← v368_def, ← v374_def, ← v369_def, ← v373_def, ← v370_def, ← v372_def, ← v371_def, ← v397_def, ← v391_def, ← v396_def, ← v392_def, ← v395_def, ← v393_def, ← v394_def, ← v390_def, ← v383_def, ← v389_def, ← v384_def, ← v388_def, ← v385_def, ← v387_def, ← v386_def, ← v412_def, ← v406_def, ← v411_def, ← v407_def, ← v410_def, ← v408_def, ← v409_def, ← v405_def, ← v398_def, ← v404_def, ← v399_def, ← v403_def, ← v400_def, ← v402_def, ← v401_def, ← v427_def, ← v421_def, ← v426_def, ← v422_def, ← v425_def, ← v423_def, ← v424_def, ← v420_def, ← v413_def, ← v419_def, ← v414_def, ← v418_def, ← v415_def, ← v417_def, ← v416_def, replaceBytes_word]
    rw [← v299_def, ← v300_def, ← v301_def, ← v302_def, ← v303_def, ← v304_def, ← v305_def, ← v306_def]
    have e85 : v85 = 0x510E527FADE682D1#64 := by rw [← v85_def, ← v81_def, ← acc18_0_def]; decide
    have e92 : v92 = 0x9B05688C2B3E6C1F#64 := by rw [← v92_def, ← v82_def, ← acc18_0_def]; decide
    have e4 : BitVec.zeroExtend 64 (extractByte (replaceByte acc101_0[4]! 0 (extractByte v187 0)) 0) =
        BitVec.zeroExtend 64 (BitVec.truncate 8 d) := by
      rw [AsmVerif.RiscV.Sym.extract1_replace1_self _ _ _ (by decide), ← v187_def, AsmVerif.RiscV.Sym.extract1_replace1_self _ _ _ (by decide)]
    have eH : [7640891576939301192#64, 13503953896175478587#64, 4354685564936845355#64, 11912009170470909681#64,
        0x510E527FADE682D1#64, 0x9B05688C2B3E6C1F#64, 7477812405655887409#64, 4577249634070577161#64] = prfH := by
      decide
    rw [e85, e92, e4, eH]
    rfl

/-- `PrfExpand::with(sk, &[])` against the specification: the 64 output bytes are
    `PRF^expand_sk([d])` (protocol specification § 4.1.2). -/
theorem prf_expand_with_correct {P : Prop} (s : MachineState) (ra sp out d sk s0 s1 s2 s3 : Word)
    (F1 F2 O : List Word) (hF1 : F1.length = 74) (hF2 : F2.length = 70) (hO : O.length = 8)
    (hpc : s.pc = 0x78023308#64) (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x480 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = d) (ha2 : s.getReg .x12 = sk)
    (ha3 : s.getReg .x13 = 32#64)
    (hRF1 : Region (sp - 0x480#64) F1 s) (hRF2 : Region (sp - 0x230#64) F2 s)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hRO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 8)
    (hd1 : Disjoint (sp - 0x480#64) 144 sk 4) (hd2 : Disjoint (sp - 0x480#64) 144 out 8)
    (hd3 : Disjoint out 8 sk 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x480#64, 144), (out, 8)] s t → ∀ O' : List Word, Region out O' t →
      Zip2005.Blake2b.stateBytes (O'.map BitVec.toNat) =
        Zip2005.prfExpand (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat)) [UInt8.ofNat d.toNat] →
      Safe P t) :
    Safe P s :=
  prf_expand_with_spec s ra sp out d sk s0 s1 s2 s3 F1 F2 O hF1 hF2 hO hpc hcW hcT hcU hcF hcL hcM hcC hcw hro
    hra hra1 hsp hstk ha0 ha1 ha2 ha3 hRF1 hRF2 hRS hokS hRO hokO hd1 hd2 hd3
    (fun t tpc tcs tcode tU _ tR => hk t tpc tcs tcode tU _ tR (prfExpand33_eq s0 s1 s2 s3 d))

end Cases.Zip2005
