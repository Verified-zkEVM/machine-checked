import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Runtime.MemsetMore
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemcpyBytes
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Blake2b.Blake2bCompress_65
import Cases.Zip2005.Blake2b.PrfExpandSpec
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Field.FromUniform
import Cases.Zip2005.Blake2b.SpecBridge
import Cases.Zip2005.Spec.Zip2005.Sending
import Cases.Zip2005.Image.F_7801d51c
import Cases.Zip2005.Image.F_78032c1c
import Cases.Zip2005.Image.F_78032db4
import Cases.Zip2005.Image.F_78032fa4
import Cases.Zip2005.Image.Ro

/-!
# `orchard::note::RandomSeed::psi`

`rseed.psi(rho) = ToBase^Orchard(PRF^expand_rseed([9] ‖ rho.to_repr()))`: the BLAKE2b hasher of
`PrfExpand::apply` inlined (`Params`, `to_state`, three `update`s of 32, 1 and 32 bytes, `finalize`:
65 bytes, one block, `compress1_65_spec`), the 64 output bytes re-read as eight words, then
`Fp::from_uniform_bytes`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

set_option machineChecked.sym.foldBytes true in
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem psi_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out rs rho s0 s1 s2 s3 p0 p1 p2 p3 : Word)
    (F1 F3 F2 : List Word) (hF1 : F1.length = 74) (hF3 : F3.length = 12) (hF2 : F2.length = 68)
    (hpc : s.pc = 0x7801d51c#64) (hcP : CodeAt F_7801d51c.base F_7801d51c.prog s)
    (hcR : CodeAt F_78029468.base F_78029468.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcX : CodeAt F_7802e2b4.base F_7802e2b4.prog s) (hcX2 : CodeAt F_78028718.base F_78028718.prog s)
    (hcX3 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = rs) (ha2 : s.getReg .x12 = rho)
    (hRF1 : Region (sp - 0x4d0#64) F1 s) (hRF3 : Region (sp - 0x280#64) F3 s) (hRF2 : Region (sp - 0x220#64) F2 s)
    (hRS : Region rs [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi rs 4)
    (hRP : Region rho [p0, p1, p2, p3] s) (hokP : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x4d0#64) 154 rs 4) (hd2 : Disjoint (sp - 0x4d0#64) 154 out 4)
    (hd3 : Disjoint (sp - 0x4d0#64) 154 rho 4)
    (he1 : Disjoint out 4 rs 4) (he2 : Disjoint out 4 rho 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4d0#64, 154), (out, 4)] s t →
      Region out (natToLeLimbs 4 (Fp.add (Fp.mul (leLimbsToNat [(compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[0]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[1]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[2]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[3]!]) Fp.R2) (Fp.mul (leLimbsToNat [(compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[4]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[5]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[6]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[7]!]) Fp.R3))) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4d0#64) 154 := hstk.frame 154 (by decide)
  have hokW1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4d0#64) 74 := hokW.sub' 0 74 (by decide) (by bv_omega)
  have hokW3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x280#64) 12 := hokW.sub' 74 12 (by decide) (by bv_omega)
  have hokW2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x220#64) 68 := hokW.sub' 86 68 (by decide) (by bv_omega)
  have hstkC : StackOk Ro.layout 0x2b0 (sp - 0x220#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0x220#64).toNat = sp.toNat - 0x220 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  have hlo := hstk.lo
  have hokO' := hokO.toText
  have hPers : Region 0x78001608#64 [0x78455f687361635a#64, 0x64656553646e6170#64] s :=
    (hro.get 11 (by decide)).sub 1 2 (by decide) rfl
  have hokPers : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001608#64 2 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 1 2 (by decide) (by decide)
  have hu := Unchanged.refl [(sp - 0x4d0#64, 154), (out, 4)] s
  sym_exec [fp_to_repr_spec, memset144_spec, memset128_spec, memcpy16_spec, memcpy32_spec, memcpy1_spec,
    memcpy0_spec, memcpy32_off1_spec, memcpy64_spec, compress1_65_spec, fp_from_uniform_bytes_spec]
  sym_close hk
  have w0 : v695 = v381 := by
    rw [← v695_def, ← v694_def, ← v693_def, ← v692_def, ← v691_def, ← v690_def, ← v689_def, ← v688_def, ← v687_def, ← v686_def, ← v685_def, ← v684_def, ← v683_def, ← v682_def, ← v681_def, ← v680_def, ← v679_def, ← v678_def, ← v677_def, ← v676_def, ← v675_def, ← v674_def, ← v400_def, ← v399_def, ← v398_def, ← v393_def, ← v392_def, ← v391_def, ← v390_def]; exact pack_shift _
  have w1 : v673 = v382 := by
    rw [← v673_def, ← v672_def, ← v671_def, ← v670_def, ← v669_def, ← v668_def, ← v667_def, ← v666_def, ← v665_def, ← v664_def, ← v663_def, ← v662_def, ← v661_def, ← v660_def, ← v659_def, ← v658_def, ← v657_def, ← v656_def, ← v655_def, ← v654_def, ← v653_def, ← v652_def, ← v415_def, ← v414_def, ← v413_def, ← v408_def, ← v407_def, ← v406_def, ← v405_def]; exact pack_shift _
  have w2 : v651 = v383 := by
    rw [← v651_def, ← v650_def, ← v649_def, ← v648_def, ← v647_def, ← v646_def, ← v645_def, ← v644_def, ← v643_def, ← v642_def, ← v641_def, ← v640_def, ← v639_def, ← v638_def, ← v637_def, ← v636_def, ← v635_def, ← v634_def, ← v633_def, ← v632_def, ← v631_def, ← v630_def, ← v430_def, ← v429_def, ← v428_def, ← v423_def, ← v422_def, ← v421_def, ← v420_def]; exact pack_shift _
  have w3 : v629 = v384 := by
    rw [← v629_def, ← v628_def, ← v627_def, ← v626_def, ← v625_def, ← v624_def, ← v623_def, ← v622_def, ← v621_def, ← v620_def, ← v619_def, ← v618_def, ← v617_def, ← v616_def, ← v615_def, ← v614_def, ← v613_def, ← v612_def, ← v611_def, ← v610_def, ← v609_def, ← v608_def, ← v445_def, ← v444_def, ← v443_def, ← v438_def, ← v437_def, ← v436_def, ← v435_def]; exact pack_shift _
  have w4 : v603 = v385 := by
    rw [← v603_def, ← v602_def, ← v601_def, ← v600_def, ← v599_def, ← v598_def, ← v597_def, ← v596_def, ← v595_def, ← v594_def, ← v593_def, ← v592_def, ← v591_def, ← v590_def, ← v589_def, ← v588_def, ← v587_def, ← v586_def, ← v585_def, ← v584_def, ← v583_def, ← v582_def, ← v460_def, ← v459_def, ← v458_def, ← v453_def, ← v452_def, ← v451_def, ← v450_def]; exact pack_shift _
  have w5 : v581 = v386 := by
    rw [← v581_def, ← v580_def, ← v579_def, ← v578_def, ← v577_def, ← v576_def, ← v575_def, ← v574_def, ← v573_def, ← v572_def, ← v571_def, ← v570_def, ← v569_def, ← v568_def, ← v567_def, ← v566_def, ← v565_def, ← v564_def, ← v563_def, ← v562_def, ← v561_def, ← v560_def, ← v475_def, ← v474_def, ← v473_def, ← v468_def, ← v467_def, ← v466_def, ← v465_def]; exact pack_shift _
  have w6 : v559 = v387 := by
    rw [← v559_def, ← v558_def, ← v557_def, ← v556_def, ← v555_def, ← v554_def, ← v553_def, ← v552_def, ← v551_def, ← v550_def, ← v549_def, ← v548_def, ← v547_def, ← v546_def, ← v545_def, ← v544_def, ← v543_def, ← v542_def, ← v541_def, ← v540_def, ← v539_def, ← v538_def, ← v490_def, ← v489_def, ← v488_def, ← v483_def, ← v482_def, ← v481_def, ← v480_def]; exact pack_shift _
  have w7 : v537 = v388 := by
    rw [← v537_def, ← v536_def, ← v535_def, ← v534_def, ← v533_def, ← v532_def, ← v531_def, ← v530_def, ← v529_def, ← v528_def, ← v527_def, ← v526_def, ← v525_def, ← v524_def, ← v523_def, ← v522_def, ← v521_def, ← v520_def, ← v519_def, ← v518_def, ← v517_def, ← v516_def, ← v505_def, ← v504_def, ← v503_def, ← v498_def, ← v497_def, ← v496_def, ← v495_def]; exact pack_shift _
  have e94 : v94 = 0x510E527FADE682D1#64 := by rw [← v94_def, ← v90_def, ← acc27_0_def]; decide
  have e101 : v101 = 0x9B05688C2B3E6C1F#64 := by rw [← v101_def, ← v91_def, ← acc27_0_def]; decide
  have e4 : replaceByte acc110_0[4]! 0 (extractByte v197 0) &&& 255#64 = BitVec.zeroExtend 64 (BitVec.truncate 8 9#64) := by
    rw [← v197_def, MachineChecked.RiscV.Sym.extract1_replace1_self _ _ _ (by decide), replaceByte0_and_ff]
  have eH : [7640891576939301192#64, 13503953896175478587#64, 4354685564936845355#64, 11912009170470909681#64,
      0x510E527FADE682D1#64, 0x9B05688C2B3E6C1F#64, 7477812405655887409#64, 4577249634070577161#64] = prfH := by
    decide
  have hv : [v381, v382, v383, v384, v385, v386, v387, v388] = compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64 := by
    rw [← v381_def, ← v382_def, ← v383_def, ← v384_def, ← v385_def, ← v386_def, ← v387_def, ← v388_def, e94, e101,
      e4, zext_extract_up1_last, eH, ← acc19_0_def]
    rfl
  rw [← acc704_0_def, w0, w1, w2, w3, w4, w5, w6, w7, hv]

/-- `rseed.psi(rho)` against the specification: for `rho` stored as the Montgomery form of `ρ`, the
    result is the Montgomery form of `Zip2005.hPsiOrchard rseed ρ`. -/
theorem psi_correct {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out rs rho s0 s1 s2 s3 p0 p1 p2 p3 : Word)
    (F1 F3 F2 : List Word) (hF1 : F1.length = 74) (hF3 : F3.length = 12) (hF2 : F2.length = 68)
    (hpc : s.pc = 0x7801d51c#64) (hcP : CodeAt F_7801d51c.base F_7801d51c.prog s)
    (hcR : CodeAt F_78029468.base F_78029468.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcX : CodeAt F_7802e2b4.base F_7802e2b4.prog s) (hcX2 : CodeAt F_78028718.base F_78028718.prog s)
    (hcX3 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = rs) (ha2 : s.getReg .x12 = rho)
    (hRF1 : Region (sp - 0x4d0#64) F1 s) (hRF3 : Region (sp - 0x280#64) F3 s) (hRF2 : Region (sp - 0x220#64) F2 s)
    (hRS : Region rs [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi rs 4)
    (hRP : Region rho [p0, p1, p2, p3] s) (hokP : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x4d0#64) 154 rs 4) (hd2 : Disjoint (sp - 0x4d0#64) 154 out 4)
    (hd3 : Disjoint (sp - 0x4d0#64) 154 rho 4)
    (he1 : Disjoint out 4 rs 4) (he2 : Disjoint out 4 rho 4)
    (ρ : Zcash.Circuits.Fp) (hp : leLimbsToNat [p0, p1, p2, p3] = ρ.val * Fp.R % Fp.p)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4d0#64, 154), (out, 4)] s t → ∀ x : Nat, Region out (natToLeLimbs 4 x) t →
      x = (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat)) ρ).val * Fp.R % Fp.p →
      SafeN G n P t) :
    SafeN G n P s := by
  refine psi_spec s ra sp out rs rho s0 s1 s2 s3 p0 p1 p2 p3 F1 F3 F2 hF1 hF3 hF2 hpc hcP hcR hcT hcU hcF hcL hcM hcC hcX hcX2 hcX3 hcw hro hra hra1 hsp hstk ha0 ha1 ha2 hRF1 hRF3 hRF2 hRS hokS hRP hokP hokO hd1 hd2 hd3 he1 he2 (fun t a b c d hR => hk t a b c d _ hR ?_)
  have hpl : ρ.val < Fp.p := ZMod.val_lt ρ
  have eP : leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p = ρ.val := by
    rw [hp, Fp.mont_back, Nat.mod_eq_of_lt hpl]
  have eL : ∀ v, (natToLeLimbs 4 v).map BitVec.toNat =
      [(natToLeLimbs 4 v)[0]!.toNat, (natToLeLimbs 4 v)[1]!.toNat, (natToLeLimbs 4 v)[2]!.toNat,
        (natToLeLimbs 4 v)[3]!.toNat] := fun _ => rfl
  have hO := prfExpand65_eq s0 s1 s2 s3 (natToLeLimbs 4 ρ.val)[0]! (natToLeLimbs 4 ρ.val)[1]!
    (natToLeLimbs 4 ρ.val)[2]! (natToLeLimbs 4 ρ.val)[3]! 9#64
  simp only [List.map_cons, List.map_nil] at hO
  rw [eP, Fp.from_uniform_eq, leLimbsToNat_halves _ (compress_length _ _ _ _ _ _)]
  unfold Zip2005.hPsiOrchard Zip2005.rhoBytes
  rw [toBaseOrchard_val, Nat.mod_mul_mod, i2leosp256_limbs _ (by have := Fp.p_lt; omega), eL,
    show Zip2005.Sep.psiOrchard = UInt8.ofNat (9#64).toNat from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [← hO, leos2ip_stateBytes]

end Cases.Zip2005
