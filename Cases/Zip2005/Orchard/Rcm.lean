import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Runtime.MemsetMore
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemcpyBytes
import Cases.Zip2005.Runtime.MemcpyRcm
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Blake2b.Blake2bCompress
import Cases.Zip2005.Blake2b.Blake2bCompress_41
import Cases.Zip2005.Blake2b.PrfExpandSpec
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Curve.ToBytes
import Cases.Zip2005.Field.FqFromUniform
import Cases.Zip2005.Blake2b.PrfExpand169
import Cases.Zip2005.Blake2b.SpecBridge
import Cases.Zip2005.Spec.Zip2005.Sending
import Cases.Zip2005.Image.F_7801d92c
import Cases.Zip2005.Image.F_78032c1c
import Cases.Zip2005.Image.F_78032db4
import Cases.Zip2005.Image.F_78032fa4
import Cases.Zip2005.Image.Ro

/-!
# `orchard::note::RandomSeed::rcm_v3`

`rseed.rcm_v3(rho, g_d, pk_d, v, psi) = ToScalar^Orchard(PRF^expand_rseed([0x0B] ‖ repr(g_d) ‖
repr(pk_d) ‖ I2LEOSP₆₄(v) ‖ rho ‖ psi))`: 169 bytes, two BLAKE2b blocks. The hasher runs inline;
`update` compresses the first (full, not final) block when `rho` arrives (`compress1_128_spec'`),
`finalize` the 41-byte tail (`compress1_41_spec'`). The encodings of `g_d`, `pk_d`, `rho`, `psi`
are named `G`, `K`, `R`, `Q` and tied to their callees' results by hypotheses.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

/-- `compress1_128_spec` with its stack frame taken as whatever the memory holds. -/
theorem compress1_128_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp blk wp c0 c1 ln fz : Word)
    (h0 h1 h2 h3 h4 h5 h6 h7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word)
    (hpc : s.pc = 0x78033260#64) (hcode : CodeAt F_78033260.base F_78033260.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x250 sp)
    (ha0 : s.getReg .x10 = blk) (ha1 : s.getReg .x11 = 128#64) (ha2 : s.getReg .x12 = wp)
    (ha3 : s.getReg .x13 = c0) (ha4 : s.getReg .x14 = c1) (ha5 : s.getReg .x15 = ln)
    (ha6 : s.getReg .x16 = fz) (ha7 : s.getReg .x17 = 0#64)
    (hRB : Region blk [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi blk 16)
    (hRH : Region wp [h0, h1, h2, h3, h4, h5, h6, h7] s) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi wp 8)
    (hd1 : Disjoint (sp - 0x250#64) 74 blk 16) (hd2 : Disjoint (sp - 0x250#64) 74 wp 8)
    (hd3 : Disjoint wp 8 blk 16)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(sp - 0x250#64, 74), (wp, 8)] s t →
      (compress [h0, h1, h2, h3, h4, h5, h6, h7] [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] (c0 + 128#64) (c1 + (if (c0 + 128#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64)).length = 8 →
      Region wp (compress [h0, h1, h2, h3, h4, h5, h6, h7] [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] (c0 + 128#64) (c1 + (if (c0 + 128#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64)) t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hRF, hF⟩ := Region.exists_junk (sp - 0x250#64) 74 s
  exact compress1_128_spec s ra sp blk wp c0 c1 ln fz h0 h1 h2 h3 h4 h5 h6 h7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 F hF hpc hcode hcodeS hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hRF hRB hokB hRH hokH hd1 hd2 hd3 hk

/-- `compress1_41_spec` with its stack frame taken as whatever the memory holds. -/
theorem compress1_41_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp blk wp c0 c1 ln fz : Word)
    (h0 h1 h2 h3 h4 h5 h6 h7 i0 i1 i2 i3 i4 i5 : Word)
    (hpc : s.pc = 0x78033260#64) (hcode : CodeAt F_78033260.base F_78033260.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x250 sp)
    (ha0 : s.getReg .x10 = blk) (ha1 : s.getReg .x11 = 41#64) (ha2 : s.getReg .x12 = wp)
    (ha3 : s.getReg .x13 = c0) (ha4 : s.getReg .x14 = c1) (ha5 : s.getReg .x15 = ln)
    (ha6 : s.getReg .x16 = fz) (ha7 : s.getReg .x17 = 0#64)
    (hRB : Region blk [i0, i1, i2, i3, i4, i5] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi blk 6)
    (hRH : Region wp [h0, h1, h2, h3, h4, h5, h6, h7] s) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi wp 8)
    (hd1 : Disjoint (sp - 0x250#64) 74 blk 6) (hd2 : Disjoint (sp - 0x250#64) 74 wp 8)
    (hd3 : Disjoint wp 8 blk 6)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(sp - 0x250#64, 74), (wp, 8)] s t →
      (compress [h0, h1, h2, h3, h4, h5, h6, h7] [i0, i1, i2, i3, i4, (BitVec.zeroExtend 64 (extractByte i5 0)), 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] (c0 + 41#64) (c1 + (if (c0 + 41#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64)).length = 8 →
      Region wp (compress [h0, h1, h2, h3, h4, h5, h6, h7] [i0, i1, i2, i3, i4, (BitVec.zeroExtend 64 (extractByte i5 0)), 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] (c0 + 41#64) (c1 + (if (c0 + 41#64).ult c0 = true then 1#64 else 0#64)) (fz + 18446744073709551615#64) ((ln ||| fz) + 18446744073709551615#64)) t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hRF, hF⟩ := Region.exists_junk (sp - 0x250#64) 74 s
  exact compress1_41_spec s ra sp blk wp c0 c1 ln fz h0 h1 h2 h3 h4 h5 h6 h7 i0 i1 i2 i3 i4 i5 F hF hpc hcode hcodeS hcodeC hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hRF hRB hokB hRH hokH hd1 hd2 hd3 hk

set_option machineChecked.sym.foldBytes true in
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 1000000 in
theorem rcm_v3_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out rs rho gd pkd v psi : Word)
    (e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 : Word)
    (G0 G1 G2 G3 K0 K1 K2 K3 R0 R1 R2 R3 Q0 Q1 Q2 Q3 : Word)
    (hG : natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).2 * Fp.rInv % Fp.p % 2)) = [G0, G1, G2, G3])
    (hK : natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).2 * Fp.rInv % Fp.p % 2)) = [K0, K1, K2, K3])
    (hR : natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) = [R0, R1, R2, R3])
    (hQ : natToLeLimbs 4 (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) = [Q0, Q1, Q2, Q3])
    (hpc : s.pc = 0x7801d92c#64) (hcP : CodeAt F_7801d92c.base F_7801d92c.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcB : CodeAt F_78025654.base F_78025654.prog s) (hcB2 : CodeAt F_78025164.base F_78025164.prog s)
    (hcB3 : CodeAt F_78028d04.base F_78028d04.prog s) (hcB4 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcB5 : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcR : CodeAt F_78029468.base F_78029468.prog s)
    (hcX : CodeAt F_7802f038.base F_7802f038.prog s) (hcX2 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x510 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = rs) (ha2 : s.getReg .x12 = rho)
    (ha3 : s.getReg .x13 = gd) (ha4 : s.getReg .x14 = pkd) (ha5 : s.getReg .x15 = v)
    (ha6 : s.getReg .x16 = psi)
    (hRS : Region rs [e0, e1, e2, e3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi rs 4)
    (hRR : Region rho [r0, r1, r2, r3] s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hRQ : Region psi [q0, q1, q2, q3] s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi psi 4)
    (hRGd : Region gd [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] s) (hokGd : RegionOk Ro.layout.roBase Ro.layout.textHi gd 12)
    (hRK : Region pkd [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi pkd 12)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x510#64) 162 rs 4) (hd2 : Disjoint (sp - 0x510#64) 162 rho 4)
    (hd3 : Disjoint (sp - 0x510#64) 162 psi 4) (hd4 : Disjoint (sp - 0x510#64) 162 gd 12)
    (hd5 : Disjoint (sp - 0x510#64) 162 pkd 12) (hd6 : Disjoint (sp - 0x510#64) 162 out 4)
    (he1 : Disjoint out 4 rs 4) (he2 : Disjoint out 4 rho 4) (he3 : Disjoint out 4 psi 4)
    (he4 : Disjoint out 4 gd 12) (he5 : Disjoint out 4 pkd 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x510#64, 162), (out, 4)] s t →
      ∀ x : Nat, Region out (natToLeLimbs 4 x) t → x = (Fq.add (Fq.mul (leLimbsToNat [(compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[0]!, (compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[1]!, (compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[2]!, (compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[3]!]) Fq.R2) (Fq.mul (leLimbsToNat [(compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[4]!, (compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[5]!, (compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[6]!, (compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[7]!]) Fq.R3)) → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x510#64) 162 := hstk.frame 162 (by decide)
  have hokF0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x220#64) 68 := hokW.sub' 94 68 (by decide) (by bv_omega)
  -- the frame, and below it one region holding every callee's frame
  obtain ⟨F0, hRF0, _⟩ := Region.exists_junk (sp - 0x220#64) 68 s
  obtain ⟨G, hRG, _⟩ := Region.exists_junk (sp - 0x510#64) 94 s
  have hokG : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x510#64) 94 := hokW.sub' 0 94 (by decide) (by bv_omega)
  have hstkC : StackOk Ro.layout 0x2f0 (sp - 0x220#64) := by
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
  have hSep : Region 0x78001628#64 [0x6f646965736f700b#64] s :=
    (hro.get 11 (by decide)).sub 5 1 (by decide) rfl
  have hokSep : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001628#64 1 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 5 1 (by decide) (by decide)
  have hu := Unchanged.refl [(sp - 0x510#64, 162), (out, 4)] s
  sym_exec [memset144_spec, memset128_spec, memcpy16_spec, memcpy32_spec, memcpy1_spec, memcpy0_spec,
    memcpy32_off1_spec, memcpy8_off1_spec, memcpy23_off1_spec, memcpy9_src7_spec, memcpy41_spec, memcpy64_spec,
    compress1_128_spec', compress1_41_spec', ep_to_bytes_spec, fp_to_repr_spec, fq_from_uniform_bytes_spec]
  sym_close hk
  have w0 : v1021 = v707 := by
    rw [← v1021_def, ← v1020_def, ← v1019_def, ← v1018_def, ← v1017_def, ← v1016_def, ← v1015_def, ← v1014_def, ← v1013_def, ← v1012_def, ← v1011_def, ← v1010_def, ← v1009_def, ← v1008_def, ← v1007_def, ← v1006_def, ← v1005_def, ← v1004_def, ← v1003_def, ← v1002_def, ← v1001_def, ← v1000_def, ← v726_def, ← v725_def, ← v724_def, ← v719_def, ← v718_def, ← v717_def, ← v716_def]; exact pack_shift _
  have w1 : v999 = v708 := by
    rw [← v999_def, ← v998_def, ← v997_def, ← v996_def, ← v995_def, ← v994_def, ← v993_def, ← v992_def, ← v991_def, ← v990_def, ← v989_def, ← v988_def, ← v987_def, ← v986_def, ← v985_def, ← v984_def, ← v983_def, ← v982_def, ← v981_def, ← v980_def, ← v979_def, ← v978_def, ← v741_def, ← v740_def, ← v739_def, ← v734_def, ← v733_def, ← v732_def, ← v731_def]; exact pack_shift _
  have w2 : v977 = v709 := by
    rw [← v977_def, ← v976_def, ← v975_def, ← v974_def, ← v973_def, ← v972_def, ← v971_def, ← v970_def, ← v969_def, ← v968_def, ← v967_def, ← v966_def, ← v965_def, ← v964_def, ← v963_def, ← v962_def, ← v961_def, ← v960_def, ← v959_def, ← v958_def, ← v957_def, ← v956_def, ← v756_def, ← v755_def, ← v754_def, ← v749_def, ← v748_def, ← v747_def, ← v746_def]; exact pack_shift _
  have w3 : v955 = v710 := by
    rw [← v955_def, ← v954_def, ← v953_def, ← v952_def, ← v951_def, ← v950_def, ← v949_def, ← v948_def, ← v947_def, ← v946_def, ← v945_def, ← v944_def, ← v943_def, ← v942_def, ← v941_def, ← v940_def, ← v939_def, ← v938_def, ← v937_def, ← v936_def, ← v935_def, ← v934_def, ← v771_def, ← v770_def, ← v769_def, ← v764_def, ← v763_def, ← v762_def, ← v761_def]; exact pack_shift _
  have w4 : v929 = v711 := by
    rw [← v929_def, ← v928_def, ← v927_def, ← v926_def, ← v925_def, ← v924_def, ← v923_def, ← v922_def, ← v921_def, ← v920_def, ← v919_def, ← v918_def, ← v917_def, ← v916_def, ← v915_def, ← v914_def, ← v913_def, ← v912_def, ← v911_def, ← v910_def, ← v909_def, ← v908_def, ← v786_def, ← v785_def, ← v784_def, ← v779_def, ← v778_def, ← v777_def, ← v776_def]; exact pack_shift _
  have w5 : v907 = v712 := by
    rw [← v907_def, ← v906_def, ← v905_def, ← v904_def, ← v903_def, ← v902_def, ← v901_def, ← v900_def, ← v899_def, ← v898_def, ← v897_def, ← v896_def, ← v895_def, ← v894_def, ← v893_def, ← v892_def, ← v891_def, ← v890_def, ← v889_def, ← v888_def, ← v887_def, ← v886_def, ← v801_def, ← v800_def, ← v799_def, ← v794_def, ← v793_def, ← v792_def, ← v791_def]; exact pack_shift _
  have w6 : v885 = v713 := by
    rw [← v885_def, ← v884_def, ← v883_def, ← v882_def, ← v881_def, ← v880_def, ← v879_def, ← v878_def, ← v877_def, ← v876_def, ← v875_def, ← v874_def, ← v873_def, ← v872_def, ← v871_def, ← v870_def, ← v869_def, ← v868_def, ← v867_def, ← v866_def, ← v865_def, ← v864_def, ← v816_def, ← v815_def, ← v814_def, ← v809_def, ← v808_def, ← v807_def, ← v806_def]; exact pack_shift _
  have w7 : v863 = v714 := by
    rw [← v863_def, ← v862_def, ← v861_def, ← v860_def, ← v859_def, ← v858_def, ← v857_def, ← v856_def, ← v855_def, ← v854_def, ← v853_def, ← v852_def, ← v851_def, ← v850_def, ← v849_def, ← v848_def, ← v847_def, ← v846_def, ← v845_def, ← v844_def, ← v843_def, ← v842_def, ← v831_def, ← v830_def, ← v829_def, ← v824_def, ← v823_def, ← v822_def, ← v821_def]; exact pack_shift _
  have e91 : v91 = 0x510E527FADE682D1#64 := by
    rw [← v91_def, ← v87_def, ← acc24_0_def]; decide
  have e98 : v98 = 0x9B05688C2B3E6C1F#64 := by
    rw [← v98_def, ← v88_def, ← acc24_0_def]; decide
  obtain ⟨hG0, hG1, hG2, hG3⟩ : BitVec.ofNat 64 acc270_0 = G0 ∧ BitVec.ofNat 64 (acc270_0 >>> 64) = G1 ∧
      BitVec.ofNat 64 (acc270_0 >>> 128) = G2 ∧ BitVec.ofNat 64 (acc270_0 >>> 192) = G3 := by
    rw [acc270_0_def, natToLeLimbs_four] at hG
    simpa only [List.cons.injEq, and_true] using hG
  obtain ⟨hK0, hK1, hK2, hK3⟩ : BitVec.ofNat 64 acc347_0 = K0 ∧ BitVec.ofNat 64 (acc347_0 >>> 64) = K1 ∧
      BitVec.ofNat 64 (acc347_0 >>> 128) = K2 ∧ BitVec.ofNat 64 (acc347_0 >>> 192) = K3 := by
    rw [acc347_0_def, natToLeLimbs_four] at hK
    simpa only [List.cons.injEq, and_true] using hK
  obtain ⟨hR0, hR1, hR2, hR3⟩ : BitVec.ofNat 64 acc497_0 = R0 ∧ BitVec.ofNat 64 (acc497_0 >>> 64) = R1 ∧
      BitVec.ofNat 64 (acc497_0 >>> 128) = R2 ∧ BitVec.ofNat 64 (acc497_0 >>> 192) = R3 := by
    rw [acc497_0_def, natToLeLimbs_four] at hR
    simpa only [List.cons.injEq, and_true] using hR
  obtain ⟨hQ0, hQ1, hQ2, hQ3⟩ : BitVec.ofNat 64 acc595_0 = Q0 ∧ BitVec.ofNat 64 (acc595_0 >>> 64) = Q1 ∧
      BitVec.ofNat 64 (acc595_0 >>> 128) = Q2 ∧ BitVec.ofNat 64 (acc595_0 >>> 192) = Q3 := by
    rw [acc595_0_def, natToLeLimbs_four] at hQ
    simpa only [List.cons.injEq, and_true] using hQ
  have esep : BitVec.zeroExtend 64 (extractByte 8026656320330362891#64 0) = 11#64 := by decide
  have eH : [7640891576939301192#64, 13503953896175478587#64, 4354685564936845355#64, 11912009170470909681#64,
      0x510E527FADE682D1#64, 0x9B05688C2B3E6C1F#64, 7477812405655887409#64, 4577249634070577161#64] = prfH := by
    decide
  have hv1 : [v686, v687, v688, v689, v678, v679, v680, v681] = compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64 := by
    rw [← v686_def, ← v687_def, ← v688_def, ← v689_def, ← v678_def, ← v679_def, ← v680_def, ← v681_def]
    simp only [Nat.shiftRight_zero, hG0, hG1, hG2, hG3, hK0, hK1, hK2, hK3, hR0, hR1, hR2, and_ff_of_up1,
      replaceByte0_and_ff, esep, e91, e98, eH]
    rfl
  have hv2 : [v707, v708, v709, v710, v711, v712, v713, v714] = compress (compress prfH [e0, e1, e2, e3, (G0 <<< 8) ||| 11#64, (G1 <<< 8) ||| (G0 >>> 56), (G2 <<< 8) ||| (G1 >>> 56), (G3 <<< 8) ||| (G2 >>> 56), (K0 <<< 8) ||| (G3 >>> 56), (K1 <<< 8) ||| (K0 >>> 56), (K2 <<< 8) ||| (K1 >>> 56), (K3 <<< 8) ||| (K2 >>> 56), (v <<< 8) ||| (K3 >>> 56), (R0 <<< 8) ||| (v >>> 56), (R1 <<< 8) ||| (R0 >>> 56), (R2 <<< 8) ||| (R1 >>> 56)] 128#64 0#64 0#64 0#64) [(R3 <<< 8) ||| (R2 >>> 56), (Q0 <<< 8) ||| (R3 >>> 56), (Q1 <<< 8) ||| (Q0 >>> 56), (Q2 <<< 8) ||| (Q1 >>> 56), (Q3 <<< 8) ||| (Q2 >>> 56), Q3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]
      169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64 := by
    rw [← v707_def, ← v708_def, ← v709_def, ← v710_def, ← v711_def, ← v712_def, ← v713_def, ← v714_def, hv1]
    simp only [Nat.shiftRight_zero, hR2, hR3, hQ0, hQ1, hQ2, hQ3, hG0, hG1, and_ff_of_up1, zext_extract_up1_last]
    rfl
  rw [← acc1030_0_def, w0, w1, w2, w3, w4, w5, w6, w7, hv2]

/-- `rseed.rcm_v3(rho, g_d, pk_d, v, psi)` against the specification: for `rho`, `psi` stored as the
    Montgomery forms of `ρ`, `ψ` and points whose `to_bytes` are `repr_ℙ(g_d)`, `repr_ℙ(pk_d)`, the result
    is the Montgomery form of `Zip2005.hRcmOrchard rseed g_d pk_d v ρ ψ`. -/
theorem rcm_v3_correct {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out rs rho gd pkd v psi : Word)
    (e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 : Word)
    (hpc : s.pc = 0x7801d92c#64) (hcP : CodeAt F_7801d92c.base F_7801d92c.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcB : CodeAt F_78025654.base F_78025654.prog s) (hcB2 : CodeAt F_78025164.base F_78025164.prog s)
    (hcB3 : CodeAt F_78028d04.base F_78028d04.prog s) (hcB4 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcB5 : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcR : CodeAt F_78029468.base F_78029468.prog s)
    (hcX : CodeAt F_7802f038.base F_7802f038.prog s) (hcX2 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x510 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = rs) (ha2 : s.getReg .x12 = rho)
    (ha3 : s.getReg .x13 = gd) (ha4 : s.getReg .x14 = pkd) (ha5 : s.getReg .x15 = v)
    (ha6 : s.getReg .x16 = psi)
    (hRS : Region rs [e0, e1, e2, e3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi rs 4)
    (hRR : Region rho [r0, r1, r2, r3] s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hRQ : Region psi [q0, q1, q2, q3] s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi psi 4)
    (hRGd : Region gd [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] s) (hokGd : RegionOk Ro.layout.roBase Ro.layout.textHi gd 12)
    (hRK : Region pkd [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi pkd 12)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x510#64) 162 rs 4) (hd2 : Disjoint (sp - 0x510#64) 162 rho 4)
    (hd3 : Disjoint (sp - 0x510#64) 162 psi 4) (hd4 : Disjoint (sp - 0x510#64) 162 gd 12)
    (hd5 : Disjoint (sp - 0x510#64) 162 pkd 12) (hd6 : Disjoint (sp - 0x510#64) 162 out 4)
    (he1 : Disjoint out 4 rs 4) (he2 : Disjoint out 4 rho 4) (he3 : Disjoint out 4 psi 4)
    (he4 : Disjoint out 4 gd 12) (he5 : Disjoint out 4 pkd 12)
    (gdP pkdP : Zcash.Circuits.Point Zcash.Circuits.Fp) (ρ ψ : Zcash.Circuits.Fp)
    (hgd : Zip2005.Blake2b.stateBytes ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).2 * Fp.rInv % Fp.p % 2))).map BitVec.toNat) = Zip2005.reprP gdP)
    (hpkd : Zip2005.Blake2b.stateBytes ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).2 * Fp.rInv % Fp.p % 2))).map BitVec.toNat) = Zip2005.reprP pkdP)
    (hr : leLimbsToNat [r0, r1, r2, r3] = ρ.val * Fp.R % Fp.p)
    (hq : leLimbsToNat [q0, q1, q2, q3] = ψ.val * Fp.R % Fp.p)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x510#64, 162), (out, 4)] s t → ∀ x : Nat, Region out (natToLeLimbs 4 x) t →
      x = (Zip2005.hRcmOrchard (Zip2005.Blake2b.stateBytes ([e0, e1, e2, e3].map BitVec.toNat)) gdP pkdP v.toNat ρ ψ).val *
        Fq.R % Fq.q → SafeN G n P t) :
    SafeN G n P s := by
  refine rcm_v3_spec s ra sp out rs rho gd pkd v psi e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).2 * Fp.rInv % Fp.p % 2))))[0]! ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).2 * Fp.rInv % Fp.p % 2))))[1]! ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).2 * Fp.rInv % Fp.p % 2))))[2]! ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) (leLimbsToNat [g8, g9, g10, g11])).2 * Fp.rInv % Fp.p % 2))))[3]! ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).2 * Fp.rInv % Fp.p % 2))))[0]! ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).2 * Fp.rInv % Fp.p % 2))))[1]! ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).2 * Fp.rInv % Fp.p % 2))))[2]! ((natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).1 * Fp.rInv % Fp.p + 2 ^ 255 * ((Fp.toAffine (leLimbsToNat [k0, k1, k2, k3]) (leLimbsToNat [k4, k5, k6, k7]) (leLimbsToNat [k8, k9, k10, k11])).2 * Fp.rInv % Fp.p % 2))))[3]! ((natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p)))[0]! ((natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p)))[1]! ((natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p)))[2]! ((natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p)))[3]! ((natToLeLimbs 4 (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p)))[0]! ((natToLeLimbs 4 (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p)))[1]! ((natToLeLimbs 4 (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p)))[2]! ((natToLeLimbs 4 (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p)))[3]! rfl rfl rfl rfl hpc hcP hcT hcU hcF hcL hcM hcC hcB hcB2 hcB3 hcB4 hcB5 hcR hcX hcX2 hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 ha4 ha5 ha6 hRS hokS hRR hokR hRQ hokQ hRGd hokGd hRK hokK hokO hd1 hd2 hd3 hd4 hd5 hd6 he1 he2 he3 he4 he5 (fun t a b c d x hR hx => hk t a b c d x hR ?_)
  have hpl : ρ.val < Fp.p := ZMod.val_lt ρ
  have hql : ψ.val < Fp.p := ZMod.val_lt ψ
  have eρ : leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p = ρ.val := by
    rw [hr, Fp.mont_back, Nat.mod_eq_of_lt hpl]
  have eψ : leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p = ψ.val := by
    rw [hq, Fp.mont_back, Nat.mod_eq_of_lt hql]
  have eL : ∀ w, (natToLeLimbs 4 w).map BitVec.toNat =
      [(natToLeLimbs 4 w)[0]!.toNat, (natToLeLimbs 4 w)[1]!.toNat, (natToLeLimbs 4 w)[2]!.toNat,
        (natToLeLimbs 4 w)[3]!.toNat] := fun _ => rfl
  have e11 : (11#64 : Word) = BitVec.zeroExtend 64 (BitVec.truncate 8 11#64) := by decide
  rw [hx, Fq.from_uniform_eq, leLimbsToNat_halves _ (compress_length _ _ _ _ _ _), e11, ← leos2ip_stateBytes,
    B2b.prfExpand169_eq]
  unfold Zip2005.hRcmOrchard Zip2005.preRcm Zip2005.rhoBytes
  rw [toScalarOrchard_val, Nat.mod_mul_mod, ← hgd, ← hpkd, i2leosp64_word, i2leosp256_limbs _ (by have := Fp.p_lt; omega),
    i2leosp256_limbs ψ.val (by have := Fp.p_lt; omega), ← eρ, ← eψ, eL, eL, eL, eL,
    show Zip2005.Sep.rcmOrchard = UInt8.ofNat (11#64).toNat from rfl]
  simp only [Zip2005.Blake2b.stateBytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_assoc, List.append_nil, List.cons_append, List.nil_append]

end Cases.Zip2005
