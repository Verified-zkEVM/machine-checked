/-
  Cases.Zip2005.FpSubNeg

  `Fp::sub` as `Ep::double` schedules two of its five subtractions: the borrow of limbs 0
  and 1 is accumulated negated (`-c0`, `-c0 - c1`, then `+ c2`), and the limb sums of the
  borrow chain are commuted with their carries taken against the difference rather than the
  mask. Everything else is `fsub_chain`'s; this lemma is that one, with the glue.
-/

import Cases.Zip2005.Field.FpSub
import Cases.Zip2005.Field.FpDbl

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

/-- `Fp::sub` on canonical operands, neg-first borrow schedule. -/
theorem fsubneg_chain {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    {f0 c0 n0 c1 f1 d1 c2 n1 bm1 m2 f2 c3 t2 d2 c2' bm2 m3 f3 c4 t3 d3 c3' M
      m0 r0 k0 m1 e1 k1 r1 k1' k r2 k2 mm3 e3 r3 : Word}
    (hf0 : a0 + -b0 = f0) (hc0 : (if a0.ult b0 = true then 1#64 else 0#64) = c0)
    (hn0 : -c0 = n0)
    (hc1 : (if a1.ult b1 = true then 1#64 else 0#64) = c1) (hf1 : a1 + -b1 = f1)
    (hd1 : f1 + -c0 = d1) (hc2 : (if d1.ult f1 = true then 1#64 else 0#64) = c2)
    (hn1 : n0 + -c1 = n1) (hbm1 : n1 + c2 = bm1)
    (hm2 : bm1.sshiftRight 63 = m2)
    (hf2 : a2 + -b2 = f2) (hc3 : (if a2.ult b2 = true then 1#64 else 0#64) = c3)
    (ht2 : m2 + -c3 = t2) (hd2 : f2 + m2 = d2)
    (hc2' : (if d2.ult f2 = true then 1#64 else 0#64) = c2') (hbm2 : t2 + c2' = bm2)
    (hm3 : bm2.sshiftRight 63 = m3)
    (hf3 : a3 + -b3 = f3) (hc4 : (if a3.ult b3 = true then 1#64 else 0#64) = c4)
    (ht3 : m3 + -c4 = t3) (hd3 : f3 + m3 = d3)
    (hc3' : (if d3.ult f3 = true then 1#64 else 0#64) = c3') (hM : t3 + c3' = M)
    (hm0 : M &&& 11037532056220336129#64 = m0) (hr0 : m0 + f0 = r0)
    (hk0 : (if r0.ult m0 = true then 1#64 else 0#64) = k0)
    (hm1 : M &&& 2469829653914515739#64 = m1) (he1 : m1 + d1 = e1)
    (hk1 : (if e1.ult m1 = true then 1#64 else 0#64) = k1) (hr1 : e1 + k0 = r1)
    (hk1' : (if r1.ult e1 = true then 1#64 else 0#64) = k1') (hk : k1 + k1' = k)
    (hr2 : k + d2 = r2) (hk2 : (if r2.ult k = true then 1#64 else 0#64) = k2)
    (hmm3 : M &&& 4611686018427387904#64 = mm3) (he3 : mm3 + d3 = e3) (hr3 : e3 + k2 = r3)
    (hA : leLimbsToNat [a0, a1, a2, a3] < Fp.p) (hB : leLimbsToNat [b0, b1, b2, b3] < Fp.p) :
    leLimbsToNat [r0, r1, r2, r3] =
      Fp.sub (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3]) := by
  have hbm1' : c2 + -(c0 + c1) = bm1 := by
    rw [← hbm1, ← hn1, ← hn0, BitVec.neg_add, BitVec.sub_eq_add_neg]; ac_rfl
  exact fsub_chain hf0 hc0 hf1 hc1 rfl hd1 hc2 hbm1' hm2 hc3 hf2 (by rw [← hd2]; ac_rfl)
    (Bn.carry_either hd2 hc2') ht2 hbm2 hm3 hc4 hf3 (by rw [← hd3]; ac_rfl)
    (Bn.carry_either hd3 hc3') ht3 hM hm0 hr0 hk0 hm1 he1 hk1 hr1 hk1' hk hr2 hk2 hmm3 he3 hr3
    hA hB

end Cases.Zip2005
