import Cases.Zip2005.Blake2b.PrfExpandApply
import Cases.Zip2005.Blake2b.SpecBridge
import Cases.Zip2005.Spec.Zip2005.KeyComponents
import Cases.Zip2005.Field.FqRepr
import Cases.Zip2005.Field.FpIntoBytes
import Cases.Zip2005.Field.FqFromUniform
import Cases.Zip2005.Image.F_78022ca0
import Cases.Zip2005.Image.Ro

/-!
# `orchard::keys::FullViewingKey::rivk`

`fvk.rivk(scope)`: `External` copies the stored `rivk` (a Montgomery `Fq`); `Internal` computes
`rivk_internal = ToScalar(PRF^expand_{rivk.to_repr()}([0x83] ‖ ak ‖ nk.to_repr()))`
(`Fq::from_uniform_bytes` of the 64 output bytes), after `SpendValidatingKey::to_bytes`'s assertion
that the sign bit of `ak`'s last byte is clear (a panic otherwise). The key's layout from `0x60`:
the 32 `ak` bytes, `nk`, `rivk`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

/-- `prf_expand_apply2_spec` with its stack frame taken as whatever the memory holds. -/
theorem prf_expand_apply2_spec' {P : Prop} (s : MachineState) (ra sp out d sk ts pa pb s0 s1 s2 s3 a0 a1 a2 a3
    b0 b1 b2 b3 : Word)
    (O : List Word) (hO : O.length = 8)
    (hpc : s.pc = 0x7801d3d4#64) (hcW : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x490 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = d) (ha2 : s.getReg .x12 = sk)
    (ha3 : s.getReg .x13 = 32#64) (ha4 : s.getReg .x14 = ts) (ha5 : s.getReg .x15 = 2#64)
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
      Region out (compress prfH [s0, s1, s2, s3, (a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (a1 <<< 8) ||| (a0 >>> 56), (a2 <<< 8) ||| (a1 >>> 56), (a3 <<< 8) ||| (a2 >>> 56), (b0 <<< 8) ||| (a3 >>> 56), (b1 <<< 8) ||| (b0 >>> 56), (b2 <<< 8) ||| (b1 >>> 56), (b3 <<< 8) ||| (b2 >>> 56), b3 >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64) t → Safe P t) :
    Safe P s := by
  obtain ⟨F1, hRF1, hF1⟩ := Region.exists_junk (sp - 0x490#64) 74 s
  obtain ⟨F2, hRF2, hF2⟩ := Region.exists_junk (sp - 0x240#64) 72 s
  exact prf_expand_apply2_spec s ra sp out d sk ts pa pb s0 s1 s2 s3 a0 a1 a2 a3 b0 b1 b2 b3 F1 F2 O hF1 hF2 hO hpc hcW hcT hcU hcF hcL hcM hcC hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 ha4 ha5 hRF1 hRF2 hRS hokS hRT hokT hRA hokA hRB hokB hRO hokO hd1 hd2 hd3 hd4 hd5 he1 he2 he3 he4 hk

set_option asmverif.sym.foldBytes true in
set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
/-- `fvk.rivk(Scope::Internal)`. -/
theorem rivk_internal_spec {P : Prop} (s : MachineState) (ra sp out fvk SC k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3 : Word)
    (Fr : List Word) (hFr : Fr.length = 28) (hRF : Region (sp - 0xe0#64) Fr s)
    (hpc : s.pc = 0x78022ca0#64) (hcR : CodeAt F_78022ca0.base F_78022ca0.prog s)
    (hcQ : CodeAt F_7802e9b8.base F_7802e9b8.prog s) (hcI : CodeAt F_78028ce8.base F_78028ce8.prog s)
    (hcI2 : CodeAt F_78029468.base F_78029468.prog s)
    (hcW : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcX : CodeAt F_7802f038.base F_7802f038.prog s) (hcX2 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcX3 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x570 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = fvk) (ha2 : s.getReg .x12 = SC)
    (hK : Region (fvk + 0x60#64) [k0, k1, k2, k3, n0, n1, n2, n3, r0, r1, r2, r3] s)
    (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (fvk + 0x60#64) 12)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x570#64) 174 (fvk + 0x60#64) 12) (hd2 : Disjoint (sp - 0x570#64) 174 out 4)
    (hd3 : Disjoint out 4 (fvk + 0x60#64) 12)
    (hSC : SC = 1#64)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → Safe P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x570#64, 174), (out, 4)] s t →
      Region out (natToLeLimbs 4 (Fq.add (Fq.mul (leLimbsToNat [(compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[0]!, (compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[1]!, (compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[2]!, (compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[3]!]) Fq.R2) (Fq.mul (leLimbsToNat [(compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[4]!, (compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[5]!, (compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[6]!, (compress prfH [(natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[0]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[1]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[2]!, (natToLeLimbs 4 (leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q))[3]!, (k0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 0x83#64), (k1 <<< 8) ||| (k0 >>> 56), (k2 <<< 8) ||| (k1 >>> 56), (k3 <<< 8) ||| (k2 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| (k3 >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[7]!]) Fq.R3))) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x570#64) 174 := hstk.frame 174 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe0#64) 28 := hokW.sub' 146 28 (by decide) (by bv_omega)
  have hstkA : StackOk Ro.layout 0x490 (sp - 0xe0#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0xe0#64).toNat = sp.toNat - 0xe0 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  have hlo := hstk.lo
  have hokO' := hokO.toText
  subst hSC
  have hu := Unchanged.refl [(sp - 0x570#64, 174), (out, 4)] s
  sym_exec [fq_to_repr_spec, fp_into_bytes_spec, prf_expand_apply2_spec', fq_from_uniform_bytes_spec, hpp]
  sym_close hk
  have ek0 : v101 = k0 := by
    rw [← v101_def, ← v99_def, ← v98_def, ← v97_def, ← v96_def, ← v95_def, ← v94_def, ← v93_def, ← v92_def, ← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def]; exact pack_word k0
  have ek1 : v78 = k1 := by
    rw [← v78_def, ← v77_def, ← v76_def, ← v75_def, ← v74_def, ← v73_def, ← v72_def, ← v71_def, ← v70_def, ← v69_def, ← v68_def, ← v67_def, ← v66_def, ← v65_def, ← v64_def, ← v63_def, ← v62_def, ← v61_def, ← v60_def, ← v59_def, ← v58_def, ← v57_def]; exact pack_word k1
  have ek2 : v56 = k2 := by
    rw [← v56_def, ← v55_def, ← v54_def, ← v53_def, ← v52_def, ← v51_def, ← v50_def, ← v49_def, ← v48_def, ← v47_def, ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def]; exact pack_word k2
  have ek3 : v33 = k3 := by
    rw [← v33_def, ← v32_def, ← v31_def, ← v30_def, ← v29_def, ← v28_def, ← v27_def, ← v26_def, ← v25_def, ← v24_def, ← v23_def, ← v22_def, ← v21_def, ← v20_def, ← v19_def, ← v18_def, ← v17_def, ← v16_def, ← v15_def, ← v14_def, ← v13_def, ← v12_def]; exact pack_word k3
  rw [← acc139_0_def, ← acc134_0_def, ek0, ek1, ek2, ek3, ← acc11_0_def, ← acc119_0_def]
  rfl

set_option maxHeartbeats 40000000 in
/-- `fvk.rivk(Scope::External)`: the stored `rivk`. -/
theorem rivk_external_spec {P : Prop} (s : MachineState) (ra sp out fvk SC r0 r1 r2 r3 : Word)
    (Fr : List Word) (hFr : Fr.length = 28) (hRF : Region (sp - 0xe0#64) Fr s)
    (hpc : s.pc = 0x78022ca0#64) (hcR : CodeAt F_78022ca0.base F_78022ca0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xe0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = fvk) (ha2 : s.getReg .x12 = SC)
    (hK : Region (fvk + 0xa0#64) [r0, r1, r2, r3] s)
    (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (fvk + 0xa0#64) 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0xe0#64) 28 (fvk + 0xa0#64) 4) (hd2 : Disjoint (sp - 0xe0#64) 28 out 4)
    (hd3 : Disjoint out 4 (fvk + 0xa0#64) 4)
    (hSC : SC = 0#64)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xe0#64, 28), (out, 4)] s t →
      Region out [r0, r1, r2, r3] t → Safe P t) :
    Safe P s := by
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe0#64) 28 := hstk.frame 28 (by decide)
  have hlo := hstk.lo
  have hokO' := hokO.toText
  subst hSC
  have hu := Unchanged.refl [(sp - 0xe0#64, 28), (out, 4)] s
  obtain ⟨O, hRO, hOl⟩ := Region.exists_junk out 4 s
  sym_exec
  sym_close hk

/-- `fvk.rivk(Scope::Internal)` against the specification: for a key whose stored `rivk` and `nk`
    are the Montgomery forms of `rivk_ext` and `nk` and whose `ak` bytes are `I2LEOSP₂₅₆(ak)`, the
    result is the Montgomery form of `H^rivk_int(I2LEOSP₂₅₆(rivk_ext), ak, nk)` (or a panic, if
    `ak`'s last byte has its top bit set). -/
theorem rivk_internal_correct {P : Prop} (s : MachineState) (ra sp out fvk SC k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3 : Word)
    (Fr : List Word) (hFr : Fr.length = 28) (hRF : Region (sp - 0xe0#64) Fr s)
    (hpc : s.pc = 0x78022ca0#64) (hcR : CodeAt F_78022ca0.base F_78022ca0.prog s)
    (hcQ : CodeAt F_7802e9b8.base F_7802e9b8.prog s) (hcI : CodeAt F_78028ce8.base F_78028ce8.prog s)
    (hcI2 : CodeAt F_78029468.base F_78029468.prog s)
    (hcW : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcX : CodeAt F_7802f038.base F_7802f038.prog s) (hcX2 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcX3 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x570 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = fvk) (ha2 : s.getReg .x12 = SC)
    (hK : Region (fvk + 0x60#64) [k0, k1, k2, k3, n0, n1, n2, n3, r0, r1, r2, r3] s)
    (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (fvk + 0x60#64) 12)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x570#64) 174 (fvk + 0x60#64) 12) (hd2 : Disjoint (sp - 0x570#64) 174 out 4)
    (hd3 : Disjoint out 4 (fvk + 0x60#64) 12)
    (hSC : SC = 1#64)
    (rivkE : Zcash.Circuits.Fq) (ak nk : Zcash.Circuits.Fp)
    (hr : leLimbsToNat [r0, r1, r2, r3] = rivkE.val * Fq.R % Fq.q)
    (hn : leLimbsToNat [n0, n1, n2, n3] = nk.val * Fp.R % Fp.p)
    (hak : Zip2005.Blake2b.stateBytes ([k0, k1, k2, k3].map BitVec.toNat) = Zip2005.i2leosp 256 ak.val)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → Safe P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x570#64, 174), (out, 4)] s t → ∀ x : Nat, Region out (natToLeLimbs 4 x) t →
      x = (Zip2005.hRivkInt (Zip2005.i2leosp 256 rivkE.val) ak nk).val * Fq.R % Fq.q → Safe P t) :
    Safe P s := by
  refine rivk_internal_spec s ra sp out fvk SC k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3 Fr hFr hRF hpc hcR hcQ hcI hcI2 hcW hcT hcU hcF hcL hcM hcC hcX hcX2 hcX3 hcw hro hra hra1 hsp hstk ha0 ha1 ha2 hK hokK hokO hd1 hd2 hd3 hSC hpp (fun t a b c d hR => hk t a b c d _ hR ?_)
  have hq : rivkE.val < Fq.q := ZMod.val_lt rivkE
  have hp : nk.val < Fp.p := ZMod.val_lt nk
  have eK : leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q = rivkE.val := by
    rw [hr, Fq.mont_back, Nat.mod_eq_of_lt hq]
  have eN : leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p = nk.val := by
    rw [hn, Fp.mont_back, Nat.mod_eq_of_lt hp]
  have eL : ∀ v, (natToLeLimbs 4 v).map BitVec.toNat =
      [(natToLeLimbs 4 v)[0]!.toNat, (natToLeLimbs 4 v)[1]!.toNat, (natToLeLimbs 4 v)[2]!.toNat,
        (natToLeLimbs 4 v)[3]!.toNat] := fun _ => rfl
  have hO := prfExpand97_eq (natToLeLimbs 4 rivkE.val)[0]! (natToLeLimbs 4 rivkE.val)[1]!
    (natToLeLimbs 4 rivkE.val)[2]! (natToLeLimbs 4 rivkE.val)[3]! k0 k1 k2 k3
    (natToLeLimbs 4 nk.val)[0]! (natToLeLimbs 4 nk.val)[1]! (natToLeLimbs 4 nk.val)[2]! (natToLeLimbs 4 nk.val)[3]!
    0x83#64
  simp only [List.map_cons, List.map_nil] at hO
  rw [eK, eN, Fq.from_uniform_eq, leLimbsToNat_halves _ (compress_length _ _ _ _ _ _)]
  unfold Zip2005.hRivkInt
  rw [toScalarOrchard_val, Nat.mod_mul_mod, i2leosp256_limbs _ (by have := Fq.q_lt; omega),
    i2leosp256_limbs nk.val (by have := Fp.p_lt; omega), ← hak, eL, eL,
    show Zip2005.Sep.rivkInt = UInt8.ofNat (0x83#64).toNat from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [← hO, leos2ip_stateBytes]

end Cases.Zip2005
