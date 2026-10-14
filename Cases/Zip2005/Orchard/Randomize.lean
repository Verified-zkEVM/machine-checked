import Cases.Zip2005.Curve.SpendAuthBasepoint
import Cases.Zip2005.Curve.EpMulFq
import Cases.Zip2005.Curve.EpAdd
import Cases.Zip2005.Curve.ToBytes
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Orchard.NullifierDerive
import Cases.Zip2005.Image.F_780227b4
import Cases.Zip2005.Image.Ro

/-!
# `SpendValidatingKey::randomize` (0x780227b4)

`rk = ak + [α] G_SpendAuth`: the point `ak` copied into the frame, the basepoint decoded from its
bytes (`spendauth_basepoint`), `Ep::mul`, `Ep::add`, then the sum and its `Ep::to_bytes` at the
output (`SpendValidatingKey` is the point followed by its encoding).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- The Jacobian sum `ak + m` for `ak` given by its twelve words and `m` as a list (`ptX` … so
that no `getElem!` on the computed point is exposed to the executor). -/
def rkJ (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Word) (m : List Word) : Nat × Nat × Nat :=
  Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [a4, a5, a6, a7])
    (leLimbsToNat [a8, a9, a10, a11]) (ptX m) (ptY m) (ptZ m)

/-- A Jacobian point as `Ep::add` leaves it: three Montgomery limb groups. -/
def jacW (J : Nat × Nat × Nat) : List Word :=
  natToLeLimbs 4 J.1 ++ natToLeLimbs 4 J.2.1 ++ natToLeLimbs 4 J.2.2

/-- `Ep::to_bytes` of a Jacobian point: the affine `x` out of Montgomery form, the parity of
`y` in the top bit. -/
def toBytesW (J : Nat × Nat × Nat) : List Word :=
  natToLeLimbs 4 ((Fp.toAffine J.1 J.2.1 J.2.2).1 * Fp.rInv % Fp.p +
    2 ^ 255 * ((Fp.toAffine J.1 J.2.1 J.2.2).2 * Fp.rInv % Fp.p % 2))

/-- `jacW` as the executor's cells. -/
theorem jacW_cells (J : Nat × Nat × Nat) : jacW J =
    [BitVec.ofNat 64 (J.1 >>> (64 * 0)), BitVec.ofNat 64 (J.1 >>> (64 * 1)), BitVec.ofNat 64 (J.1 >>> (64 * 2)), BitVec.ofNat 64 (J.1 >>> (64 * 3)), BitVec.ofNat 64 (J.2.1 >>> (64 * 0)), BitVec.ofNat 64 (J.2.1 >>> (64 * 1)), BitVec.ofNat 64 (J.2.1 >>> (64 * 2)), BitVec.ofNat 64 (J.2.1 >>> (64 * 3)), BitVec.ofNat 64 (J.2.2 >>> (64 * 0)), BitVec.ofNat 64 (J.2.2 >>> (64 * 1)), BitVec.ofNat 64 (J.2.2 >>> (64 * 2)), BitVec.ofNat 64 (J.2.2 >>> (64 * 3))] := rfl

/-- `Ep::to_bytes` applied to the cells of a Jacobian point is `toBytesW`. -/
theorem toBytesW_cells (J : Nat × Nat × Nat) (h1 : J.1 < 2 ^ 256) (h2 : J.2.1 < 2 ^ 256)
    (h3 : J.2.2 < 2 ^ 256) :
    natToLeLimbs 4 ((Fp.toAffine (leLimbsToNat [BitVec.ofNat 64 (J.1 >>> (64 * 0)), BitVec.ofNat 64 (J.1 >>> (64 * 1)), BitVec.ofNat 64 (J.1 >>> (64 * 2)), BitVec.ofNat 64 (J.1 >>> (64 * 3))]) (leLimbsToNat [BitVec.ofNat 64 (J.2.1 >>> (64 * 0)), BitVec.ofNat 64 (J.2.1 >>> (64 * 1)), BitVec.ofNat 64 (J.2.1 >>> (64 * 2)), BitVec.ofNat 64 (J.2.1 >>> (64 * 3))])
        (leLimbsToNat [BitVec.ofNat 64 (J.2.2 >>> (64 * 0)), BitVec.ofNat 64 (J.2.2 >>> (64 * 1)), BitVec.ofNat 64 (J.2.2 >>> (64 * 2)), BitVec.ofNat 64 (J.2.2 >>> (64 * 3))])).1 * Fp.rInv % Fp.p +
      2 ^ 255 * ((Fp.toAffine (leLimbsToNat [BitVec.ofNat 64 (J.1 >>> (64 * 0)), BitVec.ofNat 64 (J.1 >>> (64 * 1)), BitVec.ofNat 64 (J.1 >>> (64 * 2)), BitVec.ofNat 64 (J.1 >>> (64 * 3))]) (leLimbsToNat [BitVec.ofNat 64 (J.2.1 >>> (64 * 0)), BitVec.ofNat 64 (J.2.1 >>> (64 * 1)), BitVec.ofNat 64 (J.2.1 >>> (64 * 2)), BitVec.ofNat 64 (J.2.1 >>> (64 * 3))])
        (leLimbsToNat [BitVec.ofNat 64 (J.2.2 >>> (64 * 0)), BitVec.ofNat 64 (J.2.2 >>> (64 * 1)), BitVec.ofNat 64 (J.2.2 >>> (64 * 2)), BitVec.ofNat 64 (J.2.2 >>> (64 * 3))])).2 * Fp.rInv % Fp.p % 2)) = toBytesW J := by
  rw [AsmVerif.RiscV.Sym.cells4', AsmVerif.RiscV.Sym.cells4', AsmVerif.RiscV.Sym.cells4', leLimbsToNat_natToLeLimbs 4 _ h1,
    leLimbsToNat_natToLeLimbs 4 _ h2, leLimbsToNat_natToLeLimbs 4 _ h3]
  rfl

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem spend_validating_key_randomize_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out ak alpha : Word)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 k0 k1 k2 k3 : Word)
    (cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 16) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN Gd n P u)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN Gd n P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN Gd n P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → SafeN Gd n P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → SafeN Gd n P u)
    (hpc : s.pc = 0x780227b4#64) (hcode : CodeAt F_780227b4.base F_780227b4.prog s)
    (hcodeBP : CodeAt F_78023278.base F_78023278.prog s)
    (hcodeU : CodeAt F_78026928.base F_78026928.prog s)
    (hcodeF : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeAs : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeLn : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s)
    (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeDa : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcodeTB : CodeAt F_78025654.base F_78025654.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x960 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = ak) (ha2 : s.getReg .x12 = alpha)
    (hA : Region ak [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] s)
    (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi ak 12)
    (hakX : leLimbsToNat [a0, a1, a2, a3] < Fp.p) (hakZ : leLimbsToNat [a8, a9, a10, a11] < Fp.p)
    (hK : Region alpha [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi alpha 4)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 16)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x960#64) 300 out 16) (hdA : Disjoint (sp - 0x960#64) 300 ak 12)
    (hdK : Disjoint (sp - 0x960#64) 300 alpha 4)
    (hd_tb : Disjoint (sp - 0x960#64) 300 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x960#64) 300 iptr 138)
    (hd_g0 : Disjoint (sp - 0x960#64) 300 g0 1024) (hd_g1 : Disjoint (sp - 0x960#64) 300 g1 1024)
    (hd_g2 : Disjoint (sp - 0x960#64) 300 g2 1024) (hd_g3 : Disjoint (sp - 0x960#64) 300 g3 516)
    (heA : Disjoint out 16 ak 12) (heK : Disjoint out 16 alpha 4)
    (he_tb : Disjoint out 16 0x780488a8#64 10) (he_iptr : Disjoint out 16 iptr 138)
    (he_g0 : Disjoint out 16 g0 1024) (he_g1 : Disjoint out 16 g1 1024)
    (he_g2 : Disjoint out 16 g2 1024) (he_g3 : Disjoint out 16 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x960#64, 300), (out, 16)] s t →
      FromBytesPost 0x8d1a7284b875c963#64 0xc7f0ce37b70a10c#64 0x3b8d187c3e5f445f#64 0xb75523b328f1d606#64
        (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8 →
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) →
      mulFacts [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] [k0, k1, k2, k3] →
      Region out (jacW (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
          (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] [k0, k1, k2, k3])) ++
        toBytesW (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
          (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] [k0, k1, k2, k3]))) t →
      SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x960#64) 300 := hstk.frame 300 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64) 40 := hokW.sub' 260 40 (by decide) (by bv_omega)
  -- the frame: [8, 0x68) the copy of `ak`, [0x68, 0xc8) `[α] G`, [0xc8, 0x128) `G` then the sum,
  -- saved registers at 0x128..0x140
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0x138#64) 12 s
  obtain ⟨FM, hFM, hFMl⟩ := Region.exists_junk (sp - 0xd8#64) 12 s
  obtain ⟨FG, hFG, hFGl⟩ := Region.exists_junk (sp - 0x78#64) 12 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  have hokFA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x138#64) 12 := hokF.sub' 1 12 (by decide) (by bv_omega)
  have hokFM : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xd8#64) 12 := hokF.sub' 13 12 (by decide) (by bv_omega)
  have hokFG : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x78#64) 12 := hokF.sub' 25 12 (by decide) (by bv_omega)
  have hokFR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokF.sub' 37 3 (by decide) (by bv_omega)
  have hok0' := hok0.toText
  have hokO12 : RegionOk Ro.layout.textLo Ro.layout.textHi out 12 := hok0'.sub' 0 12 (by decide) (by bv_omega)
  have hokO4 : RegionOk Ro.layout.roBase Ro.layout.textHi (out + 0x60#64) 4 := hok0.sub' 12 4 (by decide) (by bv_omega)
  have hokA' := hokA.toText
  have hu := Unchanged.refl [(sp - 0x960#64, 300), (out, 16)] s
  have hlo := hstk.lo
  sym_exec [memcpy96_spec, spendauth_basepoint_spec, ep_mul_fq_spec, hpb, hpaf, hpp, hprz, hpanic]
    stop [0x780227fc]
  -- `[α] G`'s `Z` is canonical (`Ep::add` asserts it of its second operand)
  have hW : leLimbsToNat [acc20_0[8]!, acc20_0[9]!, acc20_0[10]!, acc20_0[11]!] < Fp.p :=
    acc20_0_def ▸ mulW_Z_lt _ _
  sym_reframe
  sym_exec [ep_add_spec, ep_to_bytes_spec, memcpy96_spec]
  -- the sum's coordinates fit four limbs
  have hJ : (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [post14_0, post14_1, post14_2, post14_3, post14_4, post14_5, post14_6, post14_7, post14_8, post14_9, post14_10, post14_11] [k0, k1, k2, k3])).1 < 2 ^ 256 ∧ (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [post14_0, post14_1, post14_2, post14_3, post14_4, post14_5, post14_6, post14_7, post14_8, post14_9, post14_10, post14_11] [k0, k1, k2, k3])).2.1 < 2 ^ 256 ∧ (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [post14_0, post14_1, post14_2, post14_3, post14_4, post14_5, post14_6, post14_7, post14_8, post14_9, post14_10, post14_11] [k0, k1, k2, k3])).2.2 < 2 ^ 256 := by
    rw [rkJ, acc20_0_def, ptX_eq, ptY_eq, ptZ_eq]
    exact Fp.addJ_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
      (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
  -- the sum at `out` and its encoding at `out + 0x60`: one block of sixteen cells
  have hb : natToLeLimbs 4 acc10_0 = toBytesW (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [post14_0, post14_1, post14_2, post14_3, post14_4, post14_5, post14_6, post14_7, post14_8, post14_9, post14_10, post14_11] [k0, k1, k2, k3])) := by
    rw [← acc10_0_def, ← toBytesW_cells _ hJ.1 hJ.2.1 hJ.2.2, rkJ, acc20_0_def, ptX_eq, ptY_eq, ptZ_eq]
  have hRo : Region out (jacW (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [post14_0, post14_1, post14_2, post14_3, post14_4, post14_5, post14_6, post14_7, post14_8, post14_9, post14_10, post14_11] [k0, k1, k2, k3])) ++ toBytesW (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [post14_0, post14_1, post14_2, post14_3, post14_4, post14_5, post14_6, post14_7, post14_8, post14_9, post14_10, post14_11] [k0, k1, k2, k3]))) s_22 := by
    rw [← hb, jacW_cells, rkJ, acc20_0_def, ptX_eq, ptY_eq, ptZ_eq, ← AsmVerif.RiscV.Sym.cells4']
    exact hR0
  clear hR0
  sym_close (hk _ post14_0 post14_1 post14_2 post14_3 post14_4 post14_5 post14_6 post14_7 post14_8
    post14_9 post14_10 post14_11)

end Cases.Zip2005
