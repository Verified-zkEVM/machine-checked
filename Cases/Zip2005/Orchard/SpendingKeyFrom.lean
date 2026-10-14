import Cases.Zip2005.Blake2b.PrfExpandWith
import Cases.Zip2005.Field.FromUniform
import Cases.Zip2005.Field.FqFromUniform
import Cases.Zip2005.Image.F_780231e8
import Cases.Zip2005.Image.F_78023230
import Cases.Zip2005.Image.Ro

/-!
# `From<&SpendingKey>` for `NullifierDerivingKey` (0x780231e8) and `CommitIvkRandomness` (0x78023230)

`PrfExpand::with(sk, &[])` with the domain byte 7 (resp. 8) into a frame slot, then
`Fp::from_uniform_bytes` (resp. `Fq::from_uniform_bytes`) into the output.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

/-- The eight output words of `PrfExpand::with(sk, &[])` for the domain byte `d`. -/
def prfExpandW (d s0 s1 s2 s3 : Word) : List Word :=
  compress prfH [s0, s1, s2, s3, BitVec.zeroExtend 64 (BitVec.truncate 8 d),
    0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]
    33#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64

/-- `nk = ToBase(PRF^expand_sk([7]))` as the guest computes it: `from_uniform_bytes` on the
eight words. -/
def nkW (s0 s1 s2 s3 : Word) : List Word :=
  natToLeLimbs 4 (Fp.add
    (Fp.mul (leLimbsToNat [(prfExpandW 7#64 s0 s1 s2 s3)[0]!, (prfExpandW 7#64 s0 s1 s2 s3)[1]!,
      (prfExpandW 7#64 s0 s1 s2 s3)[2]!, (prfExpandW 7#64 s0 s1 s2 s3)[3]!]) Fp.R2)
    (Fp.mul (leLimbsToNat [(prfExpandW 7#64 s0 s1 s2 s3)[4]!, (prfExpandW 7#64 s0 s1 s2 s3)[5]!,
      (prfExpandW 7#64 s0 s1 s2 s3)[6]!, (prfExpandW 7#64 s0 s1 s2 s3)[7]!]) Fp.R3))

/-- `rivk = ToScalar(PRF^expand_sk([8]))` as the guest computes it. -/
def rivkW (s0 s1 s2 s3 : Word) : List Word :=
  natToLeLimbs 4 (Fq.add
    (Fq.mul (leLimbsToNat [(prfExpandW 8#64 s0 s1 s2 s3)[0]!, (prfExpandW 8#64 s0 s1 s2 s3)[1]!,
      (prfExpandW 8#64 s0 s1 s2 s3)[2]!, (prfExpandW 8#64 s0 s1 s2 s3)[3]!]) Fq.R2)
    (Fq.mul (leLimbsToNat [(prfExpandW 8#64 s0 s1 s2 s3)[4]!, (prfExpandW 8#64 s0 s1 s2 s3)[5]!,
      (prfExpandW 8#64 s0 s1 s2 s3)[6]!, (prfExpandW 8#64 s0 s1 s2 s3)[7]!]) Fq.R3))

theorem nk_from_spending_key_spec {P : Prop} (s : MachineState) (ra sp out sk s0 s1 s2 s3 : Word)
    (F1 F2 : List Word) (hF1 : F1.length = 74) (hF2 : F2.length = 70)
    (hpc : s.pc = 0x780231e8#64) (hcode : CodeAt F_780231e8.base F_780231e8.prog s)
    (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeFU : CodeAt F_7802e2b4.base F_7802e2b4.prog s)
    (hcodeU : CodeAt F_78028718.base F_78028718.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = sk)
    (hRF1 : Region (sp - 0x4d0#64) F1 s) (hRF2 : Region (sp - 0x280#64) F2 s)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x4d0#64) 154 sk 4) (hd2 : Disjoint (sp - 0x4d0#64) 154 out 4)
    (hd3 : Disjoint out 4 sk 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4d0#64, 154), (out, 4)] s t →
      (prfExpandW 7#64 s0 s1 s2 s3).length = 8 →
      Region out (nkW s0 s1 s2 s3) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4d0#64) 154 := hstk.frame 154 (by decide)
  have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4d0#64) 74 := hokW.sub' 0 74 (by decide) (by bv_omega)
  have hokF2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x280#64) 70 := hokW.sub' 74 70 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 8 := hokW.sub' 144 8 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokW.sub' 152 2 (by decide) (by bv_omega)
  obtain ⟨FE, hFE, hFEl⟩ := Region.exists_junk (sp - 0x50#64) 8 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hu := Unchanged.refl [(sp - 0x4d0#64, 154), (out, 4)] s
  have hlo := hstk.lo
  unfold nkW prfExpandW at hk
  sym_exec [prf_expand_with_spec, fp_from_uniform_bytes_spec]
  sym_close hk
  rw [← acc15_0_def, acc10_0_def]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]

theorem rivk_from_spending_key_spec {P : Prop} (s : MachineState) (ra sp out sk s0 s1 s2 s3 : Word)
    (F1 F2 : List Word) (hF1 : F1.length = 74) (hF2 : F2.length = 70)
    (hpc : s.pc = 0x78023230#64) (hcode : CodeAt F_78023230.base F_78023230.prog s)
    (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeFU : CodeAt F_7802f038.base F_7802f038.prog s)
    (hcodeU : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = sk)
    (hRF1 : Region (sp - 0x4d0#64) F1 s) (hRF2 : Region (sp - 0x280#64) F2 s)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x4d0#64) 154 sk 4) (hd2 : Disjoint (sp - 0x4d0#64) 154 out 4)
    (hd3 : Disjoint out 4 sk 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4d0#64, 154), (out, 4)] s t →
      (prfExpandW 8#64 s0 s1 s2 s3).length = 8 →
      Region out (rivkW s0 s1 s2 s3) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4d0#64) 154 := hstk.frame 154 (by decide)
  have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4d0#64) 74 := hokW.sub' 0 74 (by decide) (by bv_omega)
  have hokF2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x280#64) 70 := hokW.sub' 74 70 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 8 := hokW.sub' 144 8 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokW.sub' 152 2 (by decide) (by bv_omega)
  obtain ⟨FE, hFE, hFEl⟩ := Region.exists_junk (sp - 0x50#64) 8 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hu := Unchanged.refl [(sp - 0x4d0#64, 154), (out, 4)] s
  have hlo := hstk.lo
  unfold rivkW prfExpandW at hk
  sym_exec [prf_expand_with_spec, fq_from_uniform_bytes_spec]
  sym_close hk
  rw [← acc15_0_def, acc10_0_def]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]

end Cases.Zip2005
