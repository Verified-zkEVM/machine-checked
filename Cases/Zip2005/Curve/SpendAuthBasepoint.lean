import Cases.Zip2005.Curve.FromBytesUnchecked
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Image.F_78023278
import Cases.Zip2005.Image.Ro

/-!
# `<SpendAuth as SigType>::basepoint` (reddsa)

`Ep::from_bytes_unchecked` of the 32 constant bytes at `0x78001750`, unwrapped (the `None`
case is an `assert_failed` panic), copied to the output.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem spendauth_basepoint_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 : Word)
    (cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 12) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G n P u)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN G n P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN G n P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x78023278#64) (hcode : CodeAt F_78023278.base F_78023278.prog s)
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
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x820 sp)
    (ha0 : s.getReg .x10 = a0)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x820#64) 260 a0 12)
    (hd_tb : Disjoint (sp - 0x820#64) 260 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x820#64) 260 iptr 138)
    (hd_g0 : Disjoint (sp - 0x820#64) 260 g0 1024) (hd_g1 : Disjoint (sp - 0x820#64) 260 g1 1024)
    (hd_g2 : Disjoint (sp - 0x820#64) 260 g2 1024) (hd_g3 : Disjoint (sp - 0x820#64) 260 g3 516)
    (he_tb : Disjoint a0 12 0x780488a8#64 10)
    (he_iptr : Disjoint a0 12 iptr 138)
    (he_g0 : Disjoint a0 12 g0 1024) (he_g1 : Disjoint a0 12 g1 1024)
    (he_g2 : Disjoint a0 12 g2 1024) (he_g3 : Disjoint a0 12 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x820#64, 260), (a0, 12)] s t →
      FromBytesPost 0x8d1a7284b875c963#64 0xc7f0ce37b70a10c#64 0x3b8d187c3e5f445f#64 0xb75523b328f1d606#64
        (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8 →
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) →
      Region a0 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x820#64) 260 := hstk.frame 260 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 16 := hokW.sub' 244 16 (by decide) (by bv_omega)
  -- the frame: [0, 0x68) the `CtOption<Ep>`, the flag byte at 0x6f, saved registers
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 13 := hokF.sub' 0 13 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokF.sub' 13 3 (by decide) (by bv_omega)
  obtain ⟨FE, hFE, hFEl⟩ := Region.exists_junk (sp - 0x80#64) 13 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  -- the basepoint's encoding, from rodata
  have hBp : Region 0x78001750#64 [0x8d1a7284b875c963#64, 0xc7f0ce37b70a10c#64, 0x3b8d187c3e5f445f#64, 0xb75523b328f1d606#64] s :=
    (hro.get 11 (by decide)).sub 42 4 (by decide) rfl
  have hokBp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001750#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 42 4 (by decide) (by decide)
  have he_bp : Disjoint a0 12 0x78001750#64 4 := by
    have h1 := hok0.offCode; have h2 := hok0.inMem
    simp only [AsmVerif.RiscV.Sym.Disjoint, BitVec.toNat_ofNat, Ro.layout_roBase, Ro.layout_textHi, SP1_MAX_MEMORY,
      Nat.reducePow, Nat.reduceMod] at h1 h2 ⊢
    omega
  have hu := Unchanged.refl [(sp - 0x820#64, 260), (a0, 12)] s
  have hlo := hstk.lo
  sym_exec [ep_from_bytes_unchecked_spec, memcpy96_spec, hpb, hpp, hprz, hpaf]
  -- the flag byte is `1` on the surviving path
  rw [extractByte_replaceByte _ _ (by decide)] at v10_def
  have hf : post9_12 = 1#8 := by
    rcases FromBytesPost.flag01 post9_18 with h | h
    · exact h
    · subst v10_def
      rw [h] at hbr13
      exact (hbr13 (by decide)).elim
  subst hf
  sym_close (hk _ _ _ _ _ _ _ _ _ _ _ _ _)

end Cases.Zip2005
