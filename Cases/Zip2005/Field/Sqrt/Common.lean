import Cases.Zip2005.Field.Sqrt.Seg3
import Cases.Zip2005.Image.Ro

/-! `SqrtTables::sqrt_common` (Fp): segment 1 (entry to the first cut) and the whole function. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `SqrtTables::<Fp>::sqrt_common(&self, uv, v)`: memory-safe, and the result is canonical
    (`< p`, the last `UINT256_MULMOD` is modulo `p`). Its value is left unconstrained: the
    caller `sqrt_alt` checks it (`res² = u` or `res² = ROOT·u`, else panic), so no property of
    the lookup tables beyond their extent is needed. Three segments (`Cases.Zip2005.Field.Sqrt.Seg*`). -/
theorem sqrt_common_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word)
    (O IV G0 G1 G2 G3 : List Word) (hOl : O.length = 4)
    (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G n P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN G n P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → SafeN G n P u)
    (hstk : StackOk Ro.layout 0x1b0 sp) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd0 : Disjoint (sp - 0x1b0#64) 54 a0 4)
    (hilen : ilen.toNat ≤ 1104)
    (hok_a2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4) (hd_a2 : Disjoint (sp - 0x1b0#64) 54 a2 4) (he_a2 : Disjoint a0 4 a2 4)
    (hok_a3 : RegionOk Ro.layout.roBase Ro.layout.textHi a3 4) (hd_a3 : Disjoint (sp - 0x1b0#64) 54 a3 4) (he_a3 : Disjoint a0 4 a3 4)
    (hok_tb : RegionOk Ro.layout.roBase Ro.layout.textHi tb 9) (hd_tb : Disjoint (sp - 0x1b0#64) 54 tb 9) (he_tb : Disjoint a0 4 tb 9)
    (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138) (hd_iptr : Disjoint (sp - 0x1b0#64) 54 iptr 138) (he_iptr : Disjoint a0 4 iptr 138)
    (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024) (hd_g0 : Disjoint (sp - 0x1b0#64) 54 g0 1024) (he_g0 : Disjoint a0 4 g0 1024)
    (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024) (hd_g1 : Disjoint (sp - 0x1b0#64) 54 g1 1024) (he_g1 : Disjoint a0 4 g1 1024)
    (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024) (hd_g2 : Disjoint (sp - 0x1b0#64) 54 g2 1024) (he_g2 : Disjoint a0 4 g2 1024)
    (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516) (hd_g3 : Disjoint (sp - 0x1b0#64) 54 g3 516) (he_g3 : Disjoint a0 4 g3 516)
    (hpc : s.pc = 0x7802f358#64) (hcode : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = tb) (ha2 : s.getReg .x12 = a2)
    (ha3 : s.getReg .x13 = a3)
    (hO : Region a0 O s)
    (hU : Region a2 [uv0, uv1, uv2, uv3] s) (hV : Region a3 [vv0, vv1, vv2, vv3] s)
    (hT : Region tb [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx] s) (hIV : Region iptr IV s)
    (hG0 : Region g0 G0 s) (hG1 : Region g1 G1 s) (hG2 : Region g2 G2 s) (hG3 : Region g3 G3 s)
    (hk : ∀ (t : MachineState) (r0 r1 r2 r3 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x1b0#64, 54), (a0, 4)] s t → Region a0 [r0, r1, r2, r3] t →
      leLimbsToNat [r0, r1, r2, r3] < Fp.p → SafeN G n P t) :
    SafeN G n P s := by
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1b0#64) 54 := hstk.frame 54 (by decide)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1b0#64) 41 := hokF.sub' 0 41 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 41 13 (by decide) (by bv_omega)
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk (sp - 0x1b0#64) 41 s
  obtain ⟨S, hS, hSl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x1b0#64, 54), (a0, 4)] s
  have hra1' : s.getReg .x1 &&& ~~~1#64 = s.getReg .x1 := by rw [hra]; exact hra1
  have hk' : ∀ (u : MachineState) (B' O' : List Word),
      u.pc = 0x7802fa0c#64 → u.code = s.code → CodeAt F_7802f358.base F_7802f358.prog u →
      CodeAt F_7801bf5c.base F_7801bf5c.prog u → CodeAt F_78029b64.base F_78029b64.prog u →
      CodeWithin Ro.layout.textLo Ro.layout.textHi u → RoImage Ro.layout u → Unchanged [(sp - 432#64, 54), (a0, 4)] s u →
      u.getReg .x2 = sp - 432#64 →
      u.getReg .x3 = s.getReg .x3 →
      u.getReg .x4 = s.getReg .x4 →
      u.getReg .x8 = a0 →
      u.getReg .x9 = tb →
      u.getReg .x18 = a2 →
      u.getReg .x19 = 11037532056220336129#64 →
      u.getReg .x20 = 2469829653914515739#64 →
      u.getReg .x21 = 2445952672640170197#64 →
      u.getReg .x22 = 8127635680764926565#64 →
      u.getReg .x23 = 12438865661331504215#64 →
      u.getReg .x24 = 14933811601259063721#64 →
      u.getReg .x25 = 4611686018427387904#64 →
      u.getReg .x26 = s.getReg .x26 →
      u.getReg .x27 = s.getReg .x27 →
      B'.length = 41 → Region (sp - 432#64) B' u →
      Region (sp - 104#64) [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23, s.getReg .x22,
        s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18, s.getReg .x9, s.getReg .x8,
        s.getReg .x1] u → O'.length = 4 → Region a0 O' u →
      Region a2 [uv0, uv1, uv2, uv3] u → Region a3 [vv0, vv1, vv2, vv3] u → Region tb [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx] u →
      Region iptr IV u → Region g0 G0 u → Region g1 G1 u → Region g2 G2 u → Region g3 G3 u →
      SafeN G n P u := by
    intro u B' O' upc ucode ucA ucM ucL ucw uro uU ux2 ux3 ux4 ux8 ux9 ux18 ux19 ux20 ux21 ux22 ux23 ux24 ux25 ux26 ux27 uBl uB uS uOl uO uU' uV' uT' uIV' uG0 uG1 uG2 uG3
    exact sq_seg2 s sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx IV G0 G1 G2 G3 u hIVl hG0l hG1l hG2l hG3l hpb hpp hprz hstk hok0 hd0 hok_a2 hd_a2 he_a2 hok_a3 hd_a3 he_a3 hok_tb hd_tb he_tb hok_iptr hd_iptr he_iptr hok_g0 hd_g0 he_g0 hok_g1 hd_g1 he_g1 hok_g2 hd_g2 he_g2 hok_g3 hd_g3 he_g3
      ⟨upc, ucode, ucA, ucM, ucL, ucw, uro, uU, ux2, ux3, ux4, ux8, ux9, ux18, ux19, ux20, ux21, ux22, ux23, ux24, ux25, ux26, ux27, ⟨B', uBl, uB⟩, uS, ⟨O', uOl, uO⟩,
        uU', uV', uT', uIV', uG0, uG1, uG2, uG3⟩
      (fun u2 h2 => sq_seg3 s sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx IV G0 G1 G2 G3 u2 hIVl hG0l hG1l hG2l hG3l hpb hpp hprz hstk hok0 hd0 hilen hok_a2 hd_a2 he_a2 hok_a3 hd_a3 he_a3 hok_tb hd_tb he_tb hok_iptr hd_iptr he_iptr hok_g0 hd_g0 he_g0 hok_g1 hd_g1 he_g1 hok_g2 hd_g2 he_g2 hok_g3 hd_g3 he_g3 h2 hsp hra1'
        (fun t r0 r1 r2 r3 h1 => hk t r0 r1 r2 r3 (h1.trans hra)))
  sym_exec [uint256_mulmod_spec, fp_get_lower_32_spec, hpb, hpp, hprz] stop [0x7802fa0c]
  sym_close hk' _ _ _
  all_goals first | rfl | rw [hra]

end Cases.Zip2005
