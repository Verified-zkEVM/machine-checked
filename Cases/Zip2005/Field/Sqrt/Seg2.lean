import Cases.Zip2005.Field.Sqrt.Cut
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-! `SqrtTables::sqrt_common` (Fp), segment 2 (between the cuts). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sq_seg2 {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s0 : MachineState) (sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word) (t : MachineState)
    (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s0.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s0.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s0.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hstk : StackOk Ro.layout 0x1b0 sp) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4) (hd0 : Disjoint (sp - 0x1b0#64) 54 a0 4)
    (hok_a2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4) (hd_a2 : Disjoint (sp - 0x1b0#64) 54 a2 4) (he_a2 : Disjoint a0 4 a2 4)
    (hok_a3 : RegionOk Ro.layout.roBase Ro.layout.textHi a3 4) (hd_a3 : Disjoint (sp - 0x1b0#64) 54 a3 4) (he_a3 : Disjoint a0 4 a3 4)
    (hok_tb : RegionOk Ro.layout.roBase Ro.layout.textHi tb 9) (hd_tb : Disjoint (sp - 0x1b0#64) 54 tb 9) (he_tb : Disjoint a0 4 tb 9)
    (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138) (hd_iptr : Disjoint (sp - 0x1b0#64) 54 iptr 138) (he_iptr : Disjoint a0 4 iptr 138)
    (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024) (hd_g0 : Disjoint (sp - 0x1b0#64) 54 g0 1024) (he_g0 : Disjoint a0 4 g0 1024)
    (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024) (hd_g1 : Disjoint (sp - 0x1b0#64) 54 g1 1024) (he_g1 : Disjoint a0 4 g1 1024)
    (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024) (hd_g2 : Disjoint (sp - 0x1b0#64) 54 g2 1024) (he_g2 : Disjoint a0 4 g2 1024)
    (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516) (hd_g3 : Disjoint (sp - 0x1b0#64) 54 g3 516) (he_g3 : Disjoint a0 4 g3 516)
    (h : SqCut1 s0 sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx IV G0 G1 G2 G3 0x7802fa0c#64 L t)
    (hk : ∀ u, SqCut2 s0 sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx IV G0 G1 G2 G3 0x780301f0#64 L u → SafeN G n P u) : SafeN G n P t := by
  obtain ⟨hpc, hcode, hcA, hcM, hcL, hcw, hro, hheap, hU0, hx2, hx3, hx4, hx8, hx9, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, ⟨B, hBl, hB⟩, hS, ⟨O, hOl, hO⟩,
    hRU, hRV, hRT, hRIV, hRG0, hRG1, hRG2, hRG3⟩ := h
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1b0#64) 54 := hstk.frame 54 (by decide)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1b0#64) 41 := hokF.sub' 0 41 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokF.sub' 41 13 (by decide) (by bv_omega)
  have hpb' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = t.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u :=
    fun u sp' L' h1 h2 => hpb u sp' L' h1 (h2.trans hcode)
  have hpp' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = t.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u :=
    fun u sp' L' h1 h2 => hpp u sp' L' h1 (h2.trans hcode)
  have hprz' : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = t.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u :=
    fun u sp' L' h1 h2 => hprz u sp' L' h1 (h2.trans hcode)
  clear hpb hpp hprz
  have hu := Unchanged.refl [(sp - 432#64, 54), (a0, 4)] t
  have hk' : ∀ (u : MachineState) (B' : List Word) (O' : List Word),
      u.pc = 0x780301f0#64 → u.code = t.code → CodeAt F_7802f358.base F_7802f358.prog u →
      CodeAt F_7801bf5c.base F_7801bf5c.prog u → CodeAt F_78029b64.base F_78029b64.prog u →
      CodeWithin Ro.layout.textLo Ro.layout.textHi u → RoImage Ro.layout u → Run.HeapAt L u → Unchanged [(sp - 432#64, 54), (a0, 4)] t u →
      u.getReg .x2 = sp - 432#64 →
      u.getReg .x3 = t.getReg .x3 →
      u.getReg .x4 = t.getReg .x4 →
      u.getReg .x8 = a0 →
      u.getReg .x9 = tb →
      u.getReg .x18 = a2 →
      u.getReg .x19 = 11037532056220336129#64 →
      u.getReg .x20 = 2469829653914515739#64 →
      u.getReg .x21 = 2445952672640170197#64 →
      u.getReg .x22 = 8127635680764926565#64 →
      u.getReg .x23 = 12438865661331504215#64 →
      u.getReg .x24 = 14933811601259063721#64 →
      u.getReg .x25 = tb →
      u.getReg .x26 = t.getReg .x26 →
      u.getReg .x27 = t.getReg .x27 →
      B'.length = 41 → Region (sp - 432#64) B' u →
      Region (sp - 104#64) [s0.getReg .x27, s0.getReg .x26, s0.getReg .x25, s0.getReg .x24, s0.getReg .x23, s0.getReg .x22,
      s0.getReg .x21, s0.getReg .x20, s0.getReg .x19, s0.getReg .x18, s0.getReg .x9, s0.getReg .x8,
      s0.getReg .x1] u → O'.length = 4 → Region a0 O' u →
      Region a2 [uv0, uv1, uv2, uv3] u → Region a3 [vv0, vv1, vv2, vv3] u → Region tb [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx] u → Region iptr IV u →
      Region g0 G0 u → Region g1 G1 u → Region g2 G2 u → Region g3 G3 u → SafeN G n P u := by
    intro u B' O' upc ucode ucA ucM ucL ucw uro uH uU ux2 ux3 ux4 ux8 ux9 ux18 ux19 ux20 ux21 ux22 ux23 ux24 ux25 ux26 ux27 uBl uB uS uOl uO uU' uV' uT' uIV' uG0 uG1 uG2 uG3
    exact hk u ⟨upc, ucode.trans hcode, ucA, ucM, ucL, ucw, uro, uH, hU0.trans uU, ux2, (ux3.trans hx3), (ux4.trans hx4), ux8, ux9, ux18, ux19, ux20, ux21, ux22, ux23, ux24, ux25, (ux26.trans hx26), (ux27.trans hx27),
      ⟨B', uBl, uB⟩, uS, ⟨O', uOl, uO⟩, uU', uV', uT', uIV', uG0, uG1, uG2, uG3⟩
  sym_exec [uint256_mulmod_spec, fp_get_lower_32_spec, hpb', hpp', hprz'] stop [0x780301f0]
  sym_close hk' _ _ _
  all_goals rfl

end Cases.Zip2005
