import Cases.Zip2005.Field.GetLower32
import Cases.Zip2005.Field.PowT
import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7802f358
import Cases.Zip2005.Image.F_7801bf5c
import Cases.Zip2005.Image.Ro

/-! `SqrtTables::sqrt_common` (Fp): the cut states between its three segments. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- The state of `sqrt_common` at a cut: the frame's data block arbitrary, the saved
    registers in place, the pointers and the constants in registers, every input region
    as on entry. -/
def SqCut1 (s0 : MachineState) (sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word) (c : Word) (t : MachineState) : Prop :=
  t.pc = c ∧ t.code = s0.code ∧ CodeAt F_7802f358.base F_7802f358.prog t ∧
    CodeAt F_7801bf5c.base F_7801bf5c.prog t ∧ CodeAt F_78029b64.base F_78029b64.prog t ∧
    CodeWithin Ro.layout.textLo Ro.layout.textHi t ∧ RoImage Ro.layout t ∧ Unchanged [(sp - 432#64, 54), (a0, 4)] s0 t ∧
    t.getReg .x2 = sp - 432#64 ∧
    t.getReg .x3 = s0.getReg .x3 ∧
    t.getReg .x4 = s0.getReg .x4 ∧
    t.getReg .x8 = a0 ∧
    t.getReg .x9 = tb ∧
    t.getReg .x18 = a2 ∧
    t.getReg .x19 = 11037532056220336129#64 ∧
    t.getReg .x20 = 2469829653914515739#64 ∧
    t.getReg .x21 = 2445952672640170197#64 ∧
    t.getReg .x22 = 8127635680764926565#64 ∧
    t.getReg .x23 = 12438865661331504215#64 ∧
    t.getReg .x24 = 14933811601259063721#64 ∧
    t.getReg .x25 = 4611686018427387904#64 ∧
    t.getReg .x26 = s0.getReg .x26 ∧
    t.getReg .x27 = s0.getReg .x27 ∧
    (∃ B : List Word, B.length = 41 ∧ Region (sp - 432#64) B t) ∧
    Region (sp - 104#64) [s0.getReg .x27, s0.getReg .x26, s0.getReg .x25, s0.getReg .x24, s0.getReg .x23, s0.getReg .x22,
      s0.getReg .x21, s0.getReg .x20, s0.getReg .x19, s0.getReg .x18, s0.getReg .x9, s0.getReg .x8,
      s0.getReg .x1] t ∧
    (∃ O : List Word, O.length = 4 ∧ Region a0 O t) ∧
    Region a2 [uv0, uv1, uv2, uv3] t ∧ Region a3 [vv0, vv1, vv2, vv3] t ∧ Region tb [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx] t ∧ Region iptr IV t ∧
    Region g0 G0 t ∧ Region g1 G1 t ∧ Region g2 G2 t ∧ Region g3 G3 t

/-- The state of `sqrt_common` at a cut: the frame's data block arbitrary, the saved
    registers in place, the pointers and the constants in registers, every input region
    as on entry. -/
def SqCut2 (s0 : MachineState) (sp a0 tb a2 a3 uv0 uv1 uv2 uv3 vv0 vv1 vv2 vv3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word) (c : Word) (t : MachineState) : Prop :=
  t.pc = c ∧ t.code = s0.code ∧ CodeAt F_7802f358.base F_7802f358.prog t ∧
    CodeAt F_7801bf5c.base F_7801bf5c.prog t ∧ CodeAt F_78029b64.base F_78029b64.prog t ∧
    CodeWithin Ro.layout.textLo Ro.layout.textHi t ∧ RoImage Ro.layout t ∧ Unchanged [(sp - 432#64, 54), (a0, 4)] s0 t ∧
    t.getReg .x2 = sp - 432#64 ∧
    t.getReg .x3 = s0.getReg .x3 ∧
    t.getReg .x4 = s0.getReg .x4 ∧
    t.getReg .x8 = a0 ∧
    t.getReg .x9 = tb ∧
    t.getReg .x18 = a2 ∧
    t.getReg .x19 = 11037532056220336129#64 ∧
    t.getReg .x20 = 2469829653914515739#64 ∧
    t.getReg .x21 = 2445952672640170197#64 ∧
    t.getReg .x22 = 8127635680764926565#64 ∧
    t.getReg .x23 = 12438865661331504215#64 ∧
    t.getReg .x24 = 14933811601259063721#64 ∧
    t.getReg .x25 = tb ∧
    t.getReg .x26 = s0.getReg .x26 ∧
    t.getReg .x27 = s0.getReg .x27 ∧
    (∃ B : List Word, B.length = 41 ∧ Region (sp - 432#64) B t) ∧
    Region (sp - 104#64) [s0.getReg .x27, s0.getReg .x26, s0.getReg .x25, s0.getReg .x24, s0.getReg .x23, s0.getReg .x22,
      s0.getReg .x21, s0.getReg .x20, s0.getReg .x19, s0.getReg .x18, s0.getReg .x9, s0.getReg .x8,
      s0.getReg .x1] t ∧
    (∃ O : List Word, O.length = 4 ∧ Region a0 O t) ∧
    Region a2 [uv0, uv1, uv2, uv3] t ∧ Region a3 [vv0, vv1, vv2, vv3] t ∧ Region tb [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx] t ∧ Region iptr IV t ∧
    Region g0 G0 t ∧ Region g1 G1 t ∧ Region g2 G2 t ∧ Region g3 G3 t

end Cases.Zip2005
