import Cases.Zip2005.Curve.FromBytesKit
import Cases.Zip2005.Image.F_780234cc
import Cases.Zip2005.Image.Ro

/-!
# `sinsemilla::lebs2ip_k`

Ten boolean bytes to a 10-bit integer, little-endian: the compiled shift-or-add tree over
the bytes (`lebs2ipK`); for bytes that are `0` or `1` it is `Σ bᵢ·2ⁱ`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- The compiled expression: bits 0–7 through `or`s and two `add`s (then `zext.b`), bits 8–9 `or`ed in. -/
def lebs2ipK (w0 w1 : Word) : Word :=
  ((BitVec.zeroExtend 64 (extractByte w1 1) <<< 9) ||| (BitVec.zeroExtend 64 (extractByte w1 0) <<< 8)) |||
    ((((BitVec.zeroExtend 64 (extractByte w0 7) <<< 7) + (BitVec.zeroExtend 64 (extractByte w0 6) <<< 6)) +
        ((((BitVec.zeroExtend 64 (extractByte w0 1) <<< 1) ||| BitVec.zeroExtend 64 (extractByte w0 0)) |||
            ((BitVec.zeroExtend 64 (extractByte w0 2) <<< 2) ||| (BitVec.zeroExtend 64 (extractByte w0 3) <<< 3))) |||
          ((BitVec.zeroExtend 64 (extractByte w0 4) <<< 4) ||| (BitVec.zeroExtend 64 (extractByte w0 5) <<< 5)))) &&&
      255#64)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem lebs2ip_k_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 : Word) (w0 w1 : Word)
    (hpc : s.pc = 0x780234cc#64) (hcode : CodeAt F_780234cc.base F_780234cc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra) (ha0 : s.getReg .x10 = a0)
    (hb : Region a0 [w0, w1] s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 2)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      t.getReg .x10 = lebs2ipK w0 w1 → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [] s
  sym_exec
  have hfin : s_30.getReg .x10 = lebs2ipK w0 w1 := by
    rw [hx10]
    sym_subst
    rfl
  sym_close hk

end Cases.Zip2005
