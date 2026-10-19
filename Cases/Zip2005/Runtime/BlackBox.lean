/-
  Cases.Zip2005.BlackBox

  `subtle::black_box::<u8>`: the byte, through a stack slot the optimiser
  cannot see through.
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Image.F_7803a0fc
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

theorem black_box_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp v : Word)
    (hpc : s.pc = 0x7803a0fc#64) (hcode : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp) (ha0 : s.getReg .x10 = v)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2)] s t →
      t.getReg .x10 = BitVec.zeroExtend 64 (BitVec.truncate 8 v) → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hF, hFlen⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(sp - 0x10#64, 2)] s
  sym_exec
  sym_close hk
  sym_subst
  rw [hx10, extractByte_replaceByte _ 7 (by decide)]

end Cases.Zip2005
