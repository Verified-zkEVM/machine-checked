/-
  Cases.Zip2005.MemsetMore

  `memset(a0, 0, 144)`: the BLAKE2b `Params` block (key and salt, `0x90` bytes) that
  `PrfExpand::apply` zeroes before setting the fields it uses.
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7803f57c
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memset(a0, 0, 144)`: eighteen zero doublewords. -/
theorem memset144_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 18)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 0#64) (ha2 : s.getReg .x12 = 144#64)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 18)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 18)] s t →
      Region a0 (List.replicate 18 0#64) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(a0, 18)] s
  sym_exec
  all_goals sym_close hk
  sym_subst
  rfl

end Cases.Zip2005
