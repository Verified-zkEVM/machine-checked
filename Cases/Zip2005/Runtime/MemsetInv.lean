/-
  Cases.Zip2005.MemsetInv

  `memset(a0, 1, 1098)`: `SqrtTables::new`'s `inv` table, every entry `1` before the hash loop
  fills it. Stated over the block's 138 doublewords without their contents: the tables are
  shape-only (ledger A3).
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7803f57c
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem memset1098_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 138)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 1#64) (ha2 : s.getReg .x12 = 1098#64)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 138)
    (hk : ∀ (t : MachineState) (O' : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(a0, 138)] s t → O'.length = 138 → Region a0 O' t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(a0, 138)] s
  sym_exec
  sym_close hk
  rfl

end Cases.Zip2005
