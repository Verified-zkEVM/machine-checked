/-
  Cases.Zip2005.Memset

  `memset(a0, 0, 96)` on a doubleword-aligned block, as `mul` calls it for the
  identity: the byte loops are skipped and the word loop stores twelve zeros.
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7803f57c
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 40000000 in
theorem memset96_spec {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 12)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 0#64) (ha2 : s.getReg .x12 = 96#64)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 12)] s t →
      Region a0 (List.replicate 12 0#64) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(a0, 12)] s
  sym_exec
  all_goals sym_close hk
  sym_subst
  rfl

-- `memset(a0, 0, 32)`: the four words of a point encoding, as `Ep::to_bytes` clears the identity.
set_option maxHeartbeats 40000000 in
theorem memset32_spec {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 4)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 0#64) (ha2 : s.getReg .x12 = 32#64)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 4)] s t →
      Region a0 (List.replicate 4 0#64) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(a0, 4)] s
  sym_exec
  all_goals sym_close hk
  sym_subst
  rfl

-- `memset(a0, 0, 128)`: BLAKE2b's block buffer, as `compress1_loop` zeroes it before a partial block.
set_option maxHeartbeats 40000000 in
theorem memset128_spec {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 16)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 0#64) (ha2 : s.getReg .x12 = 128#64)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 16)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 16)] s t →
      Region a0 (List.replicate 16 0#64) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(a0, 16)] s
  sym_exec
  all_goals sym_close hk
  sym_subst
  rfl

end Cases.Zip2005
