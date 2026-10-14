import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7803f57c
import Cases.Zip2005.Image.Ro

/-!
# `memset(a0, 0, 73)`: `__start`'s clearing of the public-values hasher

`__start` sets the first five words of `PUBLIC_VALUES_HASHER` (`0x78048830`) and clears the 73
bytes after them: an aligned pointer, nine doublewords and one tail byte. The spec leaves the
ten words unstated (some ten words): nothing on the accepting path reads them before
`syscall_halt`, whose hashing contract (ledger S1) does not read them either.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 40000000 in
theorem memset73_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 10)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 0#64) (ha2 : s.getReg .x12 = 73#64)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 10)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → t.privateInput = s.privateInput →
      Unchanged [(a0, 10)] s t →
      (∃ W : List Word, W.length = 10 ∧ Region a0 W t) → SafeN G n P t) :
    SafeN G n P s := by
  have hI : s.privateInput = s.privateInput := rfl
  have hu := Unchanged.refl [(a0, 10)] s
  sym_exec
  all_goals sym_close hk

end Cases.Zip2005
