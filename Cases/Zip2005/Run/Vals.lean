/-
  Cases.Zip2005.Run.Vals

  The payloads the guest passes to its panic entries (milestone M1): for each entry whose
  frame-checker interface pins a register (`Iface.vals`, from `infer-contracts`' traces), the
  values the call sites load into it, all `core::panic::Location`s and message pieces in
  `.rodata`. A restated panic contract asks for its register among them; the discharge lemmas
  check the lists against the interfaces (`Runtime.Panic`, `Runtime.PanicEntries`).
-/

import AsmVerif.RiscV.Sym.Layout

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64

/-- `core::panicking::assert_failed` (`0x7803a110`, the `Fr` instance), `x15`. -/
def vals_a110 : List Word :=
  [0x78001198#64, 0x780015d0#64, 0x780017f8#64, 0x780119c8#64, 0x78001950#64, 0x78011a70#64,
    0x78011ab8#64, 0x78011bc8#64, 0x78011be8#64, 0x78013878#64]

/-- `core::panicking::panic_const::panic_const_rem_by_zero` (`0x7803de78`), `x10`. -/
def vals_de78 : List Word := [0x78013660#64]

/-- `core::result::unwrap_failed` (`0x7803dc7c`), `x10`. -/
def vals_dc7c_10 : List Word := [0x78011988#64, 0x78011a88#64, 0x78013728#64, 0x78014108#64]

/-- `core::result::unwrap_failed` (`0x7803dc7c`), `x13`. -/
def vals_dc7c_13 : List Word := [0x78011968#64, 0x78011ad0#64, 0x78013708#64, 0x780140e8#64]

/-- `core::result::unwrap_failed` (`0x7803dc7c`), `x14`. -/
def vals_dc7c_14 : List Word :=
  [0x78011998#64, 0x78011af0#64, 0x78011b08#64, 0x78013758#64, 0x78013770#64, 0x78013788#64,
    0x78014160#64]

/-- `core::option::unwrap_failed` (`0x7803f364`), `x10`. -/
def vals_f364 : List Word :=
  [0x78001328#64, 0x78001310#64, 0x780012f8#64, 0x78001120#64, 0x78001108#64, 0x780010f0#64,
    0x780010d8#64, 0x780010c0#64, 0x780010a8#64, 0x78001420#64, 0x78001478#64, 0x780119e0#64,
    0x780136d8#64, 0x780136c0#64, 0x780136a8#64, 0x78013690#64]

/-- `core::panicking::panic` (`0x7803de20`), `x10`. -/
def vals_de20 : List Word :=
  [0x780012a8#64, 0x780011b0#64, 0x78001138#64, 0x780014b8#64, 0x780119f8#64, 0x78011b20#64,
    0x780137d0#64, 0x780138f8#64, 0x78013920#64, 0x78014330#64, 0x78001438#64,
    0x780017b0#64]

/-- `core::panicking::panic_bounds_check` (`0x7803dcdc`), `x12`. -/
def vals_dcdc : List Word := [0x780119b0#64, 0x78013678#64, 0x78013648#64, 0x78014318#64]

end Cases.Zip2005.Run
