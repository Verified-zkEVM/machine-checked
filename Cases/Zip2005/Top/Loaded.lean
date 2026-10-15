import Cases.Zip2005.Top.Elf
import Cases.Zip2005.Top.Load

/-!
# From the loaded image

`guest_loaded_run`: a run of the loaded image (`Cases.Zip2005.Image.Layout.image`, as
`AsmVerif.RiscV.Load` reads the ELF) with private input `I` is `SafeN G n (GuestAccepts I)` at every budget `n`. The
code of every function the proofs step and the code window are theorems about that image
(`RunCode.of_image`, `Top/Load.lean`), kernel-checked against the generated data; `main`'s entry
state is `guest_elf_run`'s; of the input, only that it fits the hint area. What stays assumed is `RunHyps`, which `Top/Guest.lean`
reduces to the panic and reject-halt paths.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.Top

set_option autoImplicit false

theorem guest_loaded_run {G : MachineState → Prop} {n : Nat} (I : List (BitVec 8))
    (hH : RunHyps G n (start I) I) (hIl : I.length < 2 ^ 60)
    (hIfit : I.length + 1416 ≤ 0x400000000) :
    SafeN G n (Cases.Zip2005.Top.GuestAccepts I) (start I) :=
  guest_elf_run I { toRunCode := RunCode.of_image (start_code I), toRunHyps := hH } hIl hIfit

end Cases.Zip2005
