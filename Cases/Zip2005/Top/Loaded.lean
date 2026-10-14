import Cases.Zip2005.Top.Elf
import Cases.Zip2005.Top.Load

/-!
# From the loaded image

`guest_loaded_run`: a run of the loaded image (`Cases.Zip2005.Image.Layout.image`, as
`AsmVerif.RiscV.Load` reads the ELF) with private input `I` is `Safe (GuestAccepts I)`. The
image premises of `guest_elf_run` — the code of every function the proofs step, the code
window, the read-only segment, three `.data`/`.bss` words and the entry point — are theorems
about that image (`Top/Load.lean`), kernel-checked against the generated data. What stays
assumed is `RunHyps` (the runtime contracts) and the input condition (`hbp_eq`, `hokJ2`,
`hbp`: the first input record's length leaves the second's buffer in memory).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.Top

set_option autoImplicit false

set_option maxRecDepth 10000 in
theorem guest_loaded_run (I : List (BitVec 8)) (bp : Word)
    (hH : RunHyps (start I) I) (hIl : I.length < 2 ^ 60)
    (hbp_eq : bp = 0x1c00000000#64 + (bytesToWordLE (I.take 8) + 7#64 &&& 18446744073709551608#64))
    (hokJ2 : RegionOk Ro.layout.textLo Ro.layout.textHi bp 175) (hbp : 0x1c00000000 ≤ bp.toNat) :
    Safe (Cases.Zip2005.Top.GuestAccepts I) (start I) := by
  have hR : RunContracts (start I) I :=
    { toRunCode := RunCode.of_image (start_code I), toRunHyps := hH }
  exact guest_elf_run (start I) I bp hR (start_pc I)
    (codeAt_of_image Loaded.codeWF Layout.code_F_7801bcd0 F_7801bcd0.decode_ok (start_code I))
    (codeAt_of_image Loaded.codeWF Layout.code_F_7801be34 F_7801be34.decode_ok (start_code I))
    (codeAt_of_image Loaded.codeWF Layout.code_F_7801bdec F_7801bdec.decode_ok (start_code I))
    (codeAt_of_image Loaded.codeWF Layout.code_F_7801bfac F_7801bfac.decode_ok (start_code I))
    (codeAt_of_image Loaded.codeWF Layout.code_F_7801beac F_7801beac.decode_ok (start_code I))
    (roImage (start_getMem I)) (start_input I) hIl
    (data2_word I 0 (by decide +kernel) (by decide) (by decide +kernel))
    (data2_word I 1 (by decide +kernel) (by decide) (by decide +kernel))
    (data2_word I 2032 (by decide +kernel) (by decide) (by decide +kernel))
    hbp_eq hokJ2 hbp

end Cases.Zip2005
