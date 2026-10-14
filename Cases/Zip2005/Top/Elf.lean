import Cases.Zip2005.Top.Assumptions
import Cases.Zip2005.Runtime.Start
import Cases.Zip2005.Image.Ro

/-!
# From the ELF entry

`guest_elf_run`: a run from the ELF's entry point (`_start`, `0x7801bcd0`) over the loaded image is
`Safe (GuestAccepts I)`. `__start` is stepped (`start_to_main`), so `main`'s entry state (ledger
A2: its return address, stack, the hint area's bump pointer) is no longer assumed but read off
the image: the stack top `0x78000000` (`.rodata`), `EMBEDDED_RESERVED_INPUT_PTR` at `0x1c00000000`
(`.data`), and two words of `INNER_HEAP` zero (`.bss`). What stays assumed is `RunContracts`
(code, A3–A12), and of the input that its first record's length leaves the second's buffer in
memory (`hbp_eq`, `hokJ2`, `hbp`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem guest_elf_run {G : MachineState → Prop} {n : Nat} (s : MachineState) (I : List (BitVec 8)) (bp : Word) (hR : RunContracts G n s I)
    (hpc : s.pc = 0x7801bcd0#64) (hc0 : CodeAt F_7801bcd0.base F_7801bcd0.prog s)
    (hc1 : CodeAt F_7801be34.base F_7801be34.prog s) (hc2 : CodeAt F_7801bdec.base F_7801bdec.prog s)
    (hc3 : CodeAt F_7801bfac.base F_7801bfac.prog s) (hcD : CodeAt F_7801beac.base F_7801beac.prog s)
    (hro : RoImage Ro.layout s) (hI : s.privateInput = I) (hIl : I.length < 2 ^ 60)
    (hdata : Region 0x78040618#64 [0x1c00000000#64] s)
    (hflag : Region 0x78040620#64 [0#64] s) (hhead : Region 0x78044598#64 [0#64] s)
    (hbp_eq : bp = 0x1c00000000#64 + (bytesToWordLE (I.take 8) + 7#64 &&& 18446744073709551608#64))
    (hokJ2 : RegionOk Ro.layout.textLo Ro.layout.textHi bp 175) (hbp : 0x1c00000000 ≤ bp.toNat) :
    SafeN G n (Cases.Zip2005.Top.GuestAccepts I) s := by
  refine start_to_main s hpc hc0 hc1 hc2 hc3 hcD hR.hc_7803f57c hR.hcw hro hflag hhead ?_
  intro t htpc htc hra hsp hti hun hrot
  have hB : Region 0x78040618#64 [0x1c00000000#64] t := by
    refine hdata.of_unchanged' hun rfl ?_
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (unfold AsmVerif.RiscV.Sym.Disjoint; decide)
  exact guest_accepting_run' t 0x7801bea0#64 0x77fffff0#64 0x1c00000000#64 I bp
    { toRunContracts := hR.of_code_eq htc
      hpc := htpc
      hro := hrot
      hra := hra
      hra1 := by decide
      hsp := hsp
      hstk := ⟨by decide, by decide, by decide⟩
      hI := hti.trans hI
      hIl := hIl
      hB := hB
      hb := by decide
      hokJ := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
      hbp_eq := hbp_eq
      hokJ2 := hokJ2
      hbp := hbp }

end Cases.Zip2005
