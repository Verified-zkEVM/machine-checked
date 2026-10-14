import Cases.Zip2005.Runtime.Trivial
import Cases.Zip2005.Image.F_7801bfac
import Cases.Zip2005.Image.Ro

/-!
# TLSF `Heap::init` over the arena (`embedded_alloc`, `0x7801bfac`)

`sp1_zkvm::allocators::embedded::init` hands the arena `[0x78048980, 0x1c00000000)` to the TLSF
heap whose control block is `INNER_HEAP` (`0x78040620`, 4162 words). The run is loop-free on
concrete values: the borrow flag (word 0) is taken and released, the arena becomes one free
block of `0x1b87fb7660` bytes (header at `0x78048980`, end sentinel at `0x1bffffffe0`), pushed on
the free list of class `(31, 46)` (word 2031), whose bits are set in the second-level bitmap
(word 4128) and the first-level bitmap (word 4161). From the loaded image (`.bss` zero) the flag
and the list head are `0`, so the borrow does not panic and no back link is written.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem heap_init_spec {P : Prop} (s : MachineState) (ra sp : Word)
    (hpc : s.pc = 0x7801bfac#64) (hcode : CodeAt F_7801bfac.base F_7801bfac.prog s)
    (hcodeD : CodeAt F_7801beac.base F_7801beac.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x20 sp)
    (ha0 : s.getReg .x10 = 0x78040620#64) (ha1 : s.getReg .x11 = 0x78048980#64)
    (ha2 : s.getReg .x12 = 0x1b87fb7680#64)
    (hflag : Region 0x78040620#64 [0#64] s) (hhead : Region 0x78044598#64 [0#64] s)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → t.privateInput = s.privateInput →
      Unchanged [(sp - 0x20#64, 4), (0x78040620#64, 1), (0x78044598#64, 1), (0x78048720#64, 1),
        (0x78048828#64, 1), (0x78048980#64, 4), (0x1bffffffe0#64, 2)] s t → Safe P t) :
    Safe P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hstk.frame 4 (by decide)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78044598#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048720#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048828#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok4 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 4 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok5 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x1bffffffe0#64 2 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  obtain ⟨B2, hB2, hB2l⟩ := Region.exists_junk 0x78048720#64 1 s
  obtain ⟨B3, hB3, hB3l⟩ := Region.exists_junk 0x78048828#64 1 s
  obtain ⟨H, hH, hHl⟩ := Region.exists_junk 0x78048980#64 4 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk 0x1bffffffe0#64 2 s
  have hI : s.privateInput = s.privateInput := rfl
  have hu := Unchanged.refl [(sp - 0x20#64, 4), (0x78040620#64, 1), (0x78044598#64, 1), (0x78048720#64, 1),
        (0x78048828#64, 1), (0x78048980#64, 4), (0x1bffffffe0#64, 2)] s
  have hd := fun (u : MachineState) (r : Word) (hpcu : u.pc = 0x7801beac#64) (hcu : u.code = s.code)
      (hr : u.getReg .x1 = r) (hr1 : r &&& ~~~1#64 = r) =>
    syscall_dump_elf_spec (P := P) u r hpcu (codeAt_of_code_eq hcu hcodeD) (codeWithin_of_code_eq hcu hcw) hr hr1
  sym_exec [hd] stop [0x7801c104]
  -- the second-level index of the block's size class, which the executor keeps as atoms
  have h85 : v85 = 368#64 := by
    rw [← v85_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v77_def]; decide
  subst h85
  sym_reframe
  sym_exec [] stop [0x7801beac]
  -- the tail call `syscall_dump_elf` returns to `ra` with nothing changed
  have hc28 : s_28.code = s.code := hcode.trans hcode0
  have hcs : CalleeSaved s s_28 := CalleeSaved.intro (by rw [hx2, hsp]) hx3 hx4 hx8 hx9 hx18 hx19
    hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
  refine syscall_dump_elf_spec s_28 ra hpc (codeAt_of_code_eq hc28 hcodeD) hcw hx1 hra1 ?_
  intro t htp hts htc hti htu
  exact hk t htp (hcs.trans hts) (htc.trans hc28) (hti.trans (by assumption)) (((‹Unchanged _ s s_87›).trans hunch).trans
    (fun a _ => htu a (by simp)))

end Cases.Zip2005
