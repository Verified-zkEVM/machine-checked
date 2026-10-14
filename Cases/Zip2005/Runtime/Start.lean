import Cases.Zip2005.Runtime.HeapInit
import Cases.Zip2005.Runtime.MemsetStart
import Cases.Zip2005.Image.F_7801bcd0
import Cases.Zip2005.Image.F_7801be34
import Cases.Zip2005.Image.F_7801bdec
import Cases.Zip2005.Image.Ro

/-!
# `_start` and `__start` up to `main`

From the ELF entry (`0x7801bcd0`): `_start` sets `gp` and takes `sp` from the image (`0x78000000`,
the word at `0x780014b0`), `__start` runs `embedded::init` (TLSF `Heap::init` over the arena,
`heap_init_spec`), sets the first five words of `PUBLIC_VALUES_HASHER` and clears the rest
(`memset73_spec`), and calls `main` with `ra = 0x7801bea0`, `sp = 0x77fffff0`. The writes are the
two frames, the six TLSF words, and the hasher static.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem start_to_main {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (hpcS : s.pc = 0x7801bcd0#64) (hc0 : CodeAt F_7801bcd0.base F_7801bcd0.prog s)
    (hc1 : CodeAt F_7801be34.base F_7801be34.prog s) (hc2 : CodeAt F_7801bdec.base F_7801bdec.prog s)
    (hc3 : CodeAt F_7801bfac.base F_7801bfac.prog s) (hcD : CodeAt F_7801beac.base F_7801beac.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hflag : Region 0x78040620#64 [0#64] s) (hhead : Region 0x78044598#64 [0#64] s)
    (hk : ∀ t, t.pc = 0x78019ff4#64 → t.code = s.code → t.getReg .x1 = 0x7801bea0#64 →
      t.getReg .x2 = 0x77fffff0#64 → t.privateInput = s.privateInput →
      Unchanged [(0x77ffffd0#64, 4), (0x77fffff0#64, 2), (0x78040620#64, 1), (0x78044598#64, 1),
        (0x78048720#64, 1), (0x78048828#64, 1), (0x78048980#64, 4), (0x1bffffffe0#64, 2),
        (0x78048830#64, 5), (0x78048858#64, 10)] s t → RoImage Ro.layout t → SafeN G n P t) :
    SafeN G n P s := by
  have hokF0 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x77ffffd0#64 4 := RegionOk.of_nat (by decide) (by decide) (Or.inl (by decide))
  have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x77fffff0#64 2 := RegionOk.of_nat (by decide) (by decide) (Or.inl (by decide))
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78044598#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048720#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048828#64 1 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok4 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 4 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok5 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x1bffffffe0#64 2 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok6 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048830#64 5 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hok7 : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048858#64 10 := RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk 0x77ffffd0#64 4 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk 0x77fffff0#64 2 s
  obtain ⟨B2, hB2, hB2l⟩ := Region.exists_junk 0x78048720#64 1 s
  obtain ⟨B3, hB3, hB3l⟩ := Region.exists_junk 0x78048828#64 1 s
  obtain ⟨H, hH, hHl⟩ := Region.exists_junk 0x78048980#64 4 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk 0x1bffffffe0#64 2 s
  obtain ⟨S5, hS5, hS5l⟩ := Region.exists_junk 0x78048830#64 5 s
  obtain ⟨S10, hS10, hS10l⟩ := Region.exists_junk 0x78048858#64 10 s
  have hI : s.privateInput = s.privateInput := rfl
  have hu := Unchanged.refl [(0x77ffffd0#64, 4), (0x77fffff0#64, 2), (0x78040620#64, 1), (0x78044598#64, 1),
        (0x78048720#64, 1), (0x78048828#64, 1), (0x78048980#64, 4), (0x1bffffffe0#64, 2),
        (0x78048830#64, 5), (0x78048858#64, 10)] s
  have hh := fun (u : MachineState) (r sp' : Word) (hpcu : u.pc = 0x7801bfac#64) (hcu : u.code = s.code) =>
    heap_init_spec (G := G) (n := n) (P := P) u r sp' hpcu (codeAt_of_code_eq hcu hc3) (codeAt_of_code_eq hcu hcD)
      (codeWithin_of_code_eq hcu hcw)
  have hm := fun (u : MachineState) (r a0 : Word) (O : List Word) (hOl : O.length = 10)
      (hpcu : u.pc = 0x7803f57c#64) (hcu : u.code = s.code) =>
    memset73_spec (G := G) (n := n) (P := P) u r a0 O hOl hpcu (codeAt_of_code_eq hcu hcM) (codeWithin_of_code_eq hcu hcw)
  sym_exec [hh, hm] stop [0x78019ff4]
  sym_close hk

end Cases.Zip2005
