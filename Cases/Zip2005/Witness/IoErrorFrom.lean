import AsmVerif.RiscV.Sym
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_78036184
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro

/-!
# `From<io::Error> for Box<bincode::ErrorKind>` (0x78036184)

`Box::new(ErrorKind::Io(e))`: `__rust_alloc(0x18, 8)` (ledger T2), the discriminant word
`0x8000000000000000` and the error stored, the box returned; a null pointer goes to
`handle_alloc_error`, which diverges.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem io_error_from_spec {P : Prop} (s : MachineState) (ra sp : Word)
    (hpc : s.pc = 0x78036184#64) (hcode : CodeAt F_78036184.base F_78036184.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x40 sp)
    (hhandle : ∀ u : MachineState, u.pc = 0x7803d1a8#64 → u.code = s.code → Safe P u)
    (halloc : ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x780361ac#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x780361ac#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x18 ≤ 0x1c00000000 → Safe P t) → Safe P u)
    (hk : ∀ (t : MachineState) (e : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t → t.getReg .x10 = e →
      Safe P t) :
    Safe P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 8 := hstk.frame 8 (by decide)
  have hu := Unchanged.refl [(sp - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokS.sub' 6 2 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  sym_exec [halloc, hhandle]
  sym_close (hk _ post11_0)

end Cases.Zip2005
