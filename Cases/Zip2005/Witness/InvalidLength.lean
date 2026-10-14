import AsmVerif.RiscV.Sym
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_78019f50
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro

/-!
# `<Box<bincode::ErrorKind> as serde::de::Error>::invalid_length` (0x78019f50)

`Error::custom(format_args!("invalid length {len}, expected {exp}"))`: the `Arguments` built in
the frame, `alloc::fmt::format::format_inner` (0x7803d1cc) into a `String` (three words, a
**contract** here: it returns, writes the `String` and touches only its frame and the heap,
ledger T2), the box `__rust_alloc(0x18, 8)` (T2) filled with the `String`, the box returned; a
null box goes to `handle_alloc_error`. Every caller passes the result up as an `Err`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem invalid_length_spec {P : Prop} (s : MachineState) (ra sp : Word)
    (hpc : s.pc = 0x78019f50#64) (hcode : CodeAt F_78019f50.base F_78019f50.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x460 sp)
    (hfmt : ∀ (u : MachineState) (sp' d : Word), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fa4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78019fa4#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        S.length = 3 → Region d S t → Safe P t) → Safe P u)
    (hhandle : ∀ u : MachineState, u.pc = 0x7803d1a8#64 → u.code = s.code → Safe P u)
    (halloc : ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fbc#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78019fbc#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x18 ≤ 0x1c00000000 → Safe P t) → Safe P u)
    (hk : ∀ (t : MachineState) (e : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x460#64, 140), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t → t.getReg .x10 = e →
      Safe P t) :
    Safe P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x460#64) 140 := hstk.frame 140 (by decide)
  have hu := Unchanged.refl [(sp - 0x460#64, 140), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  -- the frame (`sp' = sp - 0x60`): [0, 8), the arguments [8, 0x40), the `String` [0x40, 0x58),
  -- the save [0x58, 0x60)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 8 := hokS.sub' 128 8 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 3 := hokS.sub' 136 3 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8#64) 1 := hokS.sub' 139 1 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x60#64) 8 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x20#64) 3 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x8#64) 1 s
  sym_exec [hfmt, halloc, hhandle]
  sym_close (hk _ post29_0)

end Cases.Zip2005
