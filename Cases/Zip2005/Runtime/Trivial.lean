import Cases.Zip2005.Runtime.SyscallWrite
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.F_7801beac
import Cases.Zip2005.Image.F_7801bf6c
import Cases.Zip2005.Image.F_7801bf74
import Cases.Zip2005.Image.F_7801bfa4
import Cases.Zip2005.Image.Ro

/-!
# The one- and two-instruction runtime stubs

`__rust_no_alloc_shim_is_unstable_v2` and `syscall_dump_elf` return at once; `sys_alloc_words`
and `sys_getenv` return `0` (no words, no variable); `sys_write` tail-calls `syscall_write`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- `__rust_no_alloc_shim_is_unstable_v2`: `ret`. -/
theorem no_alloc_shim_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra : Word)
    (hpc : s.pc = 0x7801aed0#64) (hcode : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [] s
  sym_exec []
  sym_close hk

/-- `syscall_dump_elf`: `ret`. -/
theorem syscall_dump_elf_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra : Word)
    (hpc : s.pc = 0x7801beac#64) (hcode : CodeAt F_7801beac.base F_7801beac.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → t.privateInput = s.privateInput →
      Unchanged [] s t → SafeN G n P t) :
    SafeN G n P s := by
  have hI : s.privateInput = s.privateInput := rfl
  have hu := Unchanged.refl [] s
  sym_exec []
  sym_close hk

/-- `sys_alloc_words`: returns `0`. -/
theorem sys_alloc_words_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra : Word)
    (hpc : s.pc = 0x7801bf6c#64) (hcode : CodeAt F_7801bf6c.base F_7801bf6c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      t.getReg .x10 = 0#64 → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [] s
  sym_exec []
  sym_close hk

/-- `sys_getenv`: returns `0` (the variable is unset). -/
theorem sys_getenv_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra : Word)
    (hpc : s.pc = 0x7801bf74#64) (hcode : CodeAt F_7801bf74.base F_7801bf74.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [] s t →
      t.getReg .x10 = 0#64 → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [] s
  sym_exec []
  sym_close hk

/-- `sys_write(fd, …)` with `fd ≠ 13`: `syscall_write`'s. -/
theorem sys_write_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp fd : Word)
    (hpc : s.pc = 0x7801bfa4#64) (hcode : CodeAt F_7801bfa4.base F_7801bfa4.prog s)
    (hcodeW : CodeAt F_7801b3b0.base F_7801b3b0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp) (ha0 : s.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6)] s t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hu := Unchanged.refl [(sp - 0x30#64, 6)] s
  sym_exec [] stop [0x7801b3b0]
  have hcs : CalleeSaved s s_2 := CalleeSaved.intro (by rw [hx2, hsp]) hx3 hx4 hx8 hx9 hx18 hx19 hx20
    hx21 hx22 hx23 hx24 hx25 hx26 hx27
  refine syscall_write_other_spec s_2 ra sp fd hpc (codeAt_of_code_eq hcode hcodeW)
    hcw hx1 hra1 hx2 hstk hx10 hfd ?_
  intro t htp hts htc htu
  exact hk t htp (hcs.trans hts) (htc.trans hcode) (hunch.trans htu)

end Cases.Zip2005
