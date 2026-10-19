/-
  Cases.Zip2005.Top.Guest

  The end theorem with the runtime discharged (milestone M1): of `RunHyps`, the allocator's
  contracts (`__rust_alloc`, `__rust_dealloc`, `__rust_realloc` at every call site, the
  `FP_TABLES` build's included) and `From<io::Error>` are theorems about the loaded image
  (`Run/Discharge`, `Run/ReallocContracts`, `Run/ReallocOr`, `Run/SqContracts`). What stays
  assumed is `PanicPaths`: that the panic entries and the reject-halt and formatting paths never
  accept.
-/

import Cases.Zip2005.Top.Loaded
import Cases.Zip2005.Run.ReallocOr
import Cases.Zip2005.Run.SqContracts

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym Cases.Zip2005.Top Cases.Zip2005.Run

set_option autoImplicit false

/-- The premises of `RunHyps` left assumed: the panic entries (`panic_fmt`, the bounds, overflow
    and `unwrap` panics, `handle_error`, `handle_alloc_error`), the reject halts on a short or
    empty input, and the formatting path. Each says the path never accepts. -/
structure PanicPaths (G : MachineState → Prop) (n : Nat) (s : MachineState) (I : List (BitVec 8)) : Prop where
  hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhandle_al : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hpaf_nf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78019da0#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhalt_hint : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035e44#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hhalt_empty : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035f14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u
  hfmt : ∀ (u : MachineState) (sp' d : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fa4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78019fa4#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        S.length = 3 → Region d S t → Run.HeapAt L' t → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G n (Cases.Zip2005.Top.GuestAccepts I) u

/-- `RunHyps` over the loaded image from `PanicPaths`: every other field is a theorem. -/
theorem RunHyps.of_panics {G : MachineState → Prop} {n : Nat} {I : List (BitVec 8)}
    (h : PanicPaths G n (start I) I) : RunHyps G n (start I) I where
  hpaf := h.hpaf
  hpp := h.hpp
  hprz := h.hprz
  hpb := h.hpb
  hpanic := h.hpanic
  hunwrap := h.hunwrap
  hhandle_rv := h.hhandle_rv
  hhandle_al := h.hhandle_al
  hunwrap_opt := h.hunwrap_opt
  hpaf_nf := h.hpaf_nf
  hhalt_hint := h.hhalt_hint
  hhalt_empty := h.hhalt_empty
  hfmt := h.hfmt
  hsq_alloc := by rw [start_code]; exact sq_alloc_ok
  hsq_realloc_g := by rw [start_code]; exact sq_realloc_g_ok
  hsq_alloci := by rw [start_code]; exact sq_alloc_inv_ok
  hsq_realloc := by rw [start_code]; exact sq_realloc_ok
  halloc := by rw [start_code]; exact halloc_ok
  halloc_mp := by rw [start_code]; exact halloc_mp_ok
  hrealloc_mp := by rw [start_code]; exact realloc_mp_ok
  hdealloc := by rw [start_code]; exact hdealloc_ok
  hdealloc_hint := by rw [start_code]; exact hdealloc_hint_ok
  hdealloc_nf := by rw [start_code]; exact hdealloc_nf_ok
  hdealloc_ivk := by rw [start_code]; exact hdealloc_ivk_ok
  hdealloc_cm := by rw [start_code]; exact hdealloc_cm_ok
  halloc_c := by rw [start_code]; exact halloc_c_ok
  halloc_fi := by rw [start_code]; exact halloc_fi_ok
  hrealloc_fi := by rw [start_code]; exact realloc_fi_ok
  halloc_nc := by rw [start_code]; exact halloc_nc_ok
  hrealloc_nc := by rw [start_code]; exact realloc_nc_ok
  hio := by
    rw [start_code]
    exact hio_ok fun u sp' L' h1 h2 => h.hhandle_al u sp' L' h1 (h2.trans (start_code I).symm)

/-- **The guest, from the ELF's entry over the loaded image**: a run on a private input that
    fits the hint area is `Safe (GuestAccepts I)`, assuming only that the panic and reject-halt
    paths never accept (`PanicPaths`). -/
theorem guest_run {G : MachineState → Prop} {n : Nat} (I : List (BitVec 8))
    (h : PanicPaths G n (start I) I) (hIfit : I.length + 1416 ≤ 0x400000000) :
    SafeN G n (Cases.Zip2005.Top.GuestAccepts I) (start I) :=
  guest_loaded_run I (RunHyps.of_panics h) (by omega) hIfit

end Cases.Zip2005
