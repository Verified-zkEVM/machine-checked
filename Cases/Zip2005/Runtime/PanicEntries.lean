/-
  Cases.Zip2005.Runtime.PanicEntries

  The rest of the panic and halt entries the program reaches never accept (milestone M1),
  given the two formatting premises.

  `Runtime.Panic` checks the four core entries (`panic_fmt`, `panic`, `panic_nounwind`,
  `assert_failed`) against `panic_with_hook`. The program's code also calls these wrappers,
  each of which builds its arguments in its own frame and tails into one of them:

  * `core::panicking::assert_failed::<u8, u8>` (`0x7803a110`) and the `orchard` instance
    (`0x78019da0`), into `assert_failed_inner` (`0x7803dd28`);
  * `panic_const_rem_by_zero` (`0x7803de78`), `result::unwrap_failed` (`0x7803dc7c`) and
    `raw_vec::capacity_overflow` (`0x7803cf38`), into `panic_fmt` (`0x7803de40`);
  * `option::unwrap_failed` (`0x7803f364`), into `panic` (`0x7803de20`);
  * `raw_vec::handle_error` (`0x7803cf14`), into `capacity_overflow` or
    `handle_alloc_error` (`0x7803d1a8`);
  * `sp1_lib::halt_invalid_hint` (`0x78035e44`), into `syscall_halt` with a nonzero code.

  `handle_alloc_error` calls `__rust_alloc_error_handler` (`0x7803aebc`). In this binary
  `__rust_alloc_error_handler_should_panic` returns 0, so that handler does not panic: it
  runs the default allocation-error hook, which prints through `core::fmt::write` to stderr,
  and aborts. That formatting path is the second premise (`oomIface`), stated like
  `panic_with_hook`'s: it never accepts from its entry.

  Each wrapper's interface pins the registers its callee needs to the constants its call
  sites pass (`vals`, from `infer-contracts`' traces); that is what makes the payloads the
  image's own (T5).
-/

import Cases.Zip2005.Runtime.Panic
import Cases.Zip2005.Runtime.Halt
import Cases.Zip2005.Image.F_7803a110
import Cases.Zip2005.Image.F_78019da0
import Cases.Zip2005.Image.F_7803de78
import Cases.Zip2005.Image.F_7803dc7c
import Cases.Zip2005.Image.F_7803f364
import Cases.Zip2005.Image.F_7803cf38
import Cases.Zip2005.Image.F_7803cf14
import Cases.Zip2005.Image.F_7803d1a8
import Cases.Zip2005.Image.F_78035e44

set_option maxRecDepth 400000

namespace Cases.Zip2005.Runtime.PanicEntries

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check Cases.Zip2005

noncomputable abbrev C : Word → Option Instr := Image.Layout.image.codeAt

/-- The formatting premises' stack bound, as for `panic_with_hook`. -/
abbrev D : Nat := Runtime.Panic.D

/-- The second formatting premise: `__rust_alloc_error_handler` (`0x7803aebc`) never accepts
    from its entry. It prints the failed allocation's size to stderr and aborts. `D` is a
    stack bound phase E pins, as for `panic_with_hook`. -/
def oomIface : Iface := { entry := 0x7803aebc#64, depth := D, foot := [], returns := false }

/-- A stack bound for each wrapper: its own frame and its callee's, over-approximated. -/
def W : Nat := 0x400 + D

def iface_a110 : Iface := { entry := 0x7803a110#64, depth := W, foot := [], returns := false, vals := [(.x15, [0x78001198#64, 0x780015d0#64, 0x780017f8#64, 0x780119c8#64, 0x78001950#64, 0x78011a70#64, 0x78011ab8#64, 0x78011bc8#64, 0x78011be8#64, 0x78013878#64])] }
def iface_19da0 : Iface := { entry := 0x78019da0#64, depth := W, foot := [], returns := false }
def iface_de78 : Iface := { entry := 0x7803de78#64, depth := W, foot := [], returns := false, vals := [(.x10, [0x78013660#64])] }
def iface_dc7c : Iface := { entry := 0x7803dc7c#64, depth := W, foot := [], returns := false, vals := [(.x10, [0x78011988#64, 0x78011a88#64, 0x78013728#64, 0x78014108#64]), (.x13, [0x78011968#64, 0x78011ad0#64, 0x78013708#64, 0x780140e8#64]), (.x14, [0x78011998#64, 0x78011af0#64, 0x78011b08#64, 0x78013758#64, 0x78013770#64, 0x78013788#64, 0x78014160#64])] }
def iface_f364 : Iface := { entry := 0x7803f364#64, depth := W, foot := [], returns := false, vals := [(.x10, [0x78001328#64, 0x78001310#64, 0x780012f8#64, 0x78001120#64, 0x78001108#64, 0x780010f0#64, 0x780010d8#64, 0x780010c0#64, 0x780010a8#64, 0x78001420#64, 0x78001478#64, 0x780119e0#64, 0x780136d8#64, 0x780136c0#64, 0x780136a8#64, 0x78013690#64])] }
def iface_cf38 : Iface := { entry := 0x7803cf38#64, depth := W, foot := [], returns := false }
def iface_d1a8 : Iface := { entry := 0x7803d1a8#64, depth := W, foot := [], returns := false }
def iface_cf14 : Iface := { entry := 0x7803cf14#64, depth := W + 0x100, foot := [], returns := false }
def iface_35e44 : Iface := { entry := 0x78035e44#64, depth := W, foot := [], returns := false }

/-- The table: the entry chain and its premise, `syscall_halt`, the second premise and the
    wrappers. -/
def tbl : List Iface :=
  Runtime.Panic.tbl ++ [Runtime.Halt.iface, oomIface, iface_a110, iface_19da0, iface_de78,
    iface_dc7c, iface_f364, iface_cf38, iface_d1a8, iface_cf14, iface_35e44]

def fn_a110 : Fn := { base := Image.F_7803a110.base, prog := Image.F_7803a110.prog, frags := [] }
def fn_19da0 : Fn := { base := Image.F_78019da0.base, prog := Image.F_78019da0.prog, frags := [] }
def fn_de78 : Fn := { base := Image.F_7803de78.base, prog := Image.F_7803de78.prog, frags := [] }
def fn_dc7c : Fn := { base := Image.F_7803dc7c.base, prog := Image.F_7803dc7c.prog, frags := [] }
def fn_f364 : Fn := { base := Image.F_7803f364.base, prog := Image.F_7803f364.prog, frags := [] }
def fn_cf38 : Fn := { base := Image.F_7803cf38.base, prog := Image.F_7803cf38.prog, frags := [] }
def fn_d1a8 : Fn := { base := Image.F_7803d1a8.base, prog := Image.F_7803d1a8.prog, frags := [] }
def fn_cf14 : Fn := { base := Image.F_7803cf14.base, prog := Image.F_7803cf14.prog, frags := [] }
def fn_35e44 : Fn := { base := Image.F_78035e44.base, prog := Image.F_78035e44.prog, frags := [] }

noncomputable abbrev ctx_a110 : Ctx := { env := Owned.env, tbl, σ := iface_a110, f := fn_a110 }
noncomputable abbrev ctx_19da0 : Ctx := { env := Owned.env, tbl, σ := iface_19da0, f := fn_19da0 }
noncomputable abbrev ctx_de78 : Ctx := { env := Owned.env, tbl, σ := iface_de78, f := fn_de78 }
noncomputable abbrev ctx_dc7c : Ctx := { env := Owned.env, tbl, σ := iface_dc7c, f := fn_dc7c }
noncomputable abbrev ctx_f364 : Ctx := { env := Owned.env, tbl, σ := iface_f364, f := fn_f364 }
noncomputable abbrev ctx_cf38 : Ctx := { env := Owned.env, tbl, σ := iface_cf38, f := fn_cf38 }
noncomputable abbrev ctx_d1a8 : Ctx := { env := Owned.env, tbl, σ := iface_d1a8, f := fn_d1a8 }
noncomputable abbrev ctx_cf14 : Ctx := { env := Owned.env, tbl, σ := iface_cf14, f := fn_cf14 }
noncomputable abbrev ctx_35e44 : Ctx := { env := Owned.env, tbl, σ := iface_35e44, f := fn_35e44 }

noncomputable def anno_a110 : Array (List AState) := ctx_a110.fill1 [
  (0, .ofDiff [(.x15, .oneOf [0x78001198#64, 0x780015d0#64, 0x780017f8#64, 0x780119c8#64,
    0x78001950#64, 0x78011a70#64, 0x78011ab8#64, 0x78011bc8#64, 0x78011be8#64, 0x78013878#64])] [])]
noncomputable def anno_19da0 : Array (List AState) := ctx_19da0.fill1 [(0, .ofDiff [] [])]
noncomputable def anno_de78 : Array (List AState) := ctx_de78.fill1 [
  (0, .ofDiff [(.x10, .oneOf [0x78013660#64])] [])]
noncomputable def anno_dc7c : Array (List AState) := ctx_dc7c.fill1 [
  (0, .ofDiff [(.x10, .oneOf [0x78011988#64, 0x78011a88#64, 0x78013728#64, 0x78014108#64]),
    (.x13, .oneOf [0x78011968#64, 0x78011ad0#64, 0x78013708#64, 0x780140e8#64]),
    (.x14, .oneOf [0x78011998#64, 0x78011af0#64, 0x78011b08#64, 0x78013758#64, 0x78013770#64,
      0x78013788#64, 0x78014160#64])] [])]
noncomputable def anno_f364 : Array (List AState) := ctx_f364.fill1 [
  (0, .ofDiff [(.x10, .oneOf [0x78001328#64, 0x78001310#64, 0x780012f8#64, 0x78001120#64,
    0x78001108#64, 0x780010f0#64, 0x780010d8#64, 0x780010c0#64, 0x780010a8#64, 0x78001420#64,
    0x78001478#64, 0x780119e0#64, 0x780136d8#64, 0x780136c0#64, 0x780136a8#64,
    0x78013690#64])] [])]
noncomputable def anno_cf38 : Array (List AState) := ctx_cf38.fill1 [(0, .ofDiff [] [])]
noncomputable def anno_d1a8 : Array (List AState) := ctx_d1a8.fill1 [(0, .ofDiff [] [])]
noncomputable def anno_cf14 : Array (List AState) := ctx_cf14.fill1 [
  (0, .ofDiff [] []),
  -- the join after `capacity_overflow`'s call: the frame set up, its two slots saved
  (7, .ofDiff [(.x2, .lin .x2 0xfffffffffffffff0#64), (.x8, .lin .x2 0#64)]
    [(0xfffffffffffffff0#64, .lin .x8 0#64), (0xfffffffffffffff8#64, .lin .x1 0#64)])]
noncomputable def anno_35e44 : Array (List AState) := ctx_35e44.fill1 [(0, .ofDiff [] [])]

theorem valid_a110 : ctx_a110.valid anno_a110 = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_19da0 : ctx_19da0.valid anno_19da0 = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_de78 : ctx_de78.valid anno_de78 = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_dc7c : ctx_dc7c.valid anno_dc7c = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_f364 : ctx_f364.valid anno_f364 = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_cf38 : ctx_cf38.valid anno_cf38 = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_d1a8 : ctx_d1a8.valid anno_d1a8 = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_cf14 : ctx_cf14.valid anno_cf14 = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_35e44 : ctx_35e44.valid anno_35e44 = true := Ctx.validFast_sound (by decide +kernel)

theorem code_a110 : CodeAt fn_a110 C :=
  codeAt_of_image (k := 169) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_a110] at h)
theorem code_19da0 : CodeAt fn_19da0 C :=
  codeAt_of_image (k := 11) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_19da0] at h)
theorem code_de78 : CodeAt fn_de78 C :=
  codeAt_of_image (k := 280) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_de78] at h)
theorem code_dc7c : CodeAt fn_dc7c C :=
  codeAt_of_image (k := 275) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_dc7c] at h)
theorem code_f364 : CodeAt fn_f364 C :=
  codeAt_of_image (k := 301) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_f364] at h)
theorem code_cf38 : CodeAt fn_cf38 C :=
  codeAt_of_image (k := 254) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_cf38] at h)
theorem code_d1a8 : CodeAt fn_d1a8 C :=
  codeAt_of_image (k := 260) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_d1a8] at h)
theorem code_cf14 : CodeAt fn_cf14 C :=
  codeAt_of_image (k := 253) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_cf14] at h)
theorem code_35e44 : CodeAt fn_35e44 C :=
  codeAt_of_image (k := 157) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_35e44] at h)

/-- **The panic and halt entries hold**, given the two formatting premises: `panic_with_hook`
    and the allocation-error handler never accept from their entries. -/
theorem tbl_holds (hpwh : Runtime.Panic.pwhIface.Holds Owned.env C) (hoom : oomIface.Holds Owned.env C) :
    ∀ g ∈ tbl, g.Holds Owned.env C := by
  apply table_sound
  intro g hg n h
  rcases List.mem_append.mp hg with hg | hg
  · exact Runtime.Panic.tbl_holds hpwh g hg n
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Runtime.Halt.holds n
  · exact hoom n
  · exact Ctx.sound (c := ctx_a110) valid_a110 code_a110 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_19da0) valid_19da0 code_19da0 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_de78) valid_de78 code_de78 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_dc7c) valid_dc7c code_dc7c (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_f364) valid_f364 code_f364 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_cf38) valid_cf38 code_cf38 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_d1a8) valid_d1a8 code_d1a8 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_cf14) valid_cf14 code_cf14 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_35e44) valid_35e44 code_35e44 (by decide) Owned.env_wf Owned.env_ok h

end Cases.Zip2005.Runtime.PanicEntries
