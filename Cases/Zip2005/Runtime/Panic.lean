/-
  Cases.Zip2005.Runtime.Panic

  Panics never accept (phase D5), on the entry chain, given one phase-E premise.

  Every panic entry the program reaches -- `core::panicking::panic_fmt` (`0x7803de40`) and
  the three that tail into it: `panic` (`0x7803de20`), `panic_nounwind` (`0x7803dcdc`) and
  `assert_failed` (`0x7803dd28`) -- stores its arguments into its own frame and calls down
  the chain `panic_fmt` -> `rust_begin_unwind` -> two panic-handler closures ->
  `panic_with_hook`. Each of those frames is checked here (`Ctx.sound`): they write only
  their frames and every path ends in a never-returning call, so each has `returns := false`
  and never accepts.

  The chain bottoms out at `panic_with_hook` (`0x7803b8d0`), which runs the (default) hook --
  formatting the message into a heap `String` through `core::fmt::write` -- and then
  `rust_panic` -> `__rust_start_panic` -> `sys_panic` -> `syscall_halt(1)`. That formatting
  path writes a heap buffer through pointers the checker's footprints cannot describe, so it
  is the one premise left to phase E: `pwhIface.Holds`, that `panic_with_hook` never accepts
  from its entry. It is stated as an ordinary interface with `returns := false` (so its empty
  footprint is honest: the unsatisfiable postcondition means no caller relies on what it
  writes) under the hasher-owning `Owned.env`, exactly the shape phase E will discharge. Its
  `depth` is a concrete over-approximation of `panic_with_hook`'s worst-case stack; phase E
  pins the exact value (and confirms it fits the stack available when a panic fires).

  `Runtime.SysPanic` already proves the tail from `sys_panic` down unconditionally; this file
  proves the top of the chain. The gap between them -- `panic_with_hook` and the formatting
  it drives -- is `pwhIface`, discharged in phase E.
-/

import AsmVerif.RiscV.Check.Fast
import AsmVerif.RiscV.Check.Image
import Cases.Zip2005.Owned
import Cases.Zip2005.Image.F_7803de40
import Cases.Zip2005.Image.F_7803b67c
import Cases.Zip2005.Image.F_7803c3e8
import Cases.Zip2005.Image.F_7803c400
import Cases.Zip2005.Image.F_7803de20
import Cases.Zip2005.Image.F_7803dcdc
import Cases.Zip2005.Image.F_7803dd28

set_option maxRecDepth 400000

namespace Cases.Zip2005.Runtime.Panic

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check Cases.Zip2005

noncomputable abbrev C : Word → Option Instr := Image.Layout.image.codeAt

/-- A concrete over-approximation of `panic_with_hook`'s worst-case stack (option 1 pins the
    exact value and confirms it fits). -/
def D : Nat := 0x1000

/-- The one premise phase E discharges: `panic_with_hook` (`0x7803b8d0`) never accepts from
    its entry. It never returns (`returns := false`), so its empty footprint is honest — the
    unsatisfiable postcondition means no caller relies on what it writes. `D` is its stack. -/
def pwhIface : Iface := { entry := 0x7803b8d0#64, depth := D, foot := [], returns := false }

def iface_c400 : Iface := { entry := 0x7803c400#64, depth := 0x30 + D, foot := [], returns := false }
def iface_c3e8 : Iface := { entry := 0x7803c3e8#64, depth := 0x40 + D, foot := [], returns := false }
def iface_b67c : Iface := { entry := 0x7803b67c#64, depth := 0x70 + D, foot := [], returns := false }
def iface_de40 : Iface := { entry := 0x7803de40#64, depth := 0xb0 + D, foot := [], returns := false }
def iface_de20 : Iface := { entry := 0x7803de20#64, depth := 0xc0 + D, foot := [], returns := false, vals := [(.x10, [0x00000000780012a8#64, 0x00000000780011b0#64, 0x0000000078001138#64, 0x00000000780014b8#64, 0x00000000780119f8#64, 0x0000000078011b20#64, 0x00000000780137d0#64, 0x00000000780138f8#64, 0x0000000078013920#64, 0x0000000078014330#64])] }
def iface_dcdc : Iface := { entry := 0x7803dcdc#64, depth := 0xf0 + D, foot := [], returns := false, vals := [(.x12, [0x00000000780119b0#64, 0x0000000078013678#64, 0x0000000078013648#64, 0x0000000078014318#64])] }
def iface_dd28 : Iface := { entry := 0x7803dd28#64, depth := 0x140 + D, foot := [], returns := false, vals := [(.x12, [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64]), (.x14, [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64])] }

/-- The table: the premise and the four checked entry-chain frames. -/
def tbl : List Iface := [pwhIface, iface_c400, iface_c3e8, iface_b67c, iface_de40, iface_de20, iface_dcdc, iface_dd28]

def fn_c400 : Fn := { base := Image.F_7803c400.base, prog := Image.F_7803c400.prog, frags := [] }
def fn_c3e8 : Fn := { base := Image.F_7803c3e8.base, prog := Image.F_7803c3e8.prog, frags := [] }
def fn_b67c : Fn := { base := Image.F_7803b67c.base, prog := Image.F_7803b67c.prog, frags := [] }
def fn_de40 : Fn := { base := Image.F_7803de40.base, prog := Image.F_7803de40.prog, frags := [] }

noncomputable abbrev ctx_c400 : Ctx := { env := Owned.env, tbl, σ := iface_c400, f := fn_c400 }
noncomputable abbrev ctx_c3e8 : Ctx := { env := Owned.env, tbl, σ := iface_c3e8, f := fn_c3e8 }
noncomputable abbrev ctx_b67c : Ctx := { env := Owned.env, tbl, σ := iface_b67c, f := fn_b67c }
noncomputable abbrev ctx_de40 : Ctx := { env := Owned.env, tbl, σ := iface_de40, f := fn_de40 }

noncomputable def anno_c400 : Array (List AState) := (ctx_c400).fill1 [
  (0, (.ofDiff [] [])),
  (21, (.ofDiff [(.x2, (.lin .x2 0xffffffffffffffd0#64)), (.x8, (.lin .x2 0x0000000000000000#64)), (.x11, .top), (.x12, .top), (.x13, .top)] [(0xfffffffffffffff0#64, (.lin .x8 0x0000000000000000#64)), (0xfffffffffffffff8#64, (.lin .x1 0x0000000000000000#64))]))]
noncomputable def anno_c3e8 : Array (List AState) := (ctx_c3e8).fill1 [(0, .ofDiff [] [])]
noncomputable def anno_b67c : Array (List AState) := (ctx_b67c).fill1 [(0, .ofDiff [] [])]
noncomputable def anno_de40 : Array (List AState) := (ctx_de40).fill1 [(0, .ofDiff [] [])]

theorem valid_c400 : (ctx_c400).valid (anno_c400) = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_c3e8 : (ctx_c3e8).valid (anno_c3e8) = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_b67c : (ctx_b67c).valid (anno_b67c) = true := Ctx.validFast_sound (by decide +kernel)
theorem valid_de40 : (ctx_de40).valid (anno_de40) = true := Ctx.validFast_sound (by decide +kernel)

theorem code_c400 : CodeAt fn_c400 C :=
  codeAt_of_image (k := 235) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_c400] at h)
theorem code_c3e8 : CodeAt fn_c3e8 C :=
  codeAt_of_image (k := 234) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_c3e8] at h)
theorem code_b67c : CodeAt fn_b67c C :=
  codeAt_of_image (k := 209) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_b67c] at h)
theorem code_de40 : CodeAt fn_de40 C :=
  codeAt_of_image (k := 279) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_de40] at h)

def fn_de20 : Fn := { base := Image.F_7803de20.base, prog := Image.F_7803de20.prog, frags := [] }
noncomputable abbrev ctx_de20 : Ctx := { env := Owned.env, tbl, σ := iface_de20, f := fn_de20 }
noncomputable def anno_de20 : Array (List AState) := ctx_de20.fill1 [
  (0, (.ofDiff [(.x10, (.oneOf [0x00000000780012a8#64, 0x00000000780011b0#64, 0x0000000078001138#64, 0x00000000780014b8#64, 0x00000000780119f8#64, 0x0000000078011b20#64, 0x00000000780137d0#64, 0x00000000780138f8#64, 0x0000000078013920#64, 0x0000000078014330#64]))] []))]
theorem valid_de20 : ctx_de20.valid anno_de20 = true := Ctx.validFast_sound (by decide +kernel)
theorem code_de20 : CodeAt fn_de20 C :=
  codeAt_of_image (k := 278) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_de20] at h)
def fn_dcdc : Fn := { base := Image.F_7803dcdc.base, prog := Image.F_7803dcdc.prog, frags := [] }
noncomputable abbrev ctx_dcdc : Ctx := { env := Owned.env, tbl, σ := iface_dcdc, f := fn_dcdc }
noncomputable def anno_dcdc : Array (List AState) := ctx_dcdc.fill1 [
  (0, (.ofDiff [(.x12, (.oneOf [0x00000000780119b0#64, 0x0000000078013678#64, 0x0000000078013648#64, 0x0000000078014318#64]))] []))]
theorem valid_dcdc : ctx_dcdc.valid anno_dcdc = true := Ctx.validFast_sound (by decide +kernel)
theorem code_dcdc : CodeAt fn_dcdc C :=
  codeAt_of_image (k := 276) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_dcdc] at h)
def fn_dd28 : Fn := { base := Image.F_7803dd28.base, prog := Image.F_7803dd28.prog, frags := [] }
noncomputable abbrev ctx_dd28 : Ctx := { env := Owned.env, tbl, σ := iface_dd28, f := fn_dd28 }
noncomputable def anno_dd28 : Array (List AState) := ctx_dd28.fill1 [
  (0, (.ofDiff [(.x12, (.oneOf [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64])), (.x14, (.oneOf [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64]))] [])),
  (36, (.ofDiff [(.x2, (.lin .x2 0xffffffffffffff70#64)), (.x8, (.lin .x2 0x0000000000000000#64)), (.x10, .top), (.x11, .top), (.x12, (.const 0x00000000780142f8#64)), (.x14, (.oneOf [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64]))] [(0xffffffffffffff88#64, (.oneOf [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64])), (0xffffffffffffff80#64, (.lin .x13 0x0000000000000000#64)), (0xffffffffffffff78#64, (.oneOf [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64])), (0xffffffffffffff70#64, (.lin .x11 0x0000000000000000#64)), (0xfffffffffffffff0#64, (.lin .x8 0x0000000000000000#64)), (0xfffffffffffffff8#64, (.lin .x1 0x0000000000000000#64))])),
  (58, (.ofDiff [(.x0, (.const 0x0000000000000000#64)), (.x2, (.lin .x2 0xffffffffffffff70#64)), (.x8, (.lin .x2 0x0000000000000000#64)), (.x10, (.oneOf [0x0000000078000685#64, 0x000000007800076b#64])), (.x11, (.oneOf [0x000000007803ea08#64, 0x000000007803ea18#64])), (.x12, .top), (.x13, (.oneOf [0x000000007803ea30#64, 0x000000007803ea08#64])), (.x14, .top), (.x15, .top)] [(0xffffffffffffffd8#64, (.const 0x000000007803ea08#64)), (0xffffffffffffffb8#64, (.const 0x000000007803ea18#64)), (0xffffffffffffffb0#64, (.lin .x2 0xffffffffffffff90#64)), (0xffffffffffffff88#64, (.oneOf [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64])), (0xffffffffffffff80#64, (.lin .x13 0x0000000000000000#64)), (0xffffffffffffff78#64, (.oneOf [0x0000000078000260#64, 0x0000000078013850#64, 0x0000000078013a28#64, 0x0000000078014010#64])), (0xffffffffffffff70#64, (.lin .x11 0x0000000000000000#64)), (0xfffffffffffffff0#64, (.lin .x8 0x0000000000000000#64)), (0xfffffffffffffff8#64, (.lin .x1 0x0000000000000000#64))]))]
theorem valid_dd28 : ctx_dd28.valid anno_dd28 = true := Ctx.validFast_sound (by decide +kernel)
theorem code_dd28 : CodeAt fn_dd28 C :=
  codeAt_of_image (k := 277) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn_dd28] at h)

/-- **The entry-chain table holds**, given the one phase-E premise: `panic_with_hook` never
    accepts from its entry. The four frames above it on the panic path (`panic_fmt`,
    `rust_begin_unwind`, and the two panic-handler closures) are checked; each ends in a
    never-returning call, so each never accepts. -/
theorem tbl_holds (hpwh : pwhIface.Holds Owned.env C) : ∀ g ∈ tbl, g.Holds Owned.env C := by
  apply table_sound
  intro g hg n h
  simp only [tbl, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hpwh n
  · exact Ctx.sound (c := ctx_c400) valid_c400 code_c400 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_c3e8) valid_c3e8 code_c3e8 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_b67c) valid_b67c code_b67c (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_de40) valid_de40 code_de40 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_de20) valid_de20 code_de20 (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_dcdc) valid_dcdc code_dcdc (by decide) Owned.env_wf Owned.env_ok h
  · exact Ctx.sound (c := ctx_dd28) valid_dd28 code_dd28 (by decide) Owned.env_wf Owned.env_ok h

/-- **D5 for `panic_fmt`**: given the phase-E premise, `core::panicking::panic_fmt`
    (`0x7803de40`) never accepts — no accepting halt is reachable from its entry under its
    precondition. -/
theorem panic_fmt_neverAccepts (hpwh : pwhIface.Holds Owned.env C)
    {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {s : MachineState}
    (hpc : s.pc = 0x7803de40#64) (hpre : Pre Owned.env C iface_de40 s) :
    Safe G False s :=
  (tbl_holds hpwh iface_de40 (by simp [tbl])).safe hG hpc hpre
    (fun t ht => absurd ht.1 (by decide))

/-- **D5 for the other panic entries**: `core::panicking::panic` (`0x7803de20`),
    `panic_nounwind` (`0x7803dcdc`) and `assert_failed` (`0x7803dd28`) each store their
    arguments and tail into `panic_fmt`; given the premise, none accepts. -/
theorem panic_neverAccepts (hpwh : pwhIface.Holds Owned.env C)
    {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {s : MachineState}
    (hpc : s.pc = 0x7803de20#64) (hpre : Pre Owned.env C iface_de20 s) : Safe G False s :=
  (tbl_holds hpwh iface_de20 (by simp [tbl])).safe hG hpc hpre (fun t ht => absurd ht.1 (by decide))

theorem panic_nounwind_neverAccepts (hpwh : pwhIface.Holds Owned.env C)
    {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {s : MachineState}
    (hpc : s.pc = 0x7803dcdc#64) (hpre : Pre Owned.env C iface_dcdc s) : Safe G False s :=
  (tbl_holds hpwh iface_dcdc (by simp [tbl])).safe hG hpc hpre (fun t ht => absurd ht.1 (by decide))

theorem assert_failed_neverAccepts (hpwh : pwhIface.Holds Owned.env C)
    {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {s : MachineState}
    (hpc : s.pc = 0x7803dd28#64) (hpre : Pre Owned.env C iface_dd28 s) : Safe G False s :=
  (tbl_holds hpwh iface_dd28 (by simp [tbl])).safe hG hpc hpre (fun t ht => absurd ht.1 (by decide))

end Cases.Zip2005.Runtime.Panic
