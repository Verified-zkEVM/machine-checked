/-
  Cases.Zip2005.Runtime.SysPanic

  The end of every panic (phase D5): `sys_panic(msg, len)` (`0x7801bf7c`) writes the message
  to stderr through `sys_write` (a tail call to `syscall_write`) and calls
  `syscall_halt(1)`. Both are hand-proved against the hasher-owning `Env`
  (`SysWrite.holds`, `Halt.holds`), so the checker certifies `sys_write` and `sys_panic`
  against a small table of them under the same `Env`. `sys_panic`'s interface does not
  return (`returns := false`): from its precondition the run never accepts.
-/

import Cases.Zip2005.Runtime.Halt
import Cases.Zip2005.Runtime.SysWrite
import MachineChecked.RiscV.Check.Fast
import MachineChecked.RiscV.Check.Image
import Cases.Zip2005.Image.F_7801bf7c
import Cases.Zip2005.Image.F_7801bfa4
import Cases.Zip2005.Owned

set_option maxRecDepth 200000

namespace Cases.Zip2005.Runtime.SysPanic

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Frame MachineChecked.RiscV.Check

noncomputable abbrev C : Word → Option Instr := Image.Layout.image.codeAt

def writeIface : Iface :=
  { entry := 0x7801bfa4#64, depth := SysWrite.iface.depth, foot := SysWrite.iface.foot }

def iface : Iface :=
  { entry := 0x7801bf7c#64, depth := 0x10 + Halt.iface.depth, foot := SysWrite.iface.foot,
    returns := false }

def writeFn : Fn := { base := Image.F_7801bfa4.base, prog := Image.F_7801bfa4.prog, frags := [] }
def fn : Fn := { base := Image.F_7801bf7c.base, prog := Image.F_7801bf7c.prog, frags := [] }

def tbl : List Iface := [SysWrite.iface, Halt.iface, writeIface]

noncomputable abbrev wctx : Ctx := { env := Owned.env, tbl, σ := writeIface, f := writeFn }
noncomputable abbrev ctx : Ctx := { env := Owned.env, tbl, σ := iface, f := fn }

noncomputable def wanno : Array (List AState) := wctx.fill1 [(0, .ofDiff [] [])]
noncomputable def anno : Array (List AState) := ctx.fill1 [(0, .ofDiff [] [])]

theorem wvalid : wctx.valid wanno = true := Ctx.validFast_sound (by decide +kernel)
theorem valid : ctx.valid anno = true := Ctx.validFast_sound (by decide +kernel)

theorem wcode : CodeAt writeFn C :=
  codeAt_of_image (k := 40) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [writeFn] at h)

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 39) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn] at h)

/-- The table: `syscall_write`, `syscall_halt` (by hand) and `sys_write` (checked). -/
theorem tbl_holds : ∀ g ∈ tbl, g.Holds Owned.env C := by
  apply table_sound
  intro g hg n h
  simp only [tbl, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact SysWrite.holds n
  · exact Halt.holds n
  · exact Ctx.sound (c := wctx) wvalid wcode (by decide) Owned.env_wf Owned.env_ok h

/-- **`sys_panic`** never returns: it writes the message to stderr and halts with code 1,
    which never accepts. -/
theorem holds : iface.Holds Owned.env C := fun n =>
  Ctx.sound (c := ctx) valid code (by decide) Owned.env_wf Owned.env_ok fun g hg m _ => tbl_holds g hg m

end Cases.Zip2005.Runtime.SysPanic
