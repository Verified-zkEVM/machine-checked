/-
  MachineChecked.RiscV.Sp1.Pancake

  An SP1 guest as a Pancake program: lift 2 (`Logical/Lift.lean`) in the guest's execution
  environment, which is that of a whole program (`Logical/Guest.lean`: its memory at its own
  addresses, `l_trap` where it goes `wrong`) with SP1's `ecall`:

  * **`ecall`** is one FFI call, `@ecall(t0, a0, a1, a2)`: the system call number and its
    arguments. The environment does what SP1 does, to the same memory, and leaves the new
    values of `t0` and `a0` for the program to read back. After `HALT` (`t0 = 0`) the
    program ends.
  * The registers start as zero.

  Nothing is proved here. It is checked by running (`scripts/decompile-check`).

  ## Main definitions

  * `Guest`, `Guest.env`, `Guest.toPancake`
-/

import MachineChecked.Logical.Guest
import MachineChecked.RiscV.Lift.Whole

namespace MachineChecked.RiscV.Sp1

open Lprog.RiscV Lprog.RiscV.Machine

open RiscvZkvm.Rv64 Lprog MachineChecked.RiscV.Lift MachineChecked.Logical

/-- A guest: its functions, where it starts, and the words it loads. -/
abbrev Guest := Logical.Guest.Program Decoded

private def reg (r : Reg) : String := RegText.name r

/-- **The environment of a guest, for lift 2.** -/
def Guest.env (g : Guest) : Env where
  regs := [reg .x5, reg .x10, reg .x11, reg .x12]
  init := Guest.install g.memory
  decls := Guest.trapFn :: Guest.inits g.memory
  wrong := Guest.trap
  ext n stop :=
    if n = 0 then
      some (Guest.syscall _root_.Pancake.ecall (reg .x5) (reg .x10) (reg .x11) (reg .x12) [reg .x5, reg .x10] stop)
    else none

/-- The guest as an Lprog program. -/
def Guest.lift (g : Guest) : Lprog (Op Reg) Reg := liftWhole g.fns

/-- **The guest as a Pancake program.** -/
def Guest.toPancake (g : Guest) : Except String (List (_root_.Flapjack.Decl Pancake.W) × List String) :=
  Logical.Guest.Program.toPancake g g.env Lprog.RiscV.Machine.allRegs .x1 .x2 g.lift

end MachineChecked.RiscV.Sp1
