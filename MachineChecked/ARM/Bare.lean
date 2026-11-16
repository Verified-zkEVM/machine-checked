/-
  MachineChecked.ARM.Bare

  An AArch64 program without an operating system as a Pancake program: the lift of AArch64
  (`Lprog/Lift.lean`), then lift 2 in the environment of a bare program
  (`Logical/Guest.lean`).

  A system call is `svc #0`, with the number in `x8`, the arguments in `x0`, `x1` and `x2`,
  and the result in `x0`. The program starts at its entry with every register zero.

  Nothing is proved here. It is checked by running (`scripts/decompile-check`).

  ## Main definitions

  * `Guest`, `Guest.toPancake`
-/

import MachineChecked.ARM.Lprog.Lift
import MachineChecked.Lprog.Dead
import MachineChecked.Logical.Guest

namespace MachineChecked.ARM

open MachineChecked.Lprog MachineChecked.ARM.Lprog MachineChecked.Logical

/-- A program: its functions, where it starts, and the words it loads, each at an address
    that is a multiple of eight. -/
structure Guest where
  fns : List Fun
  entry : BitVec 64
  memory : List (BitVec 64 × BitVec 64)

namespace Guest

variable (g : Guest)

/-- The program as an Lprog program, without the writes of flags that nothing reads. -/
def lift : Lprog.Lprog (Op Reg) Reg :=
  (liftArm g.fns).map fun fd => { fd with body := dropDead [.nf, .zf, .cf, .vf, .t0, .t1, .t2] fd.body }

/-- **The program as a Pancake program**, and the places where it may give up. -/
def toPancake : Except String (List (_root_.Flapjack.Decl Pancake.W) × List String) := do
  let some entry := g.fns.findIdx? (·.addr == g.entry) | throw "the entry of the ELF is no function of it"
  Logical.lift (Guest.bare g.memory "x8" "x0" "x1" "x2" "x0") allRegs .x30 .sp entry g.lift

end Guest

end MachineChecked.ARM
