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

/-- A program: its functions, where it starts, and the words it loads. -/
abbrev Guest := Logical.Guest.Program (Option Arm64.Instr)

/-- The program as an Lprog program, without the writes of flags that nothing reads. -/
def Guest.lift (g : Guest) : Lprog.Lprog (Op Reg) Reg :=
  (liftArm g.fns).map fun fd => { fd with body := dropDead [.nf, .zf, .cf, .vf, .t0, .t1, .t2] fd.body }

/-- **The program as a Pancake program**, and the places where it may give up. -/
def Guest.toPancake (g : Guest) : Except String (List (_root_.Flapjack.Decl Pancake.W) × List String) :=
  Logical.Guest.Program.toPancake g (Guest.bare g.memory "x8" "x0" "x1" "x2" "x0") allRegs .x30 .sp g.lift

end MachineChecked.ARM
