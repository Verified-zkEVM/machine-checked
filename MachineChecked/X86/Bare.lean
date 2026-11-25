/-
  MachineChecked.X86.Bare

  An x86-64 program without an operating system, as a Pancake program: the lift of linked
  programs (`Lift/Lift.lean`), then lift 2 (`Logical/Lift.lean`) in the environment of a
  bare program (`Logical/Guest.lean`).

  A system call is `syscall` with its number in `rax`, its arguments in `rdi`, `rsi` and
  `rdx`, and its result in `rax`. The link register of the Lprog program is `ra`, which the
  lift keeps a return address in while a call or a return passes it.

  Nothing is proved of it. It is checked by running (`scripts/decompile-check`).

  ## Main definitions

  * `Guest`, `Guest.lifted`, `Guest.lift`, `Guest.toPancake`
-/

import MachineChecked.X86.Lift.Lift
import Lprog.Dead
import MachineChecked.Logical.Guest

namespace MachineChecked.X86

open Lprog MachineChecked.X86.Lift MachineChecked.Logical Lprog.X86

/-- A program: its functions, where it starts, and the words it loads. -/
abbrev Guest := Logical.Guest.Program (Option Instr)

/-- The program as an Lprog program, as the lift writes it: every write of the flags. This is
    the one to prove a program against, since nothing is proved of the pass below. -/
def Guest.lifted (g : Guest) : Lprog.Lprog (Op Reg) Reg := liftX86 g.fns

/-- The program as an Lprog program, without the writes of flags that nothing reads. -/
def Guest.lift (g : Guest) : Lprog.Lprog (Op Reg) Reg :=
  g.lifted.map fun fd => { fd with body := dropDead [.cf, .zf, .sf, .ovf, .pf, .t0, .t1, .t2, .t3, .t4, .t5] fd.body }

/-- **The program as a Pancake program**, and the places where it may give up. -/
def Guest.toPancake (g : Guest) : Except String (List (_root_.Flapjack.Decl Pancake.W) × List String) :=
  Logical.Guest.Program.toPancake g (Guest.bare g.memory "rax" "rdi" "rsi" "rdx" "rax") allRegs .ra .rsp g.lift

end MachineChecked.X86
