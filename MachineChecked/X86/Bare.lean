/-
  MachineChecked.X86.Bare

  An x86-64 program without an operating system, as a Pancake program: the lift of linked
  programs (`Lprog/Lift.lean`), then lift 2 (`Logical/Lift.lean`) in the environment of a
  bare program (`Logical/Guest.lean`).

  A system call is `syscall` with its number in `rax`, its arguments in `rdi`, `rsi` and
  `rdx`, and its result in `rax`. The link register of the Lprog program is `ra`, which the
  lift keeps a return address in while a call or a return passes it.

  Nothing is proved of it. It is checked by running (`scripts/decompile-check`).

  ## Main definitions

  * `Guest`, `Guest.lift`, `Guest.toPancake`
-/

import MachineChecked.X86.Lprog.Lift
import MachineChecked.Lprog.Dead
import MachineChecked.Logical.Guest

namespace MachineChecked.X86

open MachineChecked.Lprog MachineChecked.X86.Lprog MachineChecked.Logical

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
  (liftX86 g.fns).map fun fd => { fd with body := dropDead [.cf, .zf, .sf, .ovf, .t0, .t1, .t2, .t3, .t4, .t5] fd.body }

/-- **The program as a Pancake program**, and the places where it may give up. -/
def toPancake : Except String (List (_root_.Flapjack.Decl Pancake.W) × List String) := do
  let some entry := g.fns.findIdx? (·.addr == g.entry) | throw "the entry of the ELF is no function of it"
  Logical.lift (Guest.bare g.memory "rax" "rdi" "rsi" "rdx" "rax") allRegs .ra .rsp entry g.lift

end Guest

end MachineChecked.X86
