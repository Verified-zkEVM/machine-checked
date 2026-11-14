/-
  MachineChecked.RiscV.Sp1.Pancake

  An SP1 guest as a Pancake program: lift 2 (`Logical/Lift.lean`) in the guest's execution
  environment.

  * **Memory.** The Pancake program reads and writes the guest's addresses as they are, so a
    pointer the guest shows the world is the pointer it showed before, and nothing is
    translated. The machine that runs the Pancake program must therefore give it a heap that
    covers the guest's address space, with Pancake's own stack and globals outside what the
    guest uses. `init` writes the words the ELF loads (`Guest.memory`), a few hundred to a
    function (`l_init0`, …); all other memory starts as zero, as SP1's does.
  * **`ecall`** is one FFI call, `@ecall(t0, a0, a1, a2)`: the system call number and its
    arguments. The environment does what SP1 does, to the same memory, and leaves the new
    values of `t0` and `a0` in two words at `scratch`, which the program reads back. After
    `HALT` (`t0 = 0`) the program ends.
  * **`wrong`** is the FFI call `@trap(0, 0, 0, 0)`, then a loop: the environment sees that
    the program gave up, and nothing follows.
  * The registers start as zero.

  Nothing is proved here. It is checked by running (`scripts/decompile-check`).

  ## Main definitions

  * `Guest`, `Guest.env`, `Guest.toPancake`
-/

import MachineChecked.Logical.Lift
import MachineChecked.RiscV.Lprog.Whole

namespace MachineChecked.RiscV.Sp1

open RiscvZkvm.Rv64 MachineChecked.Lprog MachineChecked.RiscV.Lprog MachineChecked.Logical
open MachineChecked.Logical.Lift (gvar num gset add seq when fn)

/-- A guest: its functions, where it starts, and the words it loads, each at an address
    that is a multiple of eight. -/
structure Guest where
  whole : Whole
  entry : Word
  memory : List (Word × Word)

/-- Where the environment leaves `t0` and `a0` after an `ecall`: below anything SP1 lets a
    guest use. -/
def scratch : Nat := 0x100

/-- The words one installing function writes. -/
def perInit : Nat := 256

private def reg (r : Reg) : String := RegText.name r

/-- Where the guest goes `wrong`. -/
def trap : _root_.Flapjack.Prog Pancake.W :=
  seq [.extCall "trap" (num 0) (num 0) (num 0) (num 0), .while (num 1) .skip]

namespace Guest

variable (g : Guest)

/-- The functions that write the guest's memory. -/
def inits : List (_root_.Flapjack.Decl Pancake.W) :=
  (Lift.runs perInit g.memory).zipIdx.map fun (ws, k) =>
    fn s!"l_init{k}" [] (seq ((ws.map fun (a, w) => .store (.const a) (.const w)) ++ [.return (num 0)]))

/-- **The environment of a guest, for lift 2.** -/
def env : Env where
  regs := [reg .x5, reg .x10, reg .x11, reg .x12]
  init := (List.range g.inits.length).map fun k => .call (some (none, none)) s!"l_init{k}" []
  decls := g.inits
  wrong := trap
  ext n stop :=
    if n = 0 then
      some (seq
        [.extCall "ecall" (gvar (reg .x5)) (gvar (reg .x10)) (gvar (reg .x11)) (gvar (reg .x12)),
         when (.cmp .equal (gvar (reg .x5)) (num 0)) [stop],
         gset (reg .x5) (.load .one (num scratch)),
         gset (reg .x10) (.load .one (num (scratch + 8)))])
    else none

/-- The guest as an Lprog program. -/
def lift : Lprog (Op Reg) Reg := g.whole.liftWhole

/-- **The guest as a Pancake program.** -/
def toPancake : Except String (List (_root_.Flapjack.Decl Pancake.W)) := do
  let some entry := g.whole.entryOf g.entry | throw "the entry of the ELF is no function of it"
  Logical.lift g.env allRegs .x1 .x2 entry g.lift

end Guest

end MachineChecked.RiscV.Sp1
