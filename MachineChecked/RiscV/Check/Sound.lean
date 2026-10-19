/-
  MachineChecked.RiscV.Check.Sound

  The checker is sound: if `Ctx.valid` accepts a function's annotation, and every callee
  in the table meets its interface for smaller budgets, the function meets its own
  (`Ctx.sound`); a table every member of which is so checked meets its interfaces
  (`table_sound`). The proof is in parts:

  - `Sound.Core`: the facts of an activation, the invariant a state describes;
  - `Sound.Kn`: the known writers and their fields;
  - `Sound.Plain`: the straight-line instructions;
  - `Sound.Call`: calls, tail calls and returns;
  - `Sound.Act`: the activation, by induction on the budget.
-/

import MachineChecked.RiscV.Check.Sound.Core
import MachineChecked.RiscV.Check.Sound.Kn
import MachineChecked.RiscV.Check.Sound.Plain
import MachineChecked.RiscV.Check.Sound.Call
import MachineChecked.RiscV.Check.Sound.Act
