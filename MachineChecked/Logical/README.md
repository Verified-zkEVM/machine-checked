# Logical

**Layer 1 of the [roadmap](../../ROADMAP.md): the structured logical program.** It is
Pancake, with Flapjack's syntax (`Flapjack.Pancake.PanLang`, a dependency), so that what is
decompiled to this layer can be compiled again.

| file | contents |
| --- | --- |
| `Pancake.lean` | Pancake programs as source text (`Pancake.print`). Flapjack has a parser and no printer. |
| `Ops.lean` | The shared operations of Lprog as Pancake statements. A register is a global variable. What Pancake lacks (shifts by a register, the high halves of a product, division) is a function written in Pancake. |
| `Structure.lean` | From a control-flow graph to structured control flow (`structure`), by Ramsey's method over the dominator tree: sequences, choices, blocks and loops. It works on the reducible graphs and says so of the others. It knows nothing of Pancake. |
| `Lift.lean` | **Lift 2** (`lift`): an Lprog program as a Pancake program. Each function is a Pancake function; a call is a call, checked as Lprog checks it; the body is `if` and `while` where the function's control flow has a structure, and a loop over its blocks otherwise. The execution environment is a parameter (`Env`): the installation, each external call, and what to do where the program goes `wrong`. |

**Where this stands.** Lift 2 takes whole programs: its users are a Flapjack image
([`../RiscV/Flapjack`](../RiscV/Flapjack/README.md)) and an SP1 guest
([`../RiscV/Sp1`](../RiscV/Sp1/README.md)). Nothing is proved of it; it is checked by running
([`scripts/decompile-check`](../../scripts/decompile-check/README.md)).

What it recovers is functions and control flow. Registers stay registers (global
variables), the stack stays memory, and nothing has a type. A function whose control flow is
not reducible, or that is too long or too deeply nested for Flapjack to compile in
reasonable time, is a loop over its blocks; `decompile` says how many are.

What is meant to be here is more: registers as variables, stack frames as locals, each pass
with a proof
([`docs/design/Decompiler.md`](../../docs/design/Decompiler.md), phases 4 and 5), and the
program logics over the result ([`docs/LogicalMachine.md`](../../docs/LogicalMachine.md)).
Contributions are welcome: open an issue first to agree on the key definitions (see
[`CONTRIBUTING.md`](../../CONTRIBUTING.md), "Larger contributions").
