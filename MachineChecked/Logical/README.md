# Logical

**Layer 1 of the [roadmap](../../ROADMAP.md): the structured logical program.** It is
Pancake, with Flapjack's syntax (`Flapjack.Pancake.PanLang`, a dependency), so that what is
decompiled to this layer can be compiled again.

| file | contents |
| --- | --- |
| `Pancake.lean` | Pancake programs as source text (`Pancake.print`). Flapjack has a parser and no printer. |
| `Lift.lean` | **Lift 2, baseline** (`lift`): an Lprog program over the shared operations as a Pancake program. The registers are globals; the blocks of the program are dealt out to small functions, each a loop, with a counter that names the block to run next. What Pancake lacks (shifts by a register, the high halves of a product, division) is a function written in Pancake. The execution environment is a parameter (`Env`): the installation, and each external call. |

**Where this stands.** The baseline recovers no structure: registers stay registers, memory
stays flat, and control flow is the loop. Nothing is proved of it; it is checked by running
([`scripts/decompile-check`](../../scripts/decompile-check/README.md)). It lifts a program of
one function: calls and returns are not lifted yet, so its only user is a Flapjack image
([`../RiscV/Flapjack`](../RiscV/Flapjack/README.md)).

What is meant to be here is more: registers as variables, stack frames as locals, loops and
conditionals rebuilt from the control-flow graph, pass by pass, each with a proof
([`docs/design/Decompiler.md`](../../docs/design/Decompiler.md), phases 4 and 5), and the
program logics over the result ([`docs/LogicalMachine.md`](../../docs/LogicalMachine.md)).
Contributions are welcome: open an issue first to agree on the key definitions (see
[`CONTRIBUTING.md`](../../CONTRIBUTING.md), "Larger contributions").
