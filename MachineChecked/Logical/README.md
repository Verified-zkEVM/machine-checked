# Logical

Layer 1 of the [roadmap](../../ROADMAP.md): the structured logical program, and lift 2, which
produces it from Lprog. The language is Pancake, using Flapjack's syntax
(`Flapjack.Pancake.PanLang`, a dependency), so that decompiled output can be compiled again.

| file | contents |
| --- | --- |
| `Ops.lean` | Lprog's shared operations as Pancake statements. Registers are global variables. Operations Pancake lacks (shift by a register, high half of a product, division) are Pancake functions. |
| `Structure.lean` | Structured control flow from a control-flow graph (`structure`), using Ramsey's method over the dominator tree: sequences, choices, blocks and loops. Handles reducible graphs and reports the others. Independent of Pancake. |
| `Lift.lean` | **Lift 2** (`lift`): an Lprog program as a Pancake program. Each function becomes a Pancake function and each call a call, checked as Lprog checks it. Bodies use `if` and `while` where the control flow is structured, and a loop over basic blocks otherwise. The execution environment is a parameter (`Env`): installation, each external call, and what to do when the program goes `wrong`. |
| `Guest.lean` | Shared by whole-program environments: functions that write a program's memory at its own addresses, `l_trap`, system calls as FFI calls with results read back, and `bare`, the environment for a program without an operating system. |

Printing Pancake as source text (`Pancake.print`) and the conventions lift 2 writes with
(`Pancake.Env`) are in the package [`pancake`](../../pancake/README.md).

## Status

Lift 2 takes whole programs. Its users are Flapjack images
([`../RiscV/Flapjack`](../RiscV/Flapjack/README.md)), SP1 guests
([`../RiscV/Sp1`](../RiscV/Sp1/README.md)), and programs without an operating system for
AArch64 ([`../ARM/Bare.lean`](../ARM/README.md)) and x86-64
([`../X86/Bare.lean`](../X86/README.md)).

- **Nothing is proved.** The output is tested by recompiling and running
  ([`scripts/decompile-check`](../../scripts/decompile-check/README.md)).
- **Only functions and control flow are recovered.** Registers stay global variables, the
  stack stays memory, and nothing has a type.
- A function whose control flow is irreducible, or that is too long or too deeply nested for
  Flapjack to compile in reasonable time, becomes a loop over its blocks. `decompile` reports
  how many functions this affects.

## Not done

Registers as variables, stack frames as locals, a proof for each pass
([`docs/design/Decompiler.md`](../../docs/design/Decompiler.md), phases 4 and 5), and program
logics over the result ([`docs/LogicalMachine.md`](../../docs/LogicalMachine.md)). To
contribute, open an issue first to agree on the key definitions
([`CONTRIBUTING.md`](../../CONTRIBUTING.md)).
