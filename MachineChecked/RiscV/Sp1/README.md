# RiscV/Sp1

**An SP1 guest as a Pancake program**: the second input of the decompiler
([`docs/design/Decompiler.md`](../../../docs/design/Decompiler.md)), a RISC-V ELF that rustc
built for SP1.

| file | contents |
| --- | --- |
| `Pancake.lean` | `Guest`: the functions of an ELF, its entry and the words it loads. `Guest.env`, its environment for lift 2 ([`../../Logical/Lift.lean`](../../Logical/Lift.lean)), and `Guest.toPancake`. The Pancake program uses the guest's own addresses, so nothing is translated; `ecall` is the FFI call `@ecall(t0, a0, a1, a2)`, whose results the environment leaves in memory; where the guest goes `wrong`, the program says so through `@trap(n, 0, 0, 0)` and stops. |

The guest reaches Lprog by the lift of whole programs
([`../Lprog/Whole.lean`](../Lprog/Whole.lean)).

Nothing is proved here yet. The tool is `lake exe decompile --to pancake GUEST.elf`
([`Tools/`](../../../Tools/README.md)). It is checked by recompiling and running:
[`scripts/decompile-check`](../../../scripts/decompile-check/README.md).

What the recompiled program needs of the machine that runs it: a heap that covers the
guest's address space (SP1 lets a guest use addresses up to 2^37), with Pancake's own stack
and code outside it, and an FFI function `ecall` that does SP1's system calls on that
memory. `scripts/decompile-check/sp1run.py` is such a machine.
