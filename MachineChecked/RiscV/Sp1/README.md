# RiscV/Sp1

An SP1 guest as a Pancake program. This is the decompiler's second input
([`docs/design/Decompiler.md`](../../../docs/design/Decompiler.md)): a RISC-V ELF built by
rustc for SP1.

| file | contents |
| --- | --- |
| `Pancake.lean` | `Guest`: an ELF's functions, its entry and the words it loads. `Guest.env` is its environment for lift 2 ([`../../Logical/Lift.lean`](../../Logical/Lift.lean)), and `Guest.toPancake` the translation. The Pancake program uses the guest's own addresses, so nothing is relocated. `ecall` becomes the FFI call `@ecall(t0, a0, a1, a2)`, which leaves its results in memory. Where the guest goes `wrong`, the program calls `@trap(n, 0, 0, 0)` and stops. |

The guest is lifted to Lprog by the lift of whole programs
([`../Lift/Whole.lean`](../Lift/Whole.lean)).

The tool is `lake exe decompile --to pancake GUEST.elf` ([`Tools/`](../../../Tools/README.md)).
Nothing is proved here; it is tested by recompiling and running
([`scripts/decompile-check`](../../../scripts/decompile-check/README.md)).

The recompiled program needs a machine with a heap covering the guest's address space (SP1
lets a guest use addresses up to 2^37), with Pancake's own stack and code outside it, and an
FFI function `ecall` that performs SP1's system calls on that memory.
`scripts/decompile-check/sp1run.py` is such a machine.
