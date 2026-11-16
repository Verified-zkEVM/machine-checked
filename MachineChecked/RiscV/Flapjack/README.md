# RiscV/Flapjack

**A RISC-V binary from [Flapjack](https://github.com/pirapira/flapjack), the Pancake
compiler**: the first input of the decompiler
([`docs/design/Decompiler.md`](../../../docs/design/Decompiler.md)), since what it decompiles
to can be compiled by the compiler it came from.

| file | contents |
| --- | --- |
| `Image.lean` | `Image`: the code, the bitmaps and the FFI names. The layout it is installed in (CakeML's convention, fixed as flapjack-flip's machine fixes it): where the code, heap and stack are, the registers at entry, and the entries of the environment (halt, then the FFI functions) below the code. `Image.lift` is the image as an Lprog program, by the lift of code without functions (`../Lprog/Flat.lean`). |
| `Pancake.lean` | `Image.env`, the image's environment for lift 2 (`../../Logical/Lift.lean`), and `Image.toPancake`. The Pancake program is itself installed as an image, so the environment puts the old image back inside the new one: its heap and stack in the two halves of the new heap, its bitmaps and heap header in place, and the FFI functions as Pancake's FFI calls. |

Nothing is proved here yet. The meaning of an image as an execution context
(`Lprog.Context`) is not defined either: the RISC-V instance of Lprog reads memory behind
SP1's check, which this layout does not pass. Both are the inverse theorem's part of the
plan (phase 4).

The tool is `lake exe decompile --to pancake IMAGE.fjimg` ([`Tools/`](../../../Tools/README.md)).
It is checked by recompiling and running:
[`scripts/decompile-check`](../../../scripts/decompile-check/README.md).

Limits, as built: the image gets half the heap and half the stack it had (less 4 KiB), so a
program that needs more of either does not behave the same; and the recompiled binary takes
about twelve times the steps.
