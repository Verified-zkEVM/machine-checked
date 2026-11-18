# RiscV/Flapjack

RISC-V binaries produced by [Flapjack](https://github.com/pirapira/flapjack), the Pancake
compiler. These are the decompiler's first input
([`docs/design/Decompiler.md`](../../../docs/design/Decompiler.md)): the Pancake it produces
can be recompiled by the same compiler.

| file | contents |
| --- | --- |
| `Image.lean` | `Image`: the code, the bitmaps and the FFI names, and the layout the image is installed in (CakeML's convention, as flapjack-flip's machine fixes it): where code, heap and stack are, the registers at entry, and the environment's entries (halt, then the FFI functions) below the code. `Image.lift` is the image as an Lprog program, via the lift of code without functions (`../Lift/Flat.lean`). |
| `Pancake.lean` | `Image.env`, the image's environment for lift 2 (`../../Logical/Lift.lean`), and `Image.toPancake`. The Pancake program is itself installed as an image, so the environment places the old image inside the new one: its heap and stack in the two halves of the new heap, its bitmaps and heap header in place, and its FFI functions as Pancake FFI calls. |

The tool is `lake exe decompile --to pancake IMAGE.fjimg` ([`Tools/`](../../../Tools/README.md)).
It is tested by recompiling and running
([`scripts/decompile-check`](../../../scripts/decompile-check/README.md)).

## Status and limits

- Nothing is proved here.
- The meaning of an image as an execution context (`Lprog.Context`) is not defined: the
  RISC-V instance of Lprog reads memory behind SP1's check, which this layout does not pass.
  Both are part of phase 4 of the decompiler plan (the inverse theorem).
- The recompiled image gets half the heap and half the stack the original had (less 4 KiB),
  so a program that needs more of either behaves differently.
- The recompiled binary takes about twelve times as many steps.
