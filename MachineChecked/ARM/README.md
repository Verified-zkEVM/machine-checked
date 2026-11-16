# ARM

**AArch64, at layers 0 and 0.5 of the [roadmap](../../ROADMAP.md):** the machine model, and a
lift into the low logical program for the decompiler. The counterpart of `RiscV/`, with less
built and nothing proved.

## Today

| file | contents |
| --- | --- |
| `Arm64.lean` | Imports the AArch64 semantics: the trusted package `arm64` of DeepMind's [arm64-semantics](https://github.com/google-deepmind/code-verification/tree/main/arm64-semantics) (`Arm64.Trusted`), a dependency used unmodified at the commit pinned in `lakefile.toml`. Its `Arm64.Step` fetches four bytes, decodes and executes them, over Linux user-mode state. **Trusted** (`docs/ISA.md`). |
| `Lprog/Reg.lean` | The registers of AArch64 at Lprog: the general registers, the stack pointer, the four flags as registers that hold 0 or 1, and three of the lift's own. |
| `Lprog/Lift.lean` | The lift of AArch64 (`liftArm`): arm64-semantics' decoded instructions, the integer ones, in the lift of linked programs (`../Lprog/Linked.lean`) over the shared operations. Nothing is proved of it. |
| `Lprog/Table.lean` | The instructions by kind, each with whether the lift takes it, said by the lift itself: the table of `LIMITS.md`. |
| `Bare.lean` | An AArch64 program without an operating system as a Pancake program (`Guest.toPancake`): the lift, then lift 2 (`../Logical`), with `svc` as the system call. What `decompile --to pancake` runs on an AArch64 ELF. |
| [`LIMITS.md`](LIMITS.md) | **What the decompiler does not do on AArch64**: what it takes, every instruction lifted or not, where it gives up, what it assumes, where its output differs from the processor, how far it is tested. |

Nothing here states a judgement over `Arm64.Step` yet, and the lift is not proved against
it: it is tested against another machine (`scripts/decompile-check`).

## Where it is going

AArch64 is meant to be a peer of RISC-V, with the same layers:
- the image loader and the context (layer -1): arm64-semantics' loader and Linux system
  calls, a context other than a zkVM;
- the judgement over `Arm64.Step` (layer 0);
- the simulation that carries a run of the lifted program down to `Arm64.Step`: the
  counterpart of `../RiscV/Lprog`'s, for the lift that is here;
- the proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).
