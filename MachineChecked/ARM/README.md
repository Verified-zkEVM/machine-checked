# ARM

AArch64 at layers 0 and 0.5 of the [roadmap](../../ROADMAP.md): the machine model, and a lift
into Lprog used by the decompiler. This is the counterpart of [`../RiscV`](../RiscV/README.md),
with less built and nothing proved.

| file | contents |
| --- | --- |
| `Arm64.lean` | Imports the AArch64 semantics: the trusted package `arm64` of DeepMind's [arm64-semantics](https://github.com/google-deepmind/code-verification/tree/main/arm64-semantics) (`Arm64.Trusted`), used unmodified at the commit pinned in `lakefile.toml`. `Arm64.Step` fetches, decodes and executes one instruction over Linux user-mode state. **Trusted** ([`docs/ISA.md`](../../docs/ISA.md)). |
| `Lift/Lift.lean` | The AArch64 lift (`liftArm`): arm64-semantics' decoded integer instructions, lifted with the shared lift of linked programs (`Lprog/Linked.lean` in [`lprog`](../../lprog/README.md)). Not proved. |
| `Lift/Table.lean` | Each kind of instruction and whether the lift takes it, computed from the lift. Generates the table in `LIMITS.md`. |
| `Bare.lean` | An AArch64 program without an operating system as a Pancake program (`Guest.toPancake`): this lift, then lift 2 ([`../Logical`](../Logical/README.md)), with `svc` as the system call. Used by `decompile --to pancake` on an AArch64 ELF. |
| [`LIMITS.md`](LIMITS.md) | What the decompiler accepts on AArch64, every instruction and whether it is lifted, where it gives up, what it assumes, how its output differs from the processor, and how far it is tested. |

The AArch64 registers at Lprog are in the `lprog` package: `lprog/Lprog/ARM/Reg.lean`
(namespace `Lprog.ARM`).

## Status

No judgement over `Arm64.Step` is stated yet, and the lift is not proved against it. The lift
is tested against Unicorn ([`scripts/decompile-check`](../../scripts/decompile-check/README.md)).

## Not done

AArch64 is meant to have the same layers as RISC-V:

- layer -1: an image loader and an execution context (arm64-semantics' loader and Linux
  system calls, rather than a zkVM);
- layer 0: a judgement over `Arm64.Step`;
- a simulation that carries a run of the lifted program down to `Arm64.Step`, the
  counterpart of [`../RiscV/Lift`](../RiscV/Lift/README.md);
- proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).
