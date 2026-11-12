# ARM

**Layer 0 of the [roadmap](../../ROADMAP.md) for AArch64:** the machine model. The
counterpart of `RiscV/`, to be built out after it.

## Today

| file | contents |
| --- | --- |
| `Arm64.lean` | Imports the AArch64 semantics: the trusted package `arm64` of DeepMind's [arm64-semantics](https://github.com/google-deepmind/code-verification/tree/main/arm64-semantics) (`Arm64.Trusted`), a dependency used unmodified at the commit pinned in `lakefile.toml`. Its `Arm64.Step` fetches four bytes, decodes and executes them, over Linux user-mode state. **Trusted** (`docs/ISA.md`). |

Nothing here states a judgement over `Arm64.Step` yet.

## Where it is going

AArch64 is meant to be a peer of RISC-V, with the same layers:
- the image loader and the context (layer -1): arm64-semantics' loader and Linux system
  calls, a context other than a zkVM;
- the judgement over `Arm64.Step` (layer 0);
- a lift into the shared low logical program `../Lprog` (layer 0.5), with its simulation: the
  counterpart of `../RiscV/Lprog`. Its flags become explicit values in the shared operations;
- the proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).

