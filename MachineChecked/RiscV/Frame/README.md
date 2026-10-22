# Frame

**A layer-0 proof tool** (see [`../README.md`](../README.md)): it proves things about
riscv-zkvm's machine directly, without the lift to Lprog. Its results enter the contract table
as `SafeN` facts.

The frame analysis: the first checker, and the base the contract checker grew from. For one
activation of a function, it shows return-address integrity. At every way the activation
leaves the function, whether by a `ret` or by any transfer out of its address range, `ra`
holds its entry value, possibly restored from the stack.

| file | contents |
| --- | --- |
| `Domain.lean` | The analysis, computable so the kernel can run it, with the annotation it checks. |
| `Sound.lean` | Soundness against `stepSp1`: `integrity`. |
| `Image.lean` | The code premise (`CodeOk`), discharged from a loaded image. |

`Tools/FrameSweep.lean` runs the analysis over every function of an ELF and reports which
annotations check.
