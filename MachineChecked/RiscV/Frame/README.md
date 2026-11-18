# Frame

The frame analysis, a layer-0 proof tool (see [`../README.md`](../README.md)) and the base the
contract checker grew from. For one activation of a function it proves return-address
integrity: whenever the activation leaves the function, by `ret` or by any transfer out of its
address range, `ra` holds its entry value (possibly restored from the stack).

| file | contents |
| --- | --- |
| `Domain.lean` | The analysis, computable so the kernel can run it, and the annotation it checks. |
| `Sound.lean` | Soundness against `stepSp1`: `integrity`. |
| `Image.lean` | Discharges the code premise (`CodeOk`) from a loaded image. |

`Tools/FrameSweep.lean` runs the analysis over every function of an ELF and reports which
annotations check.
