# Ascent

The correspondence calculus, independent of any instruction set. A concrete program, run
by some step function, *corresponds* to an abstract function when every run from a related
state ends in a state related to the abstract result.

| file | contents |
| --- | --- |
| `Refines.lean` | `RefinesP` and `RefinesO`: refinement of a partial semantics by abstract programs at three result monads (pure, `Option`, `Except`), and how they relate. |
| `Corres.lean` | `CorresM step SR P fa c`: from a state related by `SR` to an abstract state satisfying `P`, running `c` succeeds and ends related to `fa` of it. `StepTriple` is the same thing as a Hoare triple. Includes the rules `weaken`, `congr` and `seq`. |

Nothing here mentions a machine. Instances live with each ISA: `RiscV/Corres.lean` takes
`step` to be riscv-zkvm's `stepsSp1`, and `Lprog/Sem.lean` defines `CorresIsa` over the
logical machine. The bridges to the framework's judgement, `SafeN`, are in those
instances.

Ported from catcrypt-compiler's ascent, which follows Sebastian Graf's
[ascent](https://github.com/sgraf812/ascent). [`PROVENANCE.md`](PROVENANCE.md) has the origin of
each file, and [`LICENSE-catcrypt`](LICENSE-catcrypt) the licence it came under.
