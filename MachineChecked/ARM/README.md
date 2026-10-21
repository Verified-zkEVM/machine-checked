# ARM

The AArch64 side of the framework: the counterpart of `RiscV/`, built out after it.

## Today

| file | contents |
| --- | --- |
| `Model.lean` | The AArch64 machine model: a scalar general-purpose subset (64-bit ALU with carry and zero flags, loads, stores, `cbnz`, conditional branches), with `evalBInst`/`evalBMInst` and block runners. **Trusted.** |
| `../Mem64.lean` | Byte-addressed 64-bit memory with little-endian doubleword access, used by the model. |

The model is not yet proved against a canonical AArch64 specification. It is named as trusted
on the trust ladder (`docs/ELF.md` §4), and is to be verified against the specification chosen in
`docs/ISA.md` or replaced by a model that already is. Nothing outside this directory imports it.

## Where it is going

AArch64 is meant to be a peer of RISC-V, with the same stack:
- an image loader;
- the judgement over this model's step;
- an `Lprog` instance with its lift and simulation (the counterpart of `Lprog/RiscV.lean` and
  `Lprog/Lift.lean`);
- the checker and executor where they pay off.

The ISA-independent layers (`Ascent/` and the core of `Lprog/`) are shared. The order of work
is in `docs/PLAN.md`.

Ported from catcrypt-compiler; see [`PROVENANCE.md`](PROVENANCE.md).
