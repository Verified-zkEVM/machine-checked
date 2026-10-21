# X86

The x86-64 side of the framework: the counterpart of `RiscV/`, built out after it.

## Today

| file | contents |
| --- | --- |
| `JasminModel.lean` | The x86-64 machine model: a transcription of Jasmin's x86 semantics. Its state has registers, five flags and word-granular memory. It covers 66 instruction forms (scalar ALU, flags, shifts and rotates, `CMOVcc`/`SETcc`, ADX/BMI2, widening multiplies, memory forms) and runs them with `evalInstr`/`runBlock`. **Trusted.** |
| `Model.lean` | An earlier, smaller model (18 forms). `JasminModel` imports it and proves the two agree on data results. |
| `BinOp.lean` | The two definitions the models share with catcrypt-compiler's IR layer: `shiftMask` and `JasminBinOp`. |

The model is not yet proved against a canonical x86-64 specification. It is named as trusted
on the trust ladder (`docs/ELF.md` §4), and is to be verified against the specification chosen in
`docs/ISA.md` or replaced by a model that already is. It has no control flow and no decoder
yet. Nothing outside this directory imports it.

## Where it is going

x86-64 is meant to be a peer of RISC-V, with the same stack:
- control flow and a decoder;
- an image loader;
- the judgement over this model's step;
- an `Lprog` instance with its lift and simulation;
- the checker and executor where they pay off.

The ISA-independent layers (`Ascent/` and the core of `Lprog/`) are shared. The order of work
is in `docs/PLAN.md`.

Ported from catcrypt-compiler; see [`PROVENANCE.md`](PROVENANCE.md).
