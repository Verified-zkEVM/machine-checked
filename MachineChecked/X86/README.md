# X86

**Layer 0 of the [roadmap](../../ROADMAP.md) for x86-64:** the machine model. The
counterpart of `RiscV/`, to be built out after it.

## Today

| file | contents |
| --- | --- |
| `Model.lean` | The x86-64 machine model: a transcription of Jasmin's x86 semantics. Its state has registers, five flags and word-granular memory. It covers 66 instruction forms (scalar ALU, flags, shifts and rotates, `CMOVcc`/`SETcc`, ADX/BMI2, widening multiplies, memory forms) and runs them with `evalInstr`/`runBlock`. **Trusted.** |
| `BinOp.lean` | Two definitions shared with catcrypt-compiler's IR layer: `shiftMask` and `JasminBinOp`. |

The model is not proved against a canonical x86-64 specification. It is named as trusted on
the trust ladder (`docs/ELF.md` §4). x86-64's semantics is now
[Kraken](https://github.com/AeneasVerif/kraken)'s x64 model (`docs/ISA.md`); when Kraken is
required, `Model.lean` is removed. Nothing outside this directory imports it.

## Where it is going

x86-64 is meant to be a peer of RISC-V, with the same layers:
- Kraken as a dependency, used unmodified at a pinned revision, as riscv-zkvm is for RISC-V.
  Its programs are assembly, so layer -1 is reading `.S` files or disassembled `.o` files,
  not loading an ELF, and the assembler and linker are trusted (`docs/ELF.md` §4);
- the judgement over Kraken's x64 step (layer 0);
- a lift into the shared low logical program `../Lprog` (layer 0.5), with its simulation: the
  counterpart of `../RiscV/Lprog`. Its flags become explicit values in the shared operations;
- the proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).

Ported from catcrypt-compiler; see [`PROVENANCE.md`](PROVENANCE.md).
