# X86

**Layer 0 of the [roadmap](../../ROADMAP.md) for x86-64:** the machine model. The
counterpart of `RiscV/`, to be built out after it.

## Today

| file | contents |
| --- | --- |
| `Kraken.lean` | Imports the x86-64 semantics: [Kraken](https://github.com/AeneasVerif/kraken)'s x64 model (`Kraken.X64.Semantics`), a dependency used unmodified at the commit pinned in `lakefile.toml`. Its programs are assembly, not bytes. **Trusted** (`docs/ISA.md`). |

Nothing here states a judgement over Kraken's step yet.

## Where it is going

x86-64 is meant to be a peer of RISC-V, with the same layers:
- Kraken's programs are assembly, so layer -1 is reading `.S` files or disassembled `.o` files,
  not loading an ELF, and the assembler and linker are trusted (`docs/ELF.md` §4);
- the judgement over Kraken's x64 step (layer 0);
- a lift into the shared low logical program `../Lprog` (layer 0.5), with its simulation: the
  counterpart of `../RiscV/Lprog`. Its flags become explicit values in the shared operations;
- the proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).

