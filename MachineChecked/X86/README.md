# X86

x86-64 at layers 0 and 0.5 of the [roadmap](../../ROADMAP.md): the machine model, and a lift
into Lprog used by the decompiler. This is the counterpart of [`../RiscV`](../RiscV/README.md),
with less built and nothing proved.

| file | contents |
| --- | --- |
| `Kraken.lean` | Imports the x86-64 semantics: [Kraken](https://github.com/AeneasVerif/kraken)'s x64 model (`Kraken.X64.Semantics`), used unmodified at the commit pinned in `lakefile.toml`. Its programs are assembly, not bytes. **Trusted** ([`docs/ISA.md`](../../docs/ISA.md)). |
| `Lift/Instr.lean` | The integer instructions of x86-64 in 64-bit mode and a decoder from bytes (`decode`). Written here, since Kraken has no decoder. Compared with LLVM's disassembler on the test programs. |
| `Lift/Lift.lean` | The x86-64 lift (`liftX86`): those instructions, lifted with the shared lift of linked programs (`Lprog/Linked.lean` in [`lprog`](../../lprog/README.md)). Not proved, and not yet compared with Kraken's semantics. |
| `Lift/Table.lean` | Each kind of instruction and whether the lift takes it, computed from the lift. Generates the table in `LIMITS.md`. |
| `Bare.lean` | An x86-64 program without an operating system as a Pancake program (`Guest.toPancake`): this lift, then lift 2 ([`../Logical`](../Logical/README.md)), with `syscall` as the system call. Used by `decompile --to pancake` on an x86-64 ELF. |
| [`LIMITS.md`](LIMITS.md) | What the decompiler accepts on x86-64, every instruction and whether it is lifted, where it gives up, what it assumes, how its output differs from the processor, and how far it is tested. |

The x86-64 registers at Lprog are in the `lprog` package: `lprog/Lprog/X86/Reg.lean`
(namespace `Lprog.X86`).

## Status

No judgement over Kraken's step is stated yet. The lift does not go through Kraken: it reads
bytes, which Kraken does not, and handles instructions Kraken lacks. It is tested against
Unicorn ([`scripts/decompile-check`](../../scripts/decompile-check/README.md)).

## Not done

x86-64 is meant to have the same layers as RISC-V:

- layer -1: since Kraken's programs are assembly, this means reading `.S` files or
  disassembled `.o` files rather than loading an ELF, with the assembler and linker trusted
  ([`docs/ELF.md`](../../docs/ELF.md) §4);
- layer 0: a judgement over Kraken's x64 step;
- the lift stated over Kraken's instructions where Kraken has them, with a simulation down to
  Kraken's step, the counterpart of [`../RiscV/Lift`](../RiscV/Lift/README.md);
- proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).
