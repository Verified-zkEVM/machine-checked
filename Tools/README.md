# Tools

**Layer -1 of the [roadmap](../ROADMAP.md)**, outside the trusted base.

Build-time tools that turn an ELF into Lean, or into a program of a layer above. They are **untrusted**: everything they emit is
checked by the Lean kernel, and nothing in `MachineChecked/` or `Cases/` imports them.

| tool | command | what it does |
| --- | --- | --- |
| `GenImage.lean` | `lake exe gen-image ELF NM OUTDIR MODPREFIX [STACKTOP]` | The ELF as Lean data: one module per function (its words and their decoding), the data chunks and the layout. |
| `Infer.lean` | `lake exe infer-contracts ELF NM OUT.tsv STACKTOP PROTLO PROTHI` | For every function, bottom-up over the call graph: an interface (`Check.Iface`) and a certificate, emitted as Lean for the checker to re-check. |
| `FrameSweep.lean` | `lake exe frame-sweep ELF NM OUT.tsv` | Runs the frame analysis over every function and reports which annotations check, and why not. |
| `Decompile.lean` | `lake exe decompile --to lprog ELF NM [OUT]`<br>`lake exe decompile --to lprog\|pancake IMAGE.fjimg [OUT]` | A binary as an Lprog program, in text; a Flapjack image also as a Pancake program. See below. |
| `Fjimg.lean` | (library) | The text form of a Flapjack image. |
| `Elf.lean` | (library) | ELF and symbol-table helpers shared by the tools. |

`NM` is the output of `llvm-nm -S --defined-only ELF`. It is used only for function boundaries,
which are hints: the kernel re-checks what the tools derive from them. Words are read with
riscv-zkvm's own ELF parser.

## `decompile`

`decompile --to lprog` is the first step of the decompiler of
[`docs/design/Decompiler.md`](../docs/design/Decompiler.md): from a RISC-V binary to layer 0.5.
Its output is text (`MachineChecked/Lprog/Text.lean`): one paragraph per function, one line per
instruction, `#` comments on top saying what was left out.

What is proved, and what the tool adds to it:

- The program is `liftProg` of the functions, the definition the theorems are about. A
  machine that holds those functions and the lifted program are equivalent to an observer
  (`RiscV/Lprog/Equiv.lean`: `refines_lift`, and `lift_refines` where the lifted program never
  goes `wrong`). An instruction the lift does not cover is an `abort`, which is `wrong`; the
  tool counts them.
- The parser reads the tokens the printer writes (`Lprog.parse_print`). Between tokens and
  text nothing is proved: the tool reads its own text back and fails unless it gets the
  program it wrote.
- Not proved: that the machine holds the functions (the ELF reader and the `NM` boundaries
  are the tool's), and that the compiled tool runs the definitions as Lean states them.

The candidates of an indirect call are every function of the program, so each is a long line.

### Flapjack images, and on to Pancake

`decompile --to pancake IMAGE.fjimg` takes a binary from Flapjack (in flapjack-flip's text
form) through Lprog to Pancake source that Flapjack compiles again:

- lift 1 for code without functions (`RiscV/Lprog/Flat.lean`), in the layout of a Flapjack
  image (`RiscV/Flapjack/`);
- lift 2, baseline (`Logical/Lift.lean`): the registers as globals and a loop over the
  blocks. It recovers no structure, so the output is about as long as the binary and
  nothing like the source it came from;
- the printer (`Logical/Pancake.lean`).

**None of this is proved yet**, unlike the lift of an ELF above. It is checked by running:
[`scripts/decompile-check`](../scripts/decompile-check/README.md) recompiles the output with
Flapjack and compares what the two binaries do. The recompiled binary takes about twelve
times the steps, and the image gets half the heap and half the stack it had.

The tools are RISC-V only for now. Generalising `gen-image` and the ELF reader to x86-64 and
AArch64 is part of bringing those instruction sets up to RISC-V's level
([`ROADMAP.md`](../ROADMAP.md)).
