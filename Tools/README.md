# Tools

**Layer -1 of the [roadmap](../ROADMAP.md)**, outside the trusted base.

Build-time tools that turn an ELF into Lean, or into a program of a layer above. They are **untrusted**: everything they emit is
checked by the Lean kernel, and nothing in `MachineChecked/` or `Cases/` imports them.

| tool | command | what it does |
| --- | --- | --- |
| `GenImage.lean` | `lake exe gen-image ELF NM OUTDIR MODPREFIX [STACKTOP]` | The ELF as Lean data: one module per function (its words and their decoding), the data chunks and the layout. |
| `Infer.lean` | `lake exe infer-contracts ELF NM OUT.tsv STACKTOP PROTLO PROTHI` | For every function, bottom-up over the call graph: an interface (`Check.Iface`) and a certificate, emitted as Lean for the checker to re-check. |
| `FrameSweep.lean` | `lake exe frame-sweep ELF NM OUT.tsv` | Runs the frame analysis over every function and reports which annotations check, and why not. |
| `Decompile.lean` | `lake exe decompile --to lprog\|pancake BINARY [OUT]` | A binary as an Lprog program, in text, or as a Pancake program. `BINARY` is an RV64 ELF or a Flapjack image. See below. |
| `Fjimg.lean` | (library) | The text form of a Flapjack image. |
| `Elf.lean` | (library) | ELF and symbol-table helpers shared by the tools. |
| `StructureTest.lean` | (built) | Checks of `Logical/Structure.lean` on small graphs, run when it is built: a switch is never a two-way choice or a way out. |

`NM` is the output of `llvm-nm -S --defined-only ELF`. It is used only for function boundaries,
which are hints: the kernel re-checks what the tools derive from them. Words are read with
riscv-zkvm's own ELF parser.

## `decompile`

The decompiler of [`docs/design/Decompiler.md`](../docs/design/Decompiler.md): from a RISC-V
binary to layer 0.5 (`--to lprog`) and on to layer 1 (`--to pancake`).

```
lake exe decompile --to pancake GUEST.elf OUT.pnk     # an RV64 ELF, as SP1 guests are
lake exe decompile --to lprog   GUEST.elf OUT.lprog
lake exe decompile --to lprog --proved GUEST.elf      # by the lift the theorems are about
lake exe decompile --to pancake IMAGE.fjimg OUT.pnk   # a binary from Flapjack
```

**Nothing on the way to Pancake is proved yet.** It is checked by running:
[`scripts/decompile-check`](../scripts/decompile-check/README.md) recompiles the output with
Flapjack and compares what the two binaries do.

### An ELF

The functions are the ELF's own text symbols (it must not be stripped). The route is

- the lift of whole programs (`RiscV/Lprog/Whole.lean`), which takes what rustc and its
  linker emit: every instruction of RV64IM, far calls, jump tables, indirect calls, calls
  that link through `t0`;
- lift 2 (`Logical/Lift.lean`): a Pancake function for each function, with `if` and `while`
  where the function's control flow has a structure;
- SP1's environment (`RiscV/Sp1/`): the guest's memory at its own addresses, and `ecall` as
  the FFI call `@ecall(t0, a0, a1, a2)`;
- the printer (`Logical/Pancake.lean`).

The Pancake text starts with comments that say what it is of: how many functions, and how
many of them are not structured but a loop over their blocks; which Pancake function is
which symbol; and the places where the program may give up (`l_trap(n)`), each described.

**What it refuses, and how.** A file it does not take is an error: no ELF, RV32, compressed
instructions, a relocatable or position-independent file, a stripped one. Inside a file it
takes, what the lift does not cover becomes a place where the Pancake program gives up when
it gets there, by `l_trap(n)`, and does nothing further: a word that is no instruction, a
jump out of a function that is no call, a computed jump to an address the tool did not find
in the program, a return to another address than the call's. So the output either behaves
as the binary or says that it stopped, and where.

**What it does not recover.** Registers are global variables, the stack is memory, and
nothing has a type or a name of its own. The text is about as long as the disassembly.

`--to lprog --proved` is the lift `liftProg`, the definition the theorems are about
(`RiscV/Lprog/Equiv.lean`: a machine that holds the functions and the lifted program are
equivalent to an observer). It covers less: what it does not is an `abort`, and a function
with a word riscv-zkvm does not decode is left out. In both forms the Lprog text is read
back and compared with the program before it is written (`Lprog.parse_print` proves the
step from tokens; the step from text is this check).

### A Flapjack image

`decompile --to pancake IMAGE.fjimg` takes a binary from Flapjack (in flapjack-flip's text
form): lift 1 for code without functions (`RiscV/Lprog/Flat.lean`), in the layout of a
Flapjack image (`RiscV/Flapjack/`), then lift 2. Flapjack's code has no function boundaries
left and returns through computed jumps, so the whole image is one function and a loop over
its blocks. The image gets half the heap and half the stack it had.

The tools are RISC-V only for now. Generalising `gen-image` and the ELF reader to x86-64 and
AArch64 is part of bringing those instruction sets up to RISC-V's level
([`ROADMAP.md`](../ROADMAP.md)).
