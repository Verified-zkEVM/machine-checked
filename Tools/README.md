# Tools

**Layer -1 of the [roadmap](../ROADMAP.md)**, outside the trusted base.

Build-time tools that turn an ELF into Lean, or into a program of a layer above. They are **untrusted**: everything they emit is
checked by the Lean kernel, and nothing in `MachineChecked/` or `Cases/` imports them.

| tool | command | what it does |
| --- | --- | --- |
| `GenImage.lean` | `lake exe gen-image ELF NM OUTDIR MODPREFIX [STACKTOP]` | The ELF as Lean data: one module per function (its words and their decoding), the data chunks and the layout. |
| `Infer.lean` | `lake exe infer-contracts ELF NM OUT.tsv STACKTOP PROTLO PROTHI` | For every function, bottom-up over the call graph: an interface (`Check.Iface`) and a certificate, emitted as Lean for the checker to re-check. |
| `FrameSweep.lean` | `lake exe frame-sweep ELF NM OUT.tsv` | Runs the frame analysis over every function and reports which annotations check, and why not. |
| `Decompile.lean` | `lake exe decompile --to lprog\|pancake\|lean BINARY …` | A binary as an Lprog program, in text or as Lean, or as a Pancake program. `BINARY` is an ELF or a Flapjack image. See below. |
| `ToLean.lean` | (library, and the command `check_elf_words`) | `decompile --to lean`: the modules it writes, the lemmas their theorems rest on, and the check of their words against the ELF. |
| `Test/ToLean.lean` | (built) | Checks of `ToLean.lean`, run when it is built: a body in parts, a function's theorem from its parts, and a changed term refuted by the kernel. |
| `Fjimg.lean` | (library) | The text form of a Flapjack image. |
| `Elf.lean` | (library) | ELF and symbol-table helpers shared by the tools. |
| `Test/` | (built) | Unit tests, run when they are built (`#guard`): each instruction set's decoder and lift, one instruction at a time against its manual (`Run.lean` runs the lift of one instruction), and the shared passes. See below. |

`NM` is the output of `llvm-nm -S --defined-only ELF`. It is used only for function boundaries,
which are hints: the kernel re-checks what the tools derive from them. Words are read with
riscv-zkvm's own ELF parser.

## `decompile`

The decompiler of [`docs/design/Decompiler.md`](../docs/design/Decompiler.md): from a binary
for RISC-V, AArch64 or x86-64 to layer 0.5 (`--to lprog`) and on to layer 1
(`--to pancake`). The instruction set is the ELF's own.

```
lake exe decompile --to pancake GUEST.elf OUT.pnk     # an ELF for RV64IM, AArch64 or x86-64
lake exe decompile --to lprog   GUEST.elf OUT.lprog
lake exe decompile --to lprog --proved GUEST.elf      # RISC-V, by the lift the theorems are about
lake exe decompile --to lean --proved GUEST.elf OUTDIR NAMESPACE   # the same as Lean, checked by the kernel
lake exe decompile --to pancake IMAGE.fjimg OUT.pnk   # a binary from Flapjack
lake exe decompile --table riscv|aarch64|x86-64 [KINDS]   # the instruction table of a LIMITS.md
lake exe decompile --kinds riscv|aarch64|x86-64 INSTRUCTIONS
lake exe decompile --listing GUEST.elf                # x86-64: what the decoder reads
```

**What it does not do is written for each instruction set, under the same headings:**
[`RiscV/LIMITS.md`](../MachineChecked/RiscV/LIMITS.md),
[`ARM/LIMITS.md`](../MachineChecked/ARM/LIMITS.md),
[`X86/LIMITS.md`](../MachineChecked/X86/LIMITS.md). Each has a table of the instructions,
lifted or not and run by the tests or not, that `--table` generates from the lift.

**Nothing on the way to Pancake is proved yet.** It is checked by running:
[`scripts/decompile-check`](../scripts/decompile-check/README.md) recompiles the output with
Flapjack and compares what the two binaries do.

### An ELF

The functions are the ELF's own text symbols (it must not be stripped). The route is

- the lift of linked programs (`Lprog/Linked.lean`), with the lift of one instruction that
  each instruction set gives: `RiscV/Lift/Whole.lean` (every instruction of RV64IM, far
  calls, calls that link through `t0`), `ARM/Lift/Lift.lean` (the integer instructions,
  with the flags as registers), `X86/Lift/Lift.lean` (the integer instructions, read from
  bytes by `X86/Lift/Instr.lean`; a return address on the stack). Jump tables, indirect
  calls and tail calls are shared;
- for AArch64 and x86-64, dropping the writes of flags that nothing reads (`Lprog/Dead.lean`);
- lift 2 (`Logical/Lift.lean`): a Pancake function for each function, with `if` and `while`
  where the function's control flow has a structure;
- the environment (`Logical/Guest.lean`): the program's memory at its own addresses, and a
  system call as an FFI call. An RV64 ELF is taken as an SP1 guest (`RiscV/Sp1/`,
  `@ecall(t0, a0, a1, a2)`); an AArch64 or x86-64 ELF as a program without an operating
  system (`ARM/Bare.lean`, `X86/Bare.lean`, `@syscall(number, a, b, c)`);
- the printer (`Logical/Pancake.lean`).

The Pancake text starts with comments that say what it is of: how many functions, and how
many of them are not structured but a loop over their blocks; which Pancake function is
which symbol; and the places where the program may give up (`l_trap(n)`), each described.

**What it refuses, and how.** A file it does not take is an error: no ELF, 32 bits,
another instruction set, compressed RISC-V instructions, a relocatable or
position-independent file, a stripped one. Inside a file it
takes, what the lift does not cover becomes a place where the Pancake program gives up when
it gets there, by `l_trap(n)`, and does nothing further: a word that is no instruction, a
jump out of a function that is no call, a computed jump to an address the tool did not find
in the program, a return to another address than the call's. So the output either behaves
as the binary or says that it stopped, and where.

**What it does not recover.** Registers are global variables, the stack is memory, and
nothing has a type or a name of its own. The text is about as long as the disassembly.

`--to lprog --proved` is the lift `liftProg`, the definition the theorems are about
(`RiscV/Lift/Equiv.lean`: a machine that holds the functions and the lifted program are
equivalent to an observer). It covers less: what it does not is an `abort`, and a function
with a word riscv-zkvm does not decode is left out. In both forms the Lprog text is read
back and compared with the program before it is written (`Lprog.parse_print` proves the
step from tokens; the step from text is this check).

### As Lean

`decompile --to lean --proved GUEST.elf OUTDIR NS` writes the `--proved` lift as Lean modules
(`ToLean.lean`), for proofs about the program to start from:

- `OUTDIR/NS/Words.lean`: each function's words, and `check_elf_words words "GUEST.elf"`,
  which reads the ELF when the module is built and adds `words_eq_elf`, the words equal to the
  ELF's, for the kernel to check. The path is as given on the command line, read from where the
  module is built. `fns` is the functions the words decode to.
- `OUTDIR/NS/F<i>.lean`: the `i`th function's lift as a term `f<i>`, and
  `f<i>_eq : (liftProg fns)[i]? = some f<i>`. The kernel decides its name, address and stack
  bound (`f<i>_head`) and its body in parts of 128 instructions (`f<i>_parts`), and
  `getElem?_eq_of_chunks` gives the whole; in parts, no limit of the kernel needs raising.
- `OUTDIR/NS.lean` imports them all.

So the kernel checks that each term is the lift of `fns`, and that `words` is the literal
`check_elf_words` put in `words_eq_elf`. How a term came to be written is not trusted. What is:

- **that the literal is the ELF's.** The kernel cannot read a file: `check_elf_words` reads it
  when the module is built, by the same ELF reader as the tool (`Elf.lean`, `functions`,
  `wordsOf`), from the path relative to where the module is built. Lake does not track the
  ELF, so a changed ELF needs the words module rebuilt by hand.
- **that the modules are as the tool wrote them.** Check that `Words.lean` defines `fns` from
  `words` as written and calls `check_elf_words`, and `#print axioms NS.f<i>_eq` for what a
  theorem rests on. A symbol's name goes into a comment only escaped (`commentSafe`).

A misread word does not make a false theorem about the binary: `Equiv.lean`'s
`equivalent_of_entry` takes the code at each function's address (`CodeAt`) as a hypothesis, so
a proof about the machine must show it holds the words `fns` was built from. What a term says
about the binary is what `liftProg`'s theorems say (`Equiv.lean`).

`NS` is an ASCII letter in upper case followed by ASCII letters, digits and `_`, and
`OUTDIR/NS` must not exist yet, so that no file of an earlier run is left among the new ones.
The modules are `noncomputable` (data for the kernel; the code generator does not take terms
this large), and require this repository's root package, for `liftProg` and `Tools.ToLean`.

| binary | functions | instructions | Lean written | build of all modules, 8 at a time |
| --- | --- | --- | --- | --- |
| `experiments/leanvm/out/blake2s.elf` | 6 | 702 | 148 KB | 8 s of CPU |
| `experiments/zip-2005/out/baseline.elf` | 304 | 41,631 | 8.3 MB | 74 s (495 s of CPU) on an Apple M3 Max; the longest function 12 s |

A word or a term changed by one bit fails: the words module does not build, or `decide` finds
the function's statement false. `Test/ToLean.lean` checks the second on a small program.

### A Flapjack image

`decompile --to pancake IMAGE.fjimg` takes a binary from Flapjack (in flapjack-flip's text
form): lift 1 for code without functions (`RiscV/Lift/Flat.lean`), in the layout of a
Flapjack image (`RiscV/Flapjack/`), then lift 2. Flapjack's code has no function boundaries
left and returns through computed jumps, so the whole image is one function and a loop over
its blocks. The image gets half the heap and half the stack it had.

The other tools are RISC-V only for now. Generalising `gen-image` and the ELF reader to
x86-64 and AArch64 is part of bringing those instruction sets up to RISC-V's level
([`ROADMAP.md`](../ROADMAP.md)): `decompile` reads their ELFs through riscv-zkvm's reader,
which reads nothing that depends on the machine.

## Tests

`Tools/Test/` holds unit tests: `#guard`s that the build evaluates, so `lake build Tools`
(and CI) fails if one does not hold. Expected values come from each instruction set's
manual, worked out by hand, not from the code under test.

| file | tests | what |
| --- | --- | --- |
| `Run.lean` | | Runs the lift of one instruction on concrete registers and a byte memory, and says how it ends: at the next instruction, at a branch target, giving up, going `wrong`, or leaving the function (a call, a return, a system call). |
| `RiscV.lean` | 214 | `decodeWord` and the whole-program lift of RV64IM: each `*w` instruction, division by zero and overflow, loads and stores of each width, `x0`, branches, calls and far calls (`auipc` then `jalr`), computed jumps. |
| `Arm.lean` | 342 | The AArch64 lift from instruction words: flags through the conditions that read them, logical immediates, bitfields, conditional select and compare, loads and stores with writeback, branches. |
| `X86.lean` | 392 | The x86-64 decoder and lift from bytes: prefixes and addressing forms, flags at every size, partial register writes, shifts, division, the stack, string instructions with `rep`. |
| `Dead.lean` | 45 | Dropping the writes of flags nothing reads: what is dropped and what is kept, and that a body runs the same before and after. |
| `Text.lean` | 55 | The Lprog text format: each kind of instruction read back from its text, and malformed text refused. |
| `Elf.lean` | 55 | The ELF reader on a small file made by hand, and on truncated and malformed ones: each gives an error, none a crash. |
| `Structure.lean` | 6 | The structure of control flow on small graphs: a switch is never a two-way choice or a way out. |

To test one file while working on it: `lake env lean Tools/Test/X86.lean` (no output is a
pass).
