# leanVM guests

A second target for the framework: guests of [leanVM](https://github.com/leanEthereum/leanVM),
`no_std` Rust built for `riscv64im-unknown-none-elf` against its SDK (branch
`riscv-exploration`). It is one of the targets in [`ROADMAP.md`](../../ROADMAP.md).

**Status:** the image is loaded and its decoding checked. Nothing about the guest's behaviour
is proved yet; no leanVM step exists in the framework. Build: `lake build
Examples.LeanVM.Blake2s.Loaded`.

## Blake2s

`programs/blake2s/blake2s.elf` at commit `9255db3ea2a604898c8af4677f4707d5f671f83a` (the merge
of leanVM PR 555). In plain Rust, it computes BLAKE2s-256 of the bytes `0, 1, 2, …` (mod 251),
as many as the advice's first word says, and commits the length and the digest. It is 12.5 KB.
Its functions, in instruction words: `compress` (644), `main` (220), the SDK's `finish` (47),
`memset` (38), `_start` (14) and four panic stubs of one `unimp` each.

- The ELF is identified by content: SHA-256 `6d83bc01…`, load digest `0x10000000 2adaee33…`
  (entry and every `PT_LOAD` segment). The fetch script is not published yet.
- **Provenance and licence.** leanVM, its SDK and the guest are Apache-2.0.
- `Blake2s/Image/`: `gen-image`'s output, cross-checked against riscv-zkvm's
  `Interpreter.load`. One module per function (`words`, `prog`), three data chunks
  (`.rodata` and `.data` at `0x40000000`, `.bss` after), and the `Layout`. `_start` has no
  size in the symbol table, so it is part of the layout rather than a function module.
- `Blake2s/Loaded.lean`: the layout is well formed and each function's words decode to its
  program, checked by the kernel.

**The specification** of the hash is the Lean one in
[hash-specs](https://github.com/dhsorens/hash-specs) (`Hash.BLAKE2.*`: reference, fast and
streaming versions, and their equivalence). hash-specs uses a newer Lean than this repository,
so it is not a dependency yet. Once the proof reaches the digest, either this repository moves
to the same toolchain and requires hash-specs, or `compress` is proved against hash-specs'
Mathlib-free reference module. The target statement: a run of the guest with advice word `n`
commits `n` and the BLAKE2s-256 digest of the `n` bytes `i mod 251`.

## What leanVM needs from the framework

Reused as is: the ELF loader and image facts (`MachineChecked.RiscV.Load`, `Image`), the
decoder (riscv-zkvm's, shared with SP1), the frame and contract checkers and their soundness
(`MachineChecked.RiscV.Frame`, `Check`), the typed-stores layer with its model instances, and
`Infer`.

To be added as a second instance beside SP1's:

- **The step.** `stepSp1` encodes SP1's `ecall` dispatch and memory checks. leanVM's only
  syscall is `exit`; an unmapped access, any other `ecall`, or an illegal instruction (`unimp`,
  which is how a panic ends) ends the run with no proof. The base instructions are the same
  RV64IM `execInstr`. leanVM adds one custom instruction, the BLAKE2s compression, which this
  guest does not use. The soundness proofs separate `plainStep` (ordinary instructions) from
  `sysStep` (the rest), so the leanVM step is a second instance of that small layer, plus a
  check that `leanvm_core::rv` agrees with `execInstr` on the base instructions.
- **The memory map**, fixed by the SDK's linker script: text at `0x10000000` (256 MiB), advice
  at `0x20000000` (64 KiB here, `__advice_top`), RAM at `0x40000000` (1 MiB), with the stack
  growing down from `0x40100000`. These become `Env` facts (`stackTop`, protected text, the
  data regions).
- **Advice.** A region the prover fills, read-only to the guest, about which the statement
  says nothing. It is a new kind of `Env` region (never written, contents unknown), stated with
  the existing footprint and `cells` vocabulary.
- **Commit and output.** `commit` appends to the SDK's `PUBLIC` buffer (`0x40000580`, 256
  bytes) and `finish` hashes it; the run's output is that digest. A guest's specification is
  about this buffer at exit.
