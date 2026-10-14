# leanVM guests

A second target for the framework: guests of [leanVM](https://github.com/leanEthereum/leanVM),
`no_std` Rust built for `riscv64im-unknown-none-elf` against its SDK, on the
`riscv-exploration` branch. `docs/TO-VERIFY.md` lists it.

## Blake2s

`programs/blake2s/blake2s.elf` at commit `9255db3ea2a604898c8af4677f4707d5f671f83a` (the
merge of leanVM PR 555): BLAKE2s-256 of the bytes `0, 1, 2, …` (mod 251), as many as the
advice's first word says, in plain Rust; it commits the length and the digest. 12.5 KB,
957 instruction words: `compress` (644), `main` (220), the SDK's `finish` (47), `memset`
(38), `_start` (14) and four one-`unimp` panic stubs.

- `experiments/leanvm/fetch.sh` fetches the ELF by content, checks its SHA-256
  (`6d83bc01…`), writes the `llvm-nm` boundaries, and prints the load digest
  (`0x10000000 2adaee33…`, entry plus every `PT_LOAD` segment).
- `Blake2s/Image/` is `gen-image`'s output: one module per function (`words`, `prog`), the
  three data chunks (`.rodata` and `.data` at `0x40000000`, `.bss` after), and the
  `Layout`. gen-image cross-checked it against riscv-zkvm's `Interpreter.load`.
- `Blake2s/Loaded.lean`: the layout is well-formed and each function's words decode to its
  program, kernel-checked.

**The specification** of the hash is the Lean one in
[hash-specs](https://github.com/dhsorens/hash-specs) (`Hash.BLAKE2.*`: reference, fast,
streaming, and their equivalence). It is on Lean `v4.34.0` with Mathlib; this repository is on
`v4.33.0` with no Mathlib, so the dependency is not taken yet. When the proof reaches the
digest, either this repository moves to the same toolchain and requires hash-specs, or the
Mathlib-free reference module is what the guest's `compress` is proved against. The statement
to aim for: a run of the guest with advice word `n` commits `n` and `BLAKE2s-256` of the
`n` bytes `i mod 251`.

## What the framework has and what leanVM needs

Generic, and reused as is: the ELF loader and image facts (`AsmVerif.RiscV.Load`,
`Image`), the decoder (riscv-zkvm's, shared with SP1), the frame and contract checkers and
their soundness (`AsmVerif.RiscV.Frame`, `Check`), the typed-stores layer with its model
instances, and `Infer`.

Specific to the zkVM, to be added as a second instance beside SP1's:

- **The step.** `stepSp1` encodes SP1's `ecall` dispatch and memory checks. leanVM's run
  has no syscall but `exit`; an unmapped access, an `ecall` that is not `exit`, or an illegal
  instruction (`unimp`, which is what a panic is) ends the run with no proof. The base
  instructions are the same rv64im `execInstr`; leanVM adds one custom instruction, the
  BLAKE2s compression, which this guest does not use (it is "plain Rust"). The soundness
  proofs are organised around `plainStep` for ordinary instructions and `sysStep` for the
  rest, so the leanVM step is a second instance of that small layer, plus a check that
  `leanvm_core::rv` agrees with `execInstr` on the base instructions.
- **The memory map.** Fixed by the SDK's linker script: text at `0x10000000` (256 MiB),
  advice at `0x20000000` (64 KiB here, `__advice_top`), RAM at `0x40000000` (1 MiB) with the
  stack growing down from `0x40100000`. These are `Env` facts (`stackTop`, protected
  text, the data regions).
- **Advice.** A region the prover fills, read-only to the guest, about which the statement
  says nothing: a new flavour of region for `Env` (unwritten, contents unknown), stated with
  the existing footprint and `cells` vocabulary.
- **Commit and the output.** `commit` appends to the SDK's `PUBLIC` buffer (`0x40000580`,
  256 bytes) and `finish` hashes it; the run's output is that digest. The specification
  of a guest is about this buffer at exit.

Nothing of this is started: the directory holds the image, its loaded facts, and this plan.
