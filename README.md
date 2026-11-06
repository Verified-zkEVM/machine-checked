# MachineChecked

Formally verify machine code directly in Lean.

> **Early days.** MachineChecked is a young research project, and it is changing quickly: its
> layers, interfaces and file layout will move as the design settles. Some layers exist only on
> paper, some proofs rest on premises that are still open, and the AArch64 and x86-64 models are
> trusted rather than verified. The [roadmap](ROADMAP.md) says what exists and what doesn't. Read
> a result here as evidence, not yet as an audit: check exactly what each theorem states and
> assumes before relying on it. Questions, issues and feedback are very welcome.

MachineChecked takes the binary a compiler produced, not its source, and proves in Lean that it
meets a high-level specification. The compiler and assembler are not trusted. What is
trusted is the model of the instruction set, the Lean kernel, and the step that reads the binary
into Lean.

## The idea

```
  layer 2     spec refinement           high-level specification, refined downward
                   ▲  meet in the middle
  layer 1     structured logical        variables, structured control flow, program
              program                   logics, function contracts       (not started)
                   ▲  lift 2: decompilation (verified, possibly partial)
  layer 0.5   low logical program       registers, flat memory, labels; operations
                                        shared by every ISA
                   ▲  lift 1: translation (verified, per ISA)
  layer 0     ISA                       a verified interpreter: RISC-V, ARM, x86
                   ▲  loading
  layer -1    ELF and context           image, layout, syscalls, halting, calling convention
```

1. **Load.** An ELF becomes Lean data: its code, read-only data and layout. Tools read the
   ELF and emit Lean, and Lean re-checks what they claim.
2. **The ISA.** The loaded program runs on a model of its instruction set, in its execution
   context (for RISC-V, SP1). This is the semantics every result is stated against.
3. **Lift.** A function's decoded instructions are translated into a low logical program
   whose control flow and operations are the same for every instruction set. A simulation
   proof carries every run of the lifted program back down to a run of the machine, so
   whatever is proved there holds of the binary.
4. **Program logics and refinement** (layers 1 and 2) are to sit above, written once rather
   than once per instruction set, and meet the high-level specification in the middle.

Function specifications compose through a contract table, and the whole program's theorem
is stated over its accepting runs from the loaded image. The roadmap, with the current state
of each layer and the targets, is [`ROADMAP.md`](ROADMAP.md).

## Instruction sets

The framework is built for RISC-V first: layers -1 to 0.5 exist there today, on
[riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm)'s model, whose step function is what
SP1 executes. x86-64 and AArch64 are meant to be peers of RISC-V. For now each has only a
machine model, which is trusted until it is verified against its canonical specification
([`docs/ISA.md`](docs/ISA.md)). Everything from layer 0.5 up is shared between them.

## Repository map

```
ROADMAP.md             the layers, where the code stands, targets and next steps
MachineChecked/        the framework, by layer (see MachineChecked/README.md)
  Ascent/              runs and correspondence, for any machine
  Lprog/               layer 0.5: the low logical program and its shared operations
  RiscV/               layers -1 and 0 for RISC-V on SP1, and the layer-0 proof tools
    Lprog/             the RISC-V lift into layer 0.5, with its simulation
  ARM/, X86/           layer 0 for AArch64 and x86-64: machine models (trusted)
  Logical/, Refine/    layers 1 and 2: not started
Cases/                 case studies: real binaries, verified (see Cases/README.md)
Tools/                 build-time tools: ELF to Lean, contract inference (see Tools/README.md)
docs/                  design notes and the trust ladder
```

## Building

The Lean toolchain is pinned in `lean-toolchain` and installed by
[elan](https://github.com/leanprover/elan).

```sh
lake exe cache get              # Mathlib's prebuilt oleans
lake build                      # the framework and the tools, in minutes
lake build Cases.CatCrypt       # one case study (each has a root module)
lake build Cases                # every case study (zip-2005 takes a few hours)
```

To check one file while working, use `lake env lean path/to/File.lean`.

## Documentation

- [`ROADMAP.md`](ROADMAP.md): the layers, the current state, the targets and the next steps.
- [`MachineChecked/README.md`](MachineChecked/README.md): the framework, directory by
  directory, with the layer each belongs to.
- [`docs/Walkthrough.md`](docs/Walkthrough.md): one proof, `memcmp`, through every layer. Start here.
- [`docs/Architecture.md`](docs/Architecture.md): the judgement and the contract table.
- [`docs/ELF.md`](docs/ELF.md): what the toolchain can tell us and what is trusted (the trust
  ladder, §4).
- [`docs/LogicalMachine.md`](docs/LogicalMachine.md): a design sketch of layer 1.
- [`docs/ISA.md`](docs/ISA.md): the canonical specification for each instruction set.
- [`docs/notes/`](docs/notes/README.md): working notes, archived.

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Licence

Apache-2.0 ([`LICENSE`](LICENSE)). Code ported from other projects keeps its original licence
notice, recorded in the `PROVENANCE.md` of its directory. The decoded binaries under
`Cases/*/Image/` come from programs under their own licences; each case's README says which.
