# MachineChecked

Formally verify machine code directly in Lean.

MachineChecked takes the binary a compiler produced, not its source, and proves in Lean that it
meets a high-level specification. The compiler and assembler are not trusted. What is
trusted is the model of the instruction set, the Lean kernel, and the step that reads the binary
into Lean.

## The idea

```
                     HIGH-LEVEL SPECIFICATION
            ┌─────────────────────────────────────┐
            │ what the program computes:          │
            │ algorithms, protocols, statements   │
            └──────────────────┬──────────────────┘
                               │ refinement
                        PROGRAM LOGICS
            ┌──────────────────┴──────────────────┐
            │ Hoare / refinement / separation /   │
            │ relational / cost / information flow│
            └──────────────────┬──────────────────┘
                               │ sit on
                    LOGICAL MACHINE (intermediate layer)
            ┌──────────────────┴──────────────────┐
            │ labels and control flow, operations,│
            │ loads/stores and effects; one shape │
            │ for every instruction set           │
            └──────────────────┬──────────────────┘
                               │ lifting + simulation proof
                      ARCHITECTURAL MACHINE
            ┌──────────────────┴──────────────────┐
            │ pc + registers + memory, stepped by │
            │ an ISA model (RISC-V, x86-64, ARM)  │
            └──────────────────┬──────────────────┘
                               │ loading
                          BINARY (ELF)
```

1. **Load.** An ELF becomes Lean data: its code, read-only data and layout. Tools read the
   ELF and emit Lean, and Lean re-checks what they claim.
2. **Architectural machine.** The loaded program runs on a model of its instruction set. This
   is the semantics every result is stated against.
3. **Logical machine.** A function's decoded instructions are lifted to an intermediate
   language that is the same for every instruction set. A simulation proof carries every
   run of the lifted program back down to a run of the machine, so whatever is proved
   at this layer holds of the binary.
4. **Program logics** sit on the logical machine, so they are written once rather than once
   per instruction set.
5. **High-level specifications** say what the program computes. They are connected to the
   logic by refinement.

Function specifications compose through a contract table, and the whole program's theorem
is stated over its accepting runs from the loaded image.

## Instruction sets

The framework is built for RISC-V first: the full stack runs there today, on
[riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm)'s model, whose step function is what
SP1 executes. x86-64 and AArch64 are meant to be peers of RISC-V. For now each has only a
machine model, which is trusted until it is verified against its canonical specification. The
ISA-independent layers (the logical machine, the correspondence calculus) are written so that
the rest of the stack can be generalised to them. The plan is in
[`docs/PLAN.md`](docs/PLAN.md), and the choice of specification per instruction set is in
[`docs/ISA.md`](docs/ISA.md).

## Repository map

```
MachineChecked/        the framework (see MachineChecked/README.md)
  Ascent/              correspondence calculus, independent of any ISA
  Lprog/               the logical machine and its simulation down to RISC-V
  RiscV/               the RISC-V stack: judgement, loader, checker, executor, correspondence
  ARM/                 the AArch64 machine model (trusted)
  X86/                 the x86-64 machine model (trusted)
Cases/                 case studies: real binaries, verified (see Cases/README.md)
Tools/                 build-time tools: ELF to Lean, contract inference (see Tools/README.md)
docs/                  design notes, the plan, the trust ladder
```

## Building

The Lean toolchain is pinned in `lean-toolchain` and installed by
[elan](https://github.com/leanprover/elan).

```sh
lake exe cache get              # Mathlib's prebuilt oleans
lake build MachineChecked       # the framework, in minutes
lake build                      # everything, including the case studies (a few hours)
```

To check one file while working, use `lake env lean path/to/File.lean`.

## Documentation

- [`MachineChecked/README.md`](MachineChecked/README.md): the framework, directory by directory.
- [`docs/PLAN.md`](docs/PLAN.md): architecture, phases and the rules every proof follows.
- [`docs/ELF.md`](docs/ELF.md): what the toolchain can tell us and what is trusted (the trust
  ladder, §4).
- [`docs/LogicalMachine.md`](docs/LogicalMachine.md): the design of the intermediate layer.
- [`docs/ISA.md`](docs/ISA.md): the canonical specification for each instruction set.
- [`docs/CATCRYPT-PORT.md`](docs/CATCRYPT-PORT.md): the roadmap for the code ported from
  catcrypt-compiler.

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).
