# MachineChecked

The framework: the semantics a binary is verified against, the layers that make proofs about it
practical, and the verified lifts between them. Case studies live in `Cases/`; nothing here
depends on them.

## The layers, and where they live

[`ROADMAP.md`](../ROADMAP.md) describes the framework as a stack of layers. A binary enters at
the bottom and is lifted upward; a specification enters at the top and is refined downward.
This is where each layer is in the code today.

Four Lake packages hold it ([`docs/design/Packages.md`](../docs/design/Packages.md)): this
directory is the root package's; Lprog and the semantics around it are the package
[`lprog`](../lprog/README.md) (modules `Lprog.*`, requiring nothing); RISC-V at Lprog is
[`lprog-riscv`](../lprog-riscv/README.md) (modules `LprogRiscV.*`, declarations in
`Lprog.RiscV`, on riscv-zkvm); and Pancake as the decompiler writes it is
[`pancake`](../pancake/README.md) (modules `Pancake.*`, on Flapjack's syntax). A proof about a
decompiled program needs only those.

```
  layer 2     spec refinement           Refine/              not started (README only)
                    ▲ refinement
  layer 1     structured logical prog.  Logical/             Pancake; lift 2, not proved
                    ▲ lift 2: decompilation
  layer 0.5   low logical program       lprog: Lprog/        ISA-independent: syntax, semantics,
                                                             shared operations; AArch64's and
                                                             x86-64's registers
                                        lprog-riscv          RISC-V's registers, its instance,
                                                             SP1's execution context
                    ▲ lift 1: translation
                                        RiscV/Lift/          the RISC-V lift and its simulation
                                        ARM/Lift/, X86/Lift/ the AArch64 and x86-64 lifts
                                        RiscV/Flapjack/      a Flapjack image and its layout
                                        RiscV/Sp1/           an SP1 guest, on to Pancake
  layer 0     ISA                       RiscV/               riscv-zkvm's stepSp1, the judgement
                                        ARM/, X86/           semantics only (dependencies)
                    ▲ loading
  layer -1    ELF and context           RiscV/               loader, image, SP1's acceptance and
                                                             syscalls

  across the layers                     lprog: Lprog/Ascent/ runs and correspondence, for any step
```

| where | layer | what it is | depends on an ISA? |
| --- | --- | --- | --- |
| [`lprog/Lprog/Ascent/`](../lprog/Lprog/Ascent/README.md) | all | Runs of any step function (`steps`, `Reaches`) and the correspondence of a machine with an abstract function (`Corres`). Every layer's runs are instances, so the lifts carry `Reaches` to `Reaches`. In the package `lprog`. | no |
| [`lprog/Lprog/`](../lprog/Lprog/README.md) | 0.5 | The low logical program: linear Jasmin with labels, registers and flat memory, and operations shared by every ISA (`Op.lean`); the registers of AArch64 and x86-64. The package `lprog`. | no |
| [`lprog-riscv/`](../lprog-riscv/README.md) | 0.5 | RISC-V at Lprog: the facts about riscv-zkvm's machine it rests on, each instruction translated to a shared operation and proved against riscv-zkvm (`Instance.lean`), SP1's execution context and its `ecall`. | RISC-V |
| [`RiscV/Lift/`](RiscV/Lift/README.md) | 0 → 0.5 | The RISC-V lift and the simulation that carries every Lprog run down to `stepSp1`. | RISC-V |
| [`RiscV/`](RiscV/README.md) | 0, -1 | riscv-zkvm's machine, the judgement `SafeN`, the loader and SP1's context, and the layer-0 proof tools (`Check`, `Sym`, `Frame`, `Exec`). | RISC-V |
| [`ARM/`](ARM/README.md) | 0, 0 → 0.5 | The AArch64 semantics (DeepMind's arm64-semantics, a dependency) and its lift (`ARM/Lift/`). | AArch64 |
| [`X86/`](X86/README.md) | 0, 0 → 0.5 | The x86-64 semantics (Kraken's x64 model, a dependency), its decoder and its lift (`X86/Lift/`). | x86-64 |
| [`Logical/`](Logical/README.md) | 0.5 → 1 | Pancake as text, and lift 2: an Lprog program as a Pancake program, a function for each function, structured where its control flow is. Not proved; checked by running. | no |
| [`Refine/`](Refine/README.md) | 2 | Placeholder: specification refinement. | no |

`MachineChecked.lean` imports every module of the four packages.

## How a proof goes today

The final theorem is always stated at layer 0, as `SafeN` over riscv-zkvm's `stepSp1`
(`RiscV/Safe.lean`), from the state the loader builds for the ELF. Proofs reach it in one of
two ways:

- **Through the lift** (the intended route). A function's decoded instructions are lifted to
  an Lprog body (`RiscV/Lift/Lift.lean`), a contract is proved for it at Lprog with the
  rules of `lprog/Lprog/Sem.lean` and `RiscV/Lift/Rules.lean`, and the transfer theorem carries it
  down to `stepSp1` (`RiscV/Lift/Transfer.lean`, `SafeN.of_contract`). Three zip-2005
  functions are proved this way; the CatCrypt kernels (`Cases/CatCrypt`) are straight-line
  blocks, proved over the machine with `RiscV/Lift/Block.lean`.
- **With the layer-0 tools.** The contract checker (`RiscV/Check`) derives structural
  specifications for every function; the symbolic executor (`RiscV/Sym`) and hand proofs
  (`RiscV/Exec`) prove functional ones over the machine. Most of zip-2005 is proved this way;
  it predates the lift. Whether these tools move up onto the lift, or stay as a fallback for
  what the lift does not cover, is an open question of the roadmap.

Both produce the continuation form of `SafeN`, so their results compose through the contract
table ([`docs/Architecture.md`](../docs/Architecture.md)).

Layers 1 and 2 do not exist yet. Today each case study's specification (for example
`Cases/Zip2005/Spec`) is connected to its proofs directly.

## Trust

The trusted base is listed in [`docs/ELF.md`](../docs/ELF.md) §4. Within this directory and the
packages `lprog` and `lprog-riscv`:
- riscv-zkvm's model (a dependency, tied to Sail) is trusted for RISC-V.
- Kraken's x64 semantics and arm64-semantics' trusted package (dependencies) are trusted for
  x86-64 and AArch64 ([`docs/ISA.md`](../docs/ISA.md)).
- Everything else is proved. No file uses `sorry`, `axiom` or `native_decide`.

Code ported from catcrypt-compiler records its origin in the module header and in the
directory's `PROVENANCE.md`; the licence it came under is
[`lprog/Lprog/Ascent/LICENSE-catcrypt`](../lprog/Lprog/Ascent/LICENSE-catcrypt).
