# MachineChecked

The framework: the semantics a binary is verified against, the layers that make proofs about it
practical, and the verified lifts between them. Case studies live in `Cases/`; nothing here
depends on them.

## The layers, and where they live

[`ROADMAP.md`](../ROADMAP.md) describes the framework as a stack of layers. A binary enters at
the bottom and is lifted upward; a specification enters at the top and is refined downward.
This is where each layer is in the code today.

```
  layer 2     spec refinement           Refine/        not started (README only)
                    ▲ refinement
  layer 1     structured logical prog.  Logical/       not started (README only)
                    ▲ lift 2: decompilation
  layer 0.5   low logical program       Lprog/         ISA-independent: syntax, semantics,
                                                       shared operations
                    ▲ lift 1: translation
                                        RiscV/Lprog/   the RISC-V lift and its simulation
  layer 0     ISA                       RiscV/         riscv-zkvm's stepSp1, the judgement
                                        ARM/, X86/     machine models only (trusted)
                    ▲ loading
  layer -1    ELF and context           RiscV/         loader, image, SP1's acceptance and
                                                       syscalls

  across the layers                     Ascent/        runs and correspondence, for any step
```

| directory | layer | what it is | depends on an ISA? |
| --- | --- | --- | --- |
| [`Ascent/`](Ascent/README.md) | all | Runs of any step function (`steps`, `Reaches`) and the correspondence of a machine with an abstract function (`Corres`). Every layer's runs are instances, so the lifts carry `Reaches` to `Reaches`. | no |
| [`Lprog/`](Lprog/README.md) | 0.5 | The low logical program: linear Jasmin with labels, registers and flat memory, and operations shared by every ISA (`Op.lean`). | no |
| [`RiscV/Lprog/`](RiscV/Lprog/README.md) | 0 → 0.5 | The RISC-V lift: each instruction translated to a shared operation, proved against riscv-zkvm, and the simulation that carries every Lprog run down to `stepSp1`. | RISC-V |
| [`RiscV/`](RiscV/README.md) | 0, -1 | riscv-zkvm's machine, the judgement `SafeN`, the loader and SP1's context, and the layer-0 proof tools (`Check`, `Sym`, `Frame`, `Exec`). | RISC-V |
| [`ARM/`](ARM/README.md) | 0 | The AArch64 machine model (trusted). | AArch64 |
| [`X86/`](X86/README.md) | 0 | The x86-64 machine model (trusted). | x86-64 |
| [`Logical/`](Logical/README.md) | 1 | Placeholder: the structured logical program. | no |
| [`Refine/`](Refine/README.md) | 2 | Placeholder: specification refinement. | no |

`MachineChecked.lean` imports every module.

## How a proof goes today

The final theorem is always stated at layer 0, as `SafeN` over riscv-zkvm's `stepSp1`
(`RiscV/Safe.lean`), from the state the loader builds for the ELF. Proofs reach it in one of
two ways:

- **Through the lift** (the intended route). A function's decoded instructions are lifted to
  an Lprog body (`RiscV/Lprog/Lift.lean`), the body is run at Lprog with the `reaches_*`
  rules, and the run is carried down to `stepSp1` by the simulation (`reach_of_halts`,
  `SafeN.of_lift`). The CatCrypt kernels (`Cases/CatCrypt`) and three zip-2005 functions are
  proved this way.
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

The trusted base is listed in [`docs/ELF.md`](../docs/ELF.md) §4. Within this directory:
- riscv-zkvm's model (a dependency, tied to Sail) is trusted for RISC-V.
- `ARM/Model.lean` and `X86/Model.lean` are trusted until each is verified against its
  canonical specification ([`docs/ISA.md`](../docs/ISA.md)).
- Everything else is proved. No file uses `sorry`, `axiom` or `native_decide`.

Code ported from catcrypt-compiler records its origin in the module header and in the
directory's `PROVENANCE.md`; the licence it came under is `Ascent/LICENSE-catcrypt`.
