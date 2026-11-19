# MachineChecked

The framework: the machine semantics a binary is verified against, the layers that make proofs
about it practical, and the lifts between them. Case studies are in `Cases/`; nothing here
depends on them.

## Layers and packages

[`ROADMAP.md`](../ROADMAP.md) describes the framework as a stack of layers. A binary enters at
the bottom and is lifted upward; a specification enters at the top and is refined downward.

The code is split across four Lake packages ([`docs/design/Packages.md`](../docs/design/Packages.md)):

| package | modules | contents | requires |
| --- | --- | --- | --- |
| root (`machine-checked`) | `MachineChecked.*` | this directory: ISA semantics, lifts, proof tools | all of the below |
| [`lprog`](../lprog/README.md) | `Lprog.*` | Lprog and the generic semantics (`Lprog.Ascent`) | nothing |
| [`lprog-riscv`](../lprog-riscv/README.md) | `LprogRiscV.*` (declarations in `Lprog.RiscV`) | RISC-V at Lprog | `lprog`, riscv-zkvm |
| [`pancake`](../pancake/README.md) | `Pancake.*` | Pancake as the decompiler writes it | Flapjack |

The last three are meant to be all a proof about a decompiled program needs. Today the modules
`decompile --to lean` writes also import `Tools.ToLean` and the RISC-V lift from the root
package ([`docs/design/Packages.md`](../docs/design/Packages.md)).

```
  layer 2     spec refinement           Refine/              not started
                    ▲ refinement
  layer 1     structured logical prog.  Logical/             Pancake; lift 2, not proved
                    ▲ lift 2: decompilation
  layer 0.5   low logical program       lprog: Lprog/        syntax, semantics, shared operations;
                                                             AArch64 and x86-64 registers
                                        lprog-riscv          RISC-V registers and instance,
                                                             SP1's execution context
                    ▲ lift 1: translation
                                        RiscV/Lift/          RISC-V lift and its simulation
                                        ARM/Lift/, X86/Lift/ AArch64 and x86-64 lifts (unproved)
                                        RiscV/Flapjack/      Flapjack images
                                        RiscV/Sp1/           SP1 guests, to Pancake
  layer 0     ISA                       RiscV/               riscv-zkvm's stepSp1, the judgement
                                        ARM/, X86/           semantics only (dependencies)
                    ▲ loading
  layer -1    ELF and context           RiscV/               loader, image, SP1 acceptance and
                                                             syscalls

  all layers                            lprog: Lprog/Ascent/ runs and correspondence, any step
```

| where | layer | contents | ISA |
| --- | --- | --- | --- |
| [`lprog/Lprog/Ascent/`](../lprog/Lprog/Ascent/README.md) | all | Runs of any step function (`steps`, `Reaches`), the judgement `SafeN`, refinement, and correspondence (`Corres`). Every layer's runs are instances, so lifts carry results between layers. | none |
| [`lprog/Lprog/`](../lprog/Lprog/README.md) | 0.5 | The low logical program: linear Jasmin with labels, registers and flat memory; the operations every ISA shares (`Op.lean`); AArch64 and x86-64 registers. | none |
| [`lprog-riscv/`](../lprog-riscv/README.md) | 0.5 | RISC-V as an Lprog instruction set, each instruction proved against riscv-zkvm (`Instance.lean`); SP1's execution context and `ecall`. | RISC-V |
| [`RiscV/Lift/`](RiscV/Lift/README.md) | 0 → 0.5 | The RISC-V lift and the simulation that carries every Lprog run down to `stepSp1`. | RISC-V |
| [`RiscV/`](RiscV/README.md) | 0, -1 | riscv-zkvm's machine, the judgement `SafeN`, the loader, SP1's context, and the layer-0 proof tools (`Check`, `Sym`, `Frame`, `Exec`). | RISC-V |
| [`ARM/`](ARM/README.md) | 0, 0 → 0.5 | AArch64 semantics (DeepMind's arm64-semantics, a dependency) and an unproved lift. | AArch64 |
| [`X86/`](X86/README.md) | 0, 0 → 0.5 | x86-64 semantics (Kraken's x64 model, a dependency), a decoder, and an unproved lift. | x86-64 |
| [`Logical/`](Logical/README.md) | 0.5 → 1 | Lift 2: an Lprog program as a structured Pancake program. Not proved; tested by running. | none |
| [`Refine/`](Refine/README.md) | 2 | Placeholder for specification refinement. | none |

`MachineChecked.lean` imports every module of the four packages.

## How a proof goes today

The final theorem is always stated at layer 0, as `SafeN` over riscv-zkvm's `stepSp1`
(`RiscV/Safe.lean`), from the state the loader builds for the ELF. There are two routes to it:

- **Through the lift** (the intended route). A function's decoded instructions are lifted to
  an Lprog body (`RiscV/Lift/Lift.lean`). A contract is proved for the body with the rules of
  `lprog/Lprog/Sem.lean` and `RiscV/Lift/Rules.lean`, and the transfer theorem carries it down
  to `stepSp1` (`RiscV/Lift/Transfer.lean`, `SafeN.of_contract`). The functions of
  `Cases/Hardening` are proved this way, with `lsym` applying the rules. A straight-line
  block can be proved over the machine with `RiscV/Lift/Block.lean`.
- **With the layer-0 tools.** The contract checker (`RiscV/Check`) derives structural
  specifications for every function. The symbolic executor (`RiscV/Sym`) and hand proofs
  (`RiscV/Exec`) prove functional specifications directly over the machine. Most of zip-2005
  was proved this way while it was a case study here (the tree at tag `with-zip2005`).
  Whether these tools move up onto the lift or remain a fallback is an open question in the
  roadmap.

Both routes produce `SafeN` in continuation form, so their results compose through the
contract table ([`docs/Architecture.md`](../docs/Architecture.md)).

Layers 1 and 2 do not exist yet. Each case study connects its specification to its proofs
directly.

## Trust

The full trusted base is in [`docs/ELF.md`](../docs/ELF.md) §4. For this directory and the
packages `lprog` and `lprog-riscv`:

- Trusted: riscv-zkvm's model (tied to Sail) for RISC-V; Kraken's x64 semantics and the
  trusted package of arm64-semantics for x86-64 and AArch64 ([`docs/ISA.md`](../docs/ISA.md)).
  All are dependencies.
- Everything else is proved. No file uses `sorry`, `axiom` or `native_decide`.
- Some code has no proofs and no theorem depends on it: the RISC-V lifts of whole programs
  and of flat code, the AArch64 and x86-64 lifts, and lift 2. The decompiler built from them
  is tested by running ([`scripts/decompile-check`](../scripts/decompile-check/README.md)).

Code ported from catcrypt-compiler records its origin in its module header and in
[`lprog/Lprog/Ascent/PROVENANCE.md`](../lprog/Lprog/Ascent/PROVENANCE.md); its licence is
[`lprog/Lprog/Ascent/LICENSE-catcrypt`](../lprog/Lprog/Ascent/LICENSE-catcrypt).
