# MachineChecked

The framework: the semantics a binary is verified against, the layers that make proofs about it
practical, and the bridges between them. Case studies live in `Cases/`; nothing here
depends on them.

## Layout

| directory | what it is | depends on an ISA? |
| --- | --- | --- |
| [`Ascent/`](Ascent/README.md) | The correspondence calculus: a concrete run refines an abstract function. | no |
| [`Lprog/`](Lprog/README.md) | The logical machine. Its syntax and semantics are ISA-independent; `RiscV.lean` and `Lift.lean` are its RISC-V instance and the simulation down to the machine. | core no, instance yes |
| [`RiscV/`](RiscV/README.md) | The RISC-V stack: the judgement, the loader, the contract checker, the symbolic executor and the correspondence on riscv-zkvm. | RISC-V |
| [`ARM/`](ARM/README.md) | The AArch64 machine model (trusted), with `Mem64.lean` its byte memory. | AArch64 |
| [`X86/`](X86/README.md) | The x86-64 machine model (trusted). | x86-64 |

`MachineChecked.lean` imports every module.

## How the pieces fit

```
          specification (in a case study)
                      ▲
                      │  Iface / SafeN contracts, composed by the contract table
                      │
   RiscV/Check ── RiscV/Sym ── RiscV/Corres ── Lprog (Reaches, CorresIsa)
                      │                          │
                      │                          │ lift + simulation (Lprog/Lift)
                      ▼                          ▼
            RiscV/Safe: SafeN over riscv-zkvm's stepSp1
                      ▲
                      │  RiscV/Load, RiscV/Image
                      │
                  the ELF's image
```

- **One judgement.** Every result is stated as `SafeN` over riscv-zkvm's `stepSp1`
  (`RiscV/Safe.lean`): every accepting state reached in fewer than `n` steps satisfies `P`.
  A function's specification is in continuation form, so callers can use it inside an
  induction on the step budget.
- **Several ways to prove one.** The contract checker (`RiscV/Check`) derives structural
  specifications automatically. The symbolic executor (`RiscV/Sym`) proves functional ones.
  The correspondence (`RiscV/Corres`) proves straight-line kernels. The logical machine
  (`Lprog`) proves loops and functions with calls, at a level that does not depend on the ISA.
  They all produce the same judgement, so their results compose.
- **One semantics per ISA.** For RISC-V it is riscv-zkvm, used unmodified. Nothing here
  defines a second RISC-V semantics.

## Instruction sets

RISC-V is built out first. `ARM/` and `X86/` are the AArch64 and x86-64 counterparts of
`RiscV/`. Today each holds only its machine model, and each is to grow the same stack:
loading, the judgement, lifting to `Lprog`, and the checker and executor where they pay off.
The ISA-independent layers (`Ascent/`, the core of `Lprog/`) are what makes that
generalisation a matter of instantiation rather than a rewrite.

## Trust

The trusted base is listed in `docs/ELF.md` §4. Within this directory:
- riscv-zkvm's model (a dependency, tied to Sail) is trusted for RISC-V.
- `ARM/Model.lean` and `X86/JasminModel.lean` are trusted until each is verified against its
  canonical specification (`docs/ISA.md`).
- Everything else is proved. No file uses `sorry`, `axiom` or `native_decide`.

Code ported from catcrypt-compiler records its origin in the module header and in the
directory's `PROVENANCE.md`; the licence it came under is `Ascent/LICENSE-catcrypt`.
