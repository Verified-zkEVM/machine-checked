# ASM-VERIF: formally verify machine code directly in Lean

The basic pipeline:

```
┌────────────────────────┐                      ┌──────────────────────────────┐
│ Source (Rust, C, etc.) │                      │      Formal Specification    │
└────────────────────────┘                      └───────────────┬──────────────┘
             │                                                  ▲
             │                                                  │
             │                                                  ▲
             │                                                  │
             │                                                  ▲
             │                                                  |
             ▼                                                  ▲
┌────────────┴───────────┐                      ┌───────────────┴──────────────┐
│  ELF (riscv, x86, ARM) │───── elf2lean ──────►│     decoded instructions     │
└────────────────────────┘                      └──────────────────────────────┘
```

## Supports 

* RiscV, x86, ARM

(open question on how context-aware this needs to be)

```
        :                  :                  :       
┌───────┴──────┐   ┌───────┴──────┐   ┌───────┴──────┐
|    riscv     |   |      x86     |   |      arm     |
└──────────────┘   └──────────────┘   └──────────────┘
        /\                /\                  /\
┌───────┐┌───────┐
|  SP1  || Zisk  |        ...                 ...
└───────┘└───────┘
```

## The Framework

```
                        CRYPTOGRAPHIC THEOREMS
            ┌─────────────────────────────────────┐
            │ XMSS security / quantum recovery /  │
            │ collision resistance assumptions    │
            └──────────────────┬──────────────────┘
                               │
                         ALGORITHM SPEC
            ┌──────────────────┴──────────────────┐
            │ SHA256.compress                     │
            │ XMSS.verify                         │
            │ WOTS.verify                         │
            └──────────────────┬──────────────────┘
                               │ refinement
                      PROGRAM LOGIC(S)
            ┌──────────────────┴──────────────────┐
            │ Hoare / refinement / separation    │
            │ relational / cost / informationflow│
            └──────────────────┬──────────────────┘
                               │
                     LOGICAL MACHINE PROGRAM
            ┌──────────────────┴──────────────────┐
            │ variables + CFG + expressions       │
            │ loads/stores + effects              │
            └──────────────────┬──────────────────┘
                               │
                        logical decompilation
                       + simulation invariant
                               │
                      ARCHITECTURAL PROGRAM
            ┌──────────────────┴──────────────────┐
            │ PC + registers + memory + ISA       │
            └──────────────────┬──────────────────┘
                               │
                          ELF LOADING
                               │
                              ELF
```

## Strategies

- TODO proof optimised, formally verified interpreters for each of riscv, x86, and arm
    - each is formally verified wrt the canonical spec (e.g. [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm); the specs are in [docs/ISA.md](docs/ISA.md)).
    - the interpreter should be speicalized in some sense for proof-friendliness (whatever that means exactly)
- TODO a strategy for dealing with the ELF (we can tolerate some trust to the compiler - fine);
    - preferably, a generic framework that handles ELFs so that we can focus verification on the bytecode in question
    - USE the debug mode of the e.g. rustc compiler to gain information about the ELF
- TODO a "decompile" strategy, inspired by:
    - [ascent](https://github.com/sgraf812/ascent/tree/master/Ascent) - probably want to be compatible with this in perpetuity (and move with any updates to it)
    - [evm-asm](https://github.com/Verified-zkEVM/evm-asm)
    - [zip-2005-asm](https://github.com/dhsorens/zip-2005-asm/)

## The idea

- import an ELF spit out by a compiler 
- write a high-level formal spec
- an agent ascends from the bytecode to the formal spec (the spec is also refined)
    - there are well thought-out skills for adversarial formal verification

## Scripts

ELF2Lean can take an ELF 

## Future

Integrate CLEAN for specs + asm verification for zkVM precompiles? (Maybe not)