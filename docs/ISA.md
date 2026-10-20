# A record of the "canonical" ISA specs

## RISCV

the SAIL spec

## x86

Probably use Kraken; possibly the ACL2 (or prove equivalence)

## ARM

?

## Status (2026-10-20)

- RISC-V: riscv-zkvm, tied to Sail. It is the only RV64 semantics here.
- x86-64 and AArch64: CatCrypt's models are ported and trusted for now. The x86 model is
  Sail-tied for the core ALU only, and AArch64 is hand-written. Each is named on the trust
  ladder (`docs/ELF.md` §4) and is to be verified against the canonical spec chosen above.
  A model that is already verified is preferred.
