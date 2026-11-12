# The canonical specification of each instruction set

Each instruction set's model is the bottom of its stack (layer 0 of
[`ROADMAP.md`](../ROADMAP.md)): the semantics every theorem about a binary for that ISA is
stated against. A model is trusted only while it is named on the trust ladder
([`ELF.md`](ELF.md) §4), and is to be verified against the canonical specification chosen
here, or replaced by a model that already is.

| ISA | canonical specification | model here | status |
| --- | --- | --- | --- |
| RISC-V | the Sail RISC-V model | [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm), a dependency | tied to Sail; the only RV64 semantics |
| x86-64 | [Kraken](https://github.com/AeneasVerif/kraken)'s x64 semantics (decided 2026-11-11, below) | `MachineChecked/X86/Model.lean`, a transcription of Jasmin's x86 semantics, until Kraken is required | trusted |
| AArch64 | [DeepMind's arm64-semantics](https://github.com/google-deepmind/code-verification/tree/main/arm64-semantics) (decided 2026-11-12, below) | `MachineChecked/ARM/Model.lean`, hand-written, until arm64-semantics is required | trusted |

## x86-64: Kraken

**Decided 2026-11-11, with catcrypt-compiler's maintainers.** The x86-64 semantics is
[Kraken](https://github.com/AeneasVerif/kraken)'s x64 model (Lean FRO, Google and INRIA; MIT).
It plays the part riscv-zkvm plays for RISC-V: a dependency, required at a pinned revision
and used unmodified, and the only x86-64 semantics here. Any other x86-64 model, such as
catcrypt-compiler's, is proved against it rather than set beside it.

Why Kraken rather than Sail x86 or the ACL2 model: it is in Lean, its semantics is written by
hand for both proof and testing, each change to it is checked against the Intel SDM by two
maintainers, it is tested against Intel's SDE by a fuzzer, and it is built for proof
automation (`SymM`, `grind`, `mvcgen`).

What it changes, compared with RISC-V:

- **Its programs are assembly, not bytes.** Kraken verifies code one level above the binary,
  `.S` files or disassembled `.o` files, with no layout, instruction sizes or addresses. An
  x86-64 theorem here is therefore stated over the assembly, and the assembler and linker
  join the trusted base for x86-64 (`ELF.md` §4). Closing that gap (checking the assembly
  against the bytes of the binary) is later work.
- **Its scope** is sequential user-level code in 64-bit mode: all general-purpose registers
  with partial-register access, status flags, memory, ADX and `MULX`. Faults, virtual memory,
  segment registers, other modes and mutable globals (`.data`, `.bss`) are out of scope. The
  first x86-64 targets (s2n-bignum-style routines, hash kernels) fit inside it.
  Instructions it lacks (for example the rest of BMI1 and BMI2, `BT`, `XCHG`) are
  contributed to Kraken when a target needs them.
- **Toolchain.** Kraken follows Lean nightlies and the module system; requiring it moves this
  repository's toolchain (see `ROADMAP.md`).

Until Kraken is required, `MachineChecked/X86/Model.lean` stays, trusted and unused. It is
removed when Kraken comes in.

## AArch64: DeepMind's arm64-semantics

**Decided 2026-11-12.** The AArch64 semantics is the trusted package `arm64` of
[arm64-semantics](https://github.com/google-deepmind/code-verification/tree/main/arm64-semantics) (Google DeepMind's code-verification repository; Apache-2.0): its
`Arm64.Steps` relation, decoder, memory and state (`Arm64/Trusted/ISA/`). It plays the part
riscv-zkvm plays for RISC-V: a dependency, required at a pinned commit and used unmodified, and
the only AArch64 semantics here.

Why it rather than sail-arm or Kraken's AArch64 model:

- **Its programs are bytes, as RISC-V's are.** `Step` fetches four bytes from memory, decodes
  them and executes the instruction, so an AArch64 theorem is stated over the binary, with no
  assembler or linker in the trusted base. That is the RISC-V shape, not Kraken's.
- **Its trusted part is small and checked.** It is written by hand from Arm's machine-readable
  ASL, kept theorem-free, and differentially tested against Sail's Armv9.4-A model, Unicorn,
  LLVM, `ld.lld` and QEMU. The encoder round trip (`encode (decode bs) = bs`) is proved.
- **Its coverage fits our targets.** Beyond the integer core, it covers the SIMD loads and
  stores and the crypto extensions (AES, SHA-1/256/512, `PMULL`, and SHA-3's `EOR3`, `RAX1`,
  `XAR`, `BCAX`).

Sail-arm, generated from the ASL itself, stays the reference arm64-semantics is tested
against, not a second semantics here.

What to know about it:

- **Its scope** is one hardware thread at EL0 running Linux user code. A fault is a status that
  stops execution, not a trap. Anything not modelled, including unmodelled system registers
  and syscalls, faults rather than guesses. The exclusive monitor is not modelled, and `FPCR`
  is pinned to zero.
- **What is required:** only the trusted package (`arm64-semantics/Arm64`, Lake package
  `arm64`, no dependencies). Its proof library `ProofLib`, case studies and tests are not
  required.
- **Toolchain.** It pins Lean v4.34.0 and builds warning-free on v4.36.0-rc2 (checked
  2026-11-12). It uses the module system, as Kraken does.

Until arm64-semantics is required, `MachineChecked/ARM/Model.lean` stays, trusted and unused.
It is removed when arm64-semantics comes in.
