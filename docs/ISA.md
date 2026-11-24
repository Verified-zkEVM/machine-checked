# The instruction-set models

Which semantics each instruction set is verified against, and why. This is current. Each model
is layer 0 of [`ROADMAP.md`](../ROADMAP.md): every theorem about a binary for that ISA is
stated against it. A model is trusted only as listed on the trust ladder
([`ELF.md`](ELF.md) §4), and is to be verified against the canonical specification named here,
or be that specification.

| ISA | canonical specification | model used here | status |
| --- | --- | --- | --- |
| RISC-V | the Sail RISC-V model | [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm) | tied to Sail; the only RV64 semantics here |
| x86-64 | [Kraken](https://github.com/AeneasVerif/kraken)'s x64 semantics | Kraken, imported by `MachineChecked/X86/Kraken.lean` | trusted as the canonical specification |
| AArch64 | [DeepMind's arm64-semantics](https://github.com/google-deepmind/code-verification/tree/main/arm64-semantics) | its trusted package `arm64`, imported by `MachineChecked/ARM/Arm64.lean` | trusted as the canonical specification |

Each model is a dependency, required at a pinned commit in `lakefile.toml` and used
unmodified. It is the only semantics for its ISA in this repository. Any other model of the
same ISA (for example catcrypt-compiler's) must be proved against it, not used beside it.

## x86-64: Kraken

Chosen on 2026-11-11, with catcrypt-compiler's maintainers. Kraken's x64 model is by the
Lean FRO, Google and INRIA (MIT licence). It was chosen over Sail x86 and the ACL2 model
because it is in Lean, its semantics is hand-written for both proof and testing, each change
is checked against the Intel SDM by two maintainers, it is fuzz-tested against Intel's SDE,
and it is built for proof automation (`SymM`, `grind`, `mvcgen`).

How it differs from RISC-V:

- **Programs are assembly, not bytes.** Kraken verifies `.S` files or disassembled `.o` files,
  with no layout, instruction sizes or addresses. An x86-64 theorem here is therefore stated
  over the assembly, and the assembler and linker are trusted for x86-64 (`ELF.md` §4).
  Checking the assembly against the binary's bytes is future work.
- **Scope:** sequential user-level code in 64-bit mode: all general-purpose registers with
  partial-register access, status flags, memory, ADX and `MULX`. Out of scope: faults,
  virtual memory, segment registers, other modes, and mutable globals (`.data`, `.bss`). The
  first x86-64 targets (s2n-bignum-style routines, hash kernels) fit in this scope. Missing
  instructions (for example the rest of BMI1 and BMI2, `BT`, `XCHG`) are to be contributed to
  Kraken when a target needs them.
- **Toolchain:** Kraken follows Lean nightlies and uses the module system. It does not build on
  Lean v4.35.0; this repository uses v4.36.0.

`MachineChecked/X86/Kraken.lean` imports `Kraken.X64.Semantics` and nothing else from Kraken.
It replaces the transcription of Jasmin's x86 semantics used before.

## AArch64: DeepMind's arm64-semantics

Chosen on 2026-11-12. The model is the trusted package `arm64` of arm64-semantics, in Google
DeepMind's code-verification repository (Apache-2.0): its `Step`/`Steps` relations, decoder,
memory and state (under `Arm64/Trusted/ISA/`). It was chosen over sail-arm and Kraken's
AArch64 model for three reasons:

- **Programs are bytes, as for RISC-V.** `Step` fetches four bytes from memory, decodes them
  and executes the instruction. An AArch64 theorem is stated over the binary, with no
  assembler or linker in the trusted base.
- **The trusted part is small and checked.** It is written by hand from Arm's
  machine-readable ASL and contains no theorems. It is differentially tested against Sail's
  Armv9.4-A model, Unicorn, LLVM, `ld.lld` and QEMU. The encoder round trip
  (`encode (decode bs) = bs`) is proved.
- **Coverage fits the targets.** Besides the integer core, it covers SIMD loads and stores and
  the crypto extensions (AES, SHA-1/256/512, `PMULL`, and SHA-3's `EOR3`, `RAX1`, `XAR`,
  `BCAX`).

Sail-arm, generated from the ASL, remains the reference that arm64-semantics is tested
against; it is not a second semantics here.

Limits and requirements:

- **Scope:** one hardware thread at EL0 running Linux user code. A fault is a status that
  stops execution, not a trap. Anything not modelled, including unmodelled system registers
  and syscalls, faults rather than guesses. The exclusive monitor is not modelled, and `FPCR`
  is fixed at zero.
- **What is required:** only the trusted package (`arm64-semantics/Arm64`, Lake package
  `arm64`, no dependencies), via `subDir` in `lakefile.toml`. Its proof library `ProofLib`,
  case studies and tests are not required.
- **Toolchain:** it pins Lean v4.34.0 and builds without warnings on v4.36.0-rc2 (checked
  2026-11-12). It uses the module system.

`MachineChecked/ARM/Arm64.lean` imports `Arm64.Trusted`. It replaces the hand-written model
ported from catcrypt-compiler used before.
