# The canonical specification of each instruction set

Each instruction set's model is the bottom of its stack (layer 0 of
[`ROADMAP.md`](../ROADMAP.md)): the semantics every theorem about a binary for that ISA is
stated against. A model is trusted only while it is named on the trust ladder
([`ELF.md`](ELF.md) §4), and is to be verified against the canonical specification chosen
here, or replaced by a model that already is.

| ISA | canonical specification | model here | status |
| --- | --- | --- | --- |
| RISC-V | the Sail RISC-V model | [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm), a dependency | tied to Sail; the only RV64 semantics |
| x86-64 | undecided: Sail x86, the ACL2 x86 model, or Kraken (or an equivalence between them) | `MachineChecked/X86/Model.lean`, a transcription of Jasmin's x86 semantics | trusted |
| AArch64 | undecided; the natural candidate is sail-arm, generated from Arm's own ASL | `MachineChecked/ARM/Model.lean`, hand-written | trusted |

Choosing Sail for all three would make "verified against the canonical specification" mean
the same thing on every ISA, and there is already a pipeline from Sail to Lean for RISC-V.
The cost is that the x86 and ARM Sail models are very large. The choice is open for
discussion.
