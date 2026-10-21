# RiscV

The RISC-V stack: everything between a loaded RV64 image and a function's specification. The
machine is [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm), a dependency used
unmodified at its pin. Its `stepSp1` is the step SP1 executes, and it is the only RISC-V
semantics in the repository.

## The base

| file | contents |
| --- | --- |
| `Safe.lean` | The judgement every result is written in. `SafeN G n P s`: every accepting state reached from `s` in fewer than `n` steps, along a run every state of which satisfies the guard `G`, satisfies `P`. |
| `Accept.lean` | The accepting halt (`Accepted`): the `ECALL` with `t0 = 0` and exit code 0 that an SP1 verifier checks. |
| `Image.lean` | An image's code as 32-bit words, decoded by riscv-zkvm's own `decode`. |
| `Load.lean` | A total, kernel-evaluable loader: the state an SP1 guest starts in, built from an image. |
| `Corres.lean` | The ascent's `CorresM` at `stepsSp1`, and the bridges into `SafeN` (`SafeN.of_corres`, `SafeN.of_fn`, `Check.Iface.holds_of_corres`). |

## The tools

| directory | what it does |
| --- | --- |
| [`Frame/`](Frame/README.md) | Frame analysis: return-address integrity for one function activation, computed and proved sound. |
| [`Check/`](Check/README.md) | The contract checker: from code, an untrusted annotation and callee interfaces, a Boolean check that a function meets its interface, proved sound against `stepSp1`. |
| [`Exec/`](Exec/README.md) | Hand proofs of interfaces the checker cannot derive, against the same judgement. |
| [`Sym/`](Sym/README.md) | The symbolic executor `sym_exec`, which proves functional specifications by stepping the machine. |
| [`Corres/`](Corres/README.md) | Correspondence tooling on `stepSp1`: straight-line blocks, register valuations, runs, calls and loops. |

`Sym.lean` imports the executor. The logical machine's RISC-V instance is in
`../Lprog/RiscV.lean` and `../Lprog/Lift.lean`.

## Choosing a tool

- **Structural facts** (frame, footprint, callee-saved registers, stack bounds) come from
  `Check/`, generated for every function by `Tools/Infer.lean`.
- **What a function computes**, for compiled code with stack frames: `Sym/`.
- **Register-only kernels**: `Corres/`, with `regs_run` and `bv_decide`.
- **Loops over all inputs, and functions with calls**, at an ISA-independent level:
  `../Lprog`.

Every tool produces the continuation form of `SafeN`, so results compose through the
contract table whichever tool proved them.

This directory is the template for the other instruction sets: `../ARM` and `../X86` are to
grow their own counterparts of it.
