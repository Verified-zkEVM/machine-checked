# RiscV

RISC-V at layers -1 and 0 of the [roadmap](../../ROADMAP.md), the lift to layer 0.5, and the
layer-0 proof tools.

The machine is [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm), a dependency used
unmodified at its pinned commit. Its `stepSp1` is the step SP1 executes, and it is the only
RISC-V semantics in the repository. The execution context is SP1.

## Layer 0: the machine and the judgement

| file | contents |
| --- | --- |
| `Safe.lean` | The judgement every result is stated in. `SafeN G n P s` is `Ascent.SafeN` at `stepSp1`: every accepting state reached from `s` in fewer than `n` steps, along a run whose states all satisfy the guard `G`, satisfies `P`. `stepsSp1` is the generic run (`Ascent.steps`) of `stepSp1`; `SafeN.of_reaches` carries `SafeN` back along a run. |
| `Accept.lean` | The accepting halt (`Accepted`): the `ECALL` with `t0 = 0` and exit code 0 that an SP1 verifier checks. |
| `Accel.lean` | The SP1 accelerators ZIP 2005 uses (`UINT256_MUL`, `PALLAS_ADD`, `PALLAS_DOUBLE`), extracted from riscv-zkvm's dispatch: each one's write and exact trap condition, and the point coordinates `Wire.xOf`/`Wire.yOf`. |

Lemmas for reading a machine state after an update (pc, registers, memory) are in
`lprog-riscv/LprogRiscV/Machine.lean` (namespace `Lprog.RiscV.Machine`), because RISC-V's
Lprog instance depends on them.

## Layer -1: loading

| file | contents |
| --- | --- |
| `Image.lean` | An image's code as 32-bit words, decoded by riscv-zkvm's own `decode`. |
| `Load.lean` | A total, kernel-evaluable loader: the state an SP1 guest starts in, built from an image. |

## Lifts and the decompiler

| directory | contents |
| --- | --- |
| [`Lift/`](Lift/README.md) | Lift 1 (`liftProg`) and the simulation that carries Lprog runs down to `stepSp1`. The intended route for new proofs. Also the unproved lifts of whole programs (`Whole.lean`, for rustc output) and of code without functions (`Flat.lean`). |
| [`Sp1/`](Sp1/README.md) | An SP1 guest ELF as a Pancake program, via `Lift/Whole.lean` and lift 2. |
| [`Flapjack/`](Flapjack/README.md) | A binary from Flapjack, the Pancake compiler, as an Lprog program and, via lift 2, as Pancake again. |
| [`LIMITS.md`](LIMITS.md) | What the decompiler does and does not do on RISC-V. |

The per-instruction translation (`rvIsa`), proved against riscv-zkvm, is in the package
[`lprog-riscv`](../../lprog-riscv/README.md).

## Layer-0 proof tools

These prove facts about the machine directly, without the lift. They were built for zip-2005
and proved most of it while it was a case study here (the tree at tag `with-zip2005`). Their
results are `SafeN` facts in the contract table, so they compose
with results proved through the lift. Whether they move up to layer 0.5 or 1, or remain a
fallback for what the lift does not cover, is an open question in the roadmap.

| directory | what it does |
| --- | --- |
| [`Frame/`](Frame/README.md) | Return-address integrity for one function activation, computed and proved sound. |
| [`Check/`](Check/README.md) | The contract checker: a Boolean check, proved sound against `stepSp1`, that a function meets its interface. Derives structural specifications (frame, footprint, callee-saved registers, stack bounds) for every function, with `Tools/Infer.lean`. |
| [`Exec/`](Exec/README.md) | Hand proofs of interfaces the checker cannot derive, against the same judgement. |
| [`Sym/`](Sym/README.md) | The symbolic executor `sym_exec`, which proves functional specifications by stepping the machine. `Sym.lean` imports it. |

This directory is the template for [`../ARM`](../ARM/README.md) and [`../X86`](../X86/README.md),
which so far have only the semantics and an unproved lift.
