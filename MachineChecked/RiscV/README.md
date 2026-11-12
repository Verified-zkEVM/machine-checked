# RiscV

**Layers 0 and -1 of the [roadmap](../../ROADMAP.md) for RISC-V**, and the lift to layer 0.5.

The machine is [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm), a dependency used
unmodified at its pin. Its `stepSp1` is the step SP1 executes, and it is the only RISC-V
semantics in the repository. The execution context is SP1.

## Layer 0: the machine and the judgement

| file | contents |
| --- | --- |
| `State.lean` | Reading a machine state after an update: the pc, registers after register and memory writes, a normal form. |
| `Safe.lean` | The judgement every result is written in. `SafeN G n P s`, the instance of `Ascent.SafeN` at `stepSp1`: every accepting state reached from `s` in fewer than `n` steps, along a run every state of which satisfies the guard `G`, satisfies `P`. `stepsSp1` is the generic run (`Ascent.steps`) of `stepSp1`, and `SafeN.of_reaches` passes `SafeN` back along a run. |
| `Accept.lean` | The accepting halt (`Accepted`): the `ECALL` with `t0 = 0` and exit code 0 that an SP1 verifier checks. |
| `Accel.lean` | The SP1 accelerator arms ZIP 2005 uses (`UINT256_MUL`, `PALLAS_ADD`, `PALLAS_DOUBLE`), cut out of riscv-zkvm's dispatch: each arm's write and exact trap condition, and the point coordinates `Wire.xOf`/`Wire.yOf`. |

## Layer -1: loading

| file | contents |
| --- | --- |
| `Image.lean` | An image's code as 32-bit words, decoded by riscv-zkvm's own `decode`. |
| `Load.lean` | A total, kernel-evaluable loader: the state an SP1 guest starts in, built from an image. |

## The lift to layer 0.5

[`Lprog/`](Lprog/README.md): `rvIsa`, the translation of each instruction into a shared
operation (proved against riscv-zkvm), `lift`, and the simulation that carries Lprog runs down
to `stepSp1`. This is the intended route for new proofs.

## Layer-0 proof tools

These prove things about the machine directly, without the lift. They were built against
zip-2005 and prove most of it. Their results enter the contract table as `SafeN` facts, so
they compose with results proved through the lift. Whether they move up (to discharge facts
at layer 0.5 or 1) or stay as a fallback for what the lift does not cover is an open question
of the roadmap.

| directory | what it does |
| --- | --- |
| [`Frame/`](Frame/README.md) | Frame analysis: return-address integrity for one function activation, computed and proved sound. |
| [`Check/`](Check/README.md) | The contract checker: from code, an untrusted annotation and callee interfaces, a Boolean check that a function meets its interface, proved sound against `stepSp1`. Derives structural specifications (frame, footprint, callee-saved registers, stack bounds) for every function, with `Tools/Infer.lean`. |
| [`Exec/`](Exec/README.md) | Hand proofs of interfaces the checker cannot derive, against the same judgement. |
| [`Sym/`](Sym/README.md) | The symbolic executor `sym_exec`, which proves functional specifications by stepping the machine. |

`Sym.lean` imports the executor.

This directory is the template for the other instruction sets: `../ARM` and `../X86` are to
grow their own counterparts of it, starting with a loader and a lift into `../Lprog`.
