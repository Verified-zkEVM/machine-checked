# Roadmap

The goal: a Lean framework for formally verifying binaries from any compiler, on RISC-V,
AArch64 and x86-64. You import it, lift an ELF into a logical machine, and prove it correct
against a high-level specification (at the level of, say, ArkLib or CompPoly). The examples
in [`Examples/`](Examples/README.md) and the case studies in [`Cases/`](Cases/README.md) are
its first users.

This document describes the layers, where each stands, the targets, and what comes next.

## The layers

A binary enters at the bottom and is lifted upward. A specification enters at the top and is
refined downward. The two meet at the structured logical program, where proofs are done.

```
  layer 2     spec refinement          high-level specification, refined downward
                   ▲  meet in the middle
  layer 1     structured logical       variables, structured control flow, program logics,
              program                  function contracts                (ISA-independent)
                   ▲  lift 2: decompilation (verified, possibly partial)
  layer 0.5   low logical program      registers, flat memory, labels; shared operations
                   ▲  lift 1: translation (verified, per ISA)
  layer 0     ISA                      verified interpreter for RISC-V / ARM / x86
                   ▲  loading
  layer -1    ELF and context          image, layout, syscalls, halting, calling convention
```

**Layer 2: specification refinement.** Tools to refine a high-level specification down toward
the logical program. A verification effort works from both ends and meets at layer 1.

**Layer 1: structured logical programs.** Pancake, with the semantics of
[Flapjack](https://github.com/pirapira/flapjack), the Lean port of the Pancake compiler.
Registers become variables, frames become locals, and control flow is structured. This is where
program logics and contract composition belong, with the ABI and context as parameters. Lift 2
into it is real decompilation: per function, and allowed to fail. A function it cannot lift is
proved at layer 0.5 instead. Its output is Pancake source, so Flapjack can compile it back down.

**Layer 0.5: low logical programs (Lprog).** Inspired by linear Jasmin and Pancake's lower
intermediate languages (Stack, Lab). Registers, flat memory and labels, but one language for
every ISA: shared control flow and shared operations (bitvector expressions, loads and stores,
flags as explicit values). Only register names and the calling convention are ISA parameters.
So each ISA's lift absorbs its quirks, and everything above is written once.

**Layer 0: the ISA.** A verified interpreter per ISA, such as
[riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm) for RISC-V. Each lift into layer 0.5
comes with a theorem that anything proved of the lifted program holds of the machine running
the binary. The final theorem is always stated here, even though the proving happens higher up.

**Layer -1: the ELF and its context.** How an ELF is loaded, which depends on the execution
context (riscv-zkvm, for example, has SP1 and Zisk backends; in the long run each ISA should
support several, see [this slide](https://derekhsorensen.com/slides/verso/cambridge-2026/#/5/2)). A context also fixes the system
calls, how a run halts and what counts as accepting, the memory regions, and the calling
convention. It is a parameter carried through every layer: a system call is a step at layer 0
and an external call with a specification above.

## Across instruction sets

![Each instruction set (ARM, RISC-V, x86) decompiles into linear Jasmin, which lifts into
Pancake (Flapjack); programs are transpiled between instruction
sets.](docs/media/machine-checked-structure.png)

The aim is a decompiler and transpiler framework where every arrow is verified and the diagram
commutes:

- **Decompile** is lift 1 into layer 0.5, then lift 2 into Pancake.
- **Transpile** translates a program from one ISA to another, with a simulation relating the
  two programs' runs.
- **Commuting** means the routes agree: transpiling A to B and then decompiling gives the same
  layer-0.5 program, up to behavioural equivalence with the ABI mapped, as decompiling from A.
  Likewise A to B then B to C agrees with A to C.

Then a property proved once at layer 0.5 holds on every ISA the program reaches.

**Compiling back down.** Two verified compilers in Lean go the other way, so a transpiler can be
our decompiler followed by one of them: **Flapjack** (Pancake to RISC-V, AArch64, x86-64) and
**catcrypt-compiler** (through a Jasmin dialect and a linear form close to layer 0.5); Jasmin
itself is a third. First
use: decompile, recompile, and compare behaviour on tests. Later: a round-trip refinement
theorem in the shape of [flapjack-flip](https://github.com/dhsorens/flapjack-flip)'s
`DecompilerSound`. That needs each compiler's correctness stated over this repository's ISA
semantics rather than its own.

Open: whether some transpilers are better built directly; what to do with features one ISA
lacks (flags, which RISC-V has none of; instructions without a counterpart; different syscalls); and which observations
the equivalence keeps (outputs, memory, leakage).

## Current state

| layer | what exists |
| --- | --- |
| 2 | Nothing generic (`MachineChecked/Refine` is a placeholder). Each example's and case study's specification connects to its proofs directly. |
| 1 | `MachineChecked/Logical`: Pancake, and lift 2 from Lprog with structured control flow where it can be found. Not proved; checked by recompiling with Flapjack and comparing runs ([`scripts/decompile-check`](scripts/decompile-check/README.md)) for RISC-V, AArch64 and x86-64. [`docs/LogicalMachine.md`](docs/LogicalMachine.md) sketches the program logics. |
| 0.5 | The package [`lprog`](lprog/README.md): Lprog's syntax and semantics, independent of any ISA, with calls, tail calls, returns and external calls; the judgement `SafeN`; contracts (`Isa.Contract`); the symbolic-execution tactic `lsym`. Design: [`docs/design/Lprog.md`](docs/design/Lprog.md), [`docs/design/Automation.md`](docs/design/Automation.md). |
| 0 → 0.5 | **RISC-V** (`MachineChecked/RiscV/Lift`): whole programs lift, and the transfer theorem carries `SafeN` at Lprog down to `stepSp1`, with SP1's system calls as the context. `SafeN.of_isa_contract` (`Contract.lean`) carries a contract proved with `lsym` to the machine as it is. **AArch64, x86-64** (`MachineChecked/ARM/Lift`, `X86/Lift`): lifts of linked programs for `decompile`, tested but not proved; limits in each `LIMITS.md`. |
| 0 | **RISC-V:** riscv-zkvm, tied to Sail, with the judgement `SafeN` over `stepSp1`, and the layer-0 proof tools (`RiscV/Check`, `Sym`, `Frame`, `Exec`). **x86-64:** Kraken's x64 semantics (`MachineChecked/X86/Kraken.lean`); no judgement over it yet. **AArch64:** DeepMind's arm64-semantics (`MachineChecked/ARM/Arm64.lean`); no judgement over it yet. |
| -1 | RISC-V on SP1 only: the loader, SP1's acceptance and system calls. The context is not yet a parameter. |
| all | `lprog/Lprog/Ascent`: one notion of a run and one correspondence, for any step function. |
| proofs | [`Examples/`](Examples/README.md): 19 functions in C and Rust (RISC-V), each with a contract at Lprog (`<function>_contract`, by `lsym`) and the same statement about the machine alone (`<function>_correct`). Lifted there and not proved: `chacha20_block` and the three SHA-256 functions. [`Cases/Hardening`](Cases/Hardening/README.md): code written to break the tools, and `memcmp` and `write_vectored` of an SP1 guest's runtime. No whole program. |

In short: layers -1 to 0.5 are real for RISC-V, layer 0.5 is shared, and layers 1 and 2 are not
started as proved layers. The layer-0 tools predate the lift; new proofs go through the lift.

## Targets

Chosen to exercise the framework in different ways, so that practice drives the design.

| target | ISA | exercises | status |
| --- | --- | --- | --- |
| [the example ladder](Examples/README.md): small functions in C and Rust, their sources shared with [braid](https://github.com/dhsorens/braid) | RISC-V | the whole route on one function at a time, from straight-line code to cryptographic kernels: source, binary, lift, contract with `lsym`, theorem about the machine | 19 functions proved down to the machine, up to `crc32` and ChaCha20's `quarter_round`; `chacha20_block` and SHA-256 (`sha256_round`, `sha256_schedule`, `sha256_compress`) lifted, not proved |
| zip-2005: an SP1 guest checking a Zcash Orchard statement | RISC-V | a whole Rust binary: runtime, allocator, panics, cryptography, `main` | has its verification in its own repository, [zip-2005-asm](https://github.com/dhsorens/zip-2005-asm); here, `memcmp` and an SP1 guest's `write_vectored` are proved through the lift in [Hardening](Cases/Hardening/README.md) |
| [leanVM BLAKE2s](Cases/LeanVM/README.md) | RISC-V | a second execution context; a hash against [hash-specs](https://github.com/dhsorens/hash-specs) | image and loading only |
| [Hardening](Cases/Hardening/README.md): small C programs written to break the tools, and two functions of an SP1 guest's runtime | RISC-V | every function proved with `lsym` against what C says | done; findings tracked in its README |
| the sig.golf verifier | to be chosen | signature verification end to end | not started |
| hash and bignum routines in the style of [s2n-bignum](https://github.com/awslabs/s2n-bignum) | x86-64, AArch64 | hand-written assembly, flags and carries | not started |

To propose a target, open an issue saying what the program is, where its binary comes from,
and what its specification would be.

## Next steps

1. **Finish automation at Lprog.** Lprog programs and the RISC-V transfer theorem are done
   (milestone A of [`docs/design/Lprog.md`](docs/design/Lprog.md)), contracts (`Isa.Contract`)
   are stated, and the symbolic executor `lsym` works on real code ([`docs/design/Automation.md`](docs/design/Automation.md)).
   Next: `lsym` stepping straight-line blocks at once (`SafeN.block`), milestone B's
   benchmarks re-proved with it, and the contract table at Lprog (milestone C).
2. **Finish the example ladder** before larger guests: SHA-256 and `chacha20_block`
   ([`Examples/README.md`](Examples/README.md)). Their long straight-line bodies need
   `SafeN.block` in `lsym`, or more speed per step.
3. **Move zip-2005 onto the lift.** Re-prove its function specifications at Lprog (in
   [zip-2005-asm](https://github.com/dhsorens/zip-2005-asm)), so the end theorem goes through
   one route. This is also the test of step 1 at scale.
4. **Contexts as parameters,** with SP1 as the first instance, so a second context (Zisk,
   leanVM) can sit beside it.
5. **Layer 1:** lift 2 into Pancake proved, per function and possibly partial
   ([`docs/design/Decompiler.md`](docs/design/Decompiler.md)).
6. **Program logics at layer 1, and specification refinement (layer 2),** driven by the
   targets.
7. **AArch64 and x86-64:** state the judgement over each step function, then prove each lift.
   The s2n-bignum style routines are the first targets.
8. **Transpiling between instruction sets,** first checked on tests, then proved, with the
   theorems that the figure above commutes.

## Open questions

- **Properties beyond functional correctness,** such as constant time or cost. Constant time
  needs a leakage trace in the semantics of layers 0.5 and 1, and lifts that preserve it.
- **Trust in loading:** what trusting the toolchain involves, and which theorems loading needs.
- **The layer-0 proof tools** (`MachineChecked/RiscV/{Check,Sym,Frame,Exec}`): move them up to
  layer 0.5 or 1, or keep them as a fallback for code the lift does not cover?
