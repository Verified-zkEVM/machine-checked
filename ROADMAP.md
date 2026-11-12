# Machine-Checked ✅ Project Roadmap

Our goal is to have a framework for formally verifying bytecode and ELFs, from any compiler, in x86, ARM, and RiscV. In its mature state, this will be a Lean project that can be imported into a context where one wishes to formally verify bytecode (examples are in [Cases/](Cases/) for now) and which will give all the relevant tools to lift an e.g. RiscV ELF into an intermediate, logical machine and then prove it correct wrt a high-level spec (at the level e.g. of Arklib or CompPoly).

## General shape

The framework is a stack of layers. A binary enters at the bottom and is lifted upward. A
high-level specification enters at the top and is refined downward. The two meet in the
middle, at the structured logical program, where proofs are done.

```
  layer 2     spec refinement          high-level specification, refined downward
                   │  refinement
                   ▼  ▲  meet in the middle
  layer 1     structured logical       variables, structured control flow, program logics,
              program                  function contracts             (ISA-independent)
                      ▲  lift 2: decompilation (verified, possibly partial)
  layer 0.5   low logical program      registers, flat memory, labels; shared operations
                      ▲  lift 1: translation (verified, per ISA)
  layer 0     ISA                      verified interpreter for RISC-V / ARM / x86
                      ▲  loading
  layer -1    ELF and context          image, layout, syscalls, halting, calling convention
```

### Layer 2: specification refinement

Tools for refining high-level specifications, at the level of ArkLib or CompPoly, down
toward the logical program. In practice a verification effort works from both ends: the
program ascends through the program logics of layer 1, the specification descends through
refinement, and the two meet there.

### Layer 1: structured logical programs

The ISA-independent layer: Pancake, with the semantics of [Flapjack](https://github.com/pirapira/flapjack), the Lean port of the Pancake
compiler. Registers become variables, stack frames are abstracted away, and control flow is
structured. It is the layer meant for proving:
- **Program logics** that give the machinery to reason about programs.
- **Function contracts and their composition** (calls, linking), with the ABI and the
  context as parameters.

The lift into this layer is real decompilation. It turns registers into variables and frames
into locals, and rebuilds structured control flow from the control-flow graph. It will not
always succeed, so it is per function and may be partial. A function that cannot be lifted
stays at layer 0.5 and is proved there. Its output is Pancake source, so Flapjack can compile it
back down (see the next section).

### Layer 0.5: low logical programs

The first lifting target, inspired by linear Jasmin and by the lower intermediate languages of
Pancake's compiler (Stack and Lab). It still has registers, flat
memory and labels, but it is one shared language for every ISA: shared control flow, and a
shared set of operations (bitvector expressions, loads and stores, flags and carries as
explicit values). Only ABI-level details, such as register names and the calling convention,
are ISA parameters.

So the lift from each ISA into layer 0.5 absorbs that ISA's quirks, and the lift from 0.5 into
layer 1 is written and proved once. We may also want concordance with the communities behind
these languages.

### Layer 0: the ISA

A formally verified interpreter for each supported ISA, such as
[riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm) for RISC-V. They live in
`MachineChecked/RiscV`, `MachineChecked/ARM` and `MachineChecked/X86`. Each comes with the
machinery to lift its programs into layer 0.5.

Each lift is a **verified lifter**: it comes with a theorem that anything proved of the lifted
program also holds of the original bytecode, and so of the ELF. The transfer theorems of the
two lifts compose. The final theorem is therefore always stated at this layer, over the
machine running the loaded ELF. That is what is trusted, even though the proving happens
higher up.

RISC-V is built first. ARM and x86 follow, as peers.

### Across instruction sets: decompiling and transpiling

![Each instruction set (ARM, RISC-V, x86) decompiles into linear Jasmin; programs are
transpiled between instruction sets.](docs/media/machine-checked-structure.png)

The figure is the guiding picture, for now, of how the work is organised at the level of
instruction sets. The aim is a decompiler and transpiler framework in which every arrow is
verified and the diagram commutes.

- **Decompile** is lift 1 above: from each ISA into linear Jasmin, the low logical program of
  layer 0.5, with a simulation that carries every run of the lifted program down to a run of
  the machine.
- **Transpile** is new: a translation of a program from one ISA to another, in each direction,
  with a simulation relating the runs of the two programs.
- **Commuting** means that the routes agree. Transpiling a program from ISA A to ISA B and then
  decompiling it gives the same layer-0.5 program, up to a stated equivalence, as decompiling
  it from A directly. Likewise transpiling A to B and then B to C agrees with transpiling A to
  C. The equivalence at layer 0.5 is behavioural (the same observable runs), with the ABI
  parameters, such as register names and the calling convention, mapped between the ISAs.

The payoff is that a property proved once at layer 0.5 holds of the program on every ISA it
reaches, whichever route it took.

**Compiling back down.** Two verified compilers in Lean go the other way, so a transpiler can
be our decompiler followed by one of them:

- **Flapjack** compiles Pancake (layer 1) to RISC-V, AArch64 and x86-64.
- **catcrypt-compiler** compiles through a Jasmin dialect and a linear form close to linear
  Jasmin (layer 0.5) to the same three ISAs; Jasmin itself is a third.

We use them in two stages. First as a sanity check: decompile a binary, recompile the result
and compare its behaviour with the original's on tests. Then for proof: a round-trip theorem
that the recompiled program refines the original and the original refines it, in the shape of
the `DecompilerSound` statement of the
[flapjack-flip](https://github.com/dhsorens/flapjack-flip) challenge. For that, each compiler's
correctness theorem has to be stated over this repository's semantics of its target
(riscv-zkvm, Kraken, arm64-semantics), not over its own machine model.

Open design questions:

- whether some transpilers are better built directly, ISA to ISA, than through a decompiler
  and a compiler;
- what a transpiler does with what one ISA has and another lacks: flags (RISC-V has none),
  instructions without a counterpart, different syscalls and calling conventions;
- the equivalence itself: which observations it keeps (outputs, memory, leakage) and how the
  contexts of the two ISAs are related.

### Layer -1: the ELF and its context

How an ELF is loaded into the ISA layer. This depends on the context: riscv-zkvm, for example,
has SP1 and Zisk backends. In the long run each ISA should support several contexts (see
[this slide](https://derekhsorensen.com/slides/verso/cambridge-2026/#/5/2)).

A context is more than loading. It also fixes:
- the system calls;
- how a run halts, and what counts as accepting;
- the memory regions;
- the calling convention.

It is therefore a parameter carried through every layer. A system call is a step at layer 0,
and an external call with a specification at layers 0.5 and 1.

### Open questions

- **Properties.** Which properties are in scope beyond functional correctness, such as
  constant time or cost? Constant time, for example, needs a leakage trace in the semantics
  of layers 0.5 and 1, and lifts that preserve it.
- **Trust in loading.** What trust in the compiler and toolchain loading involves, and which
  theorems it needs.
- **The layer-0 proof tools.** `MachineChecked/RiscV/{Check,Sym,Frame,Exec}` prove things about
  the machine directly, without the lift. Should they move up, to discharge facts at layer
  0.5 or 1 (the contract checker's footprints and stack bounds are useful at any layer), or
  stay as a fallback for code the lift does not cover?
- **The context as a parameter.** How the execution context (SP1 today) is threaded through
  the judgement, the loader, the lift's memory and the syscall specifications, so that a
  second context (Zisk, leanVM) can sit beside it.

## Targets

An initial set of programs to verify with the framework. They are chosen to exercise it in
different ways, so that the design is driven by what verification in practice needs.

| target | ISA | what it exercises | status |
| --- | --- | --- | --- |
| [zip-2005](Cases/Zip2005/README.md): an SP1 guest checking a Zcash Orchard statement | RISC-V | a whole Rust binary: runtime, allocator, panics, cryptography, `main` | most of it proved with the layer-0 tools; three functions through the lift |
| [CatCrypt kernels](Cases/CatCrypt/README.md): field and point arithmetic emitted by catcrypt-compiler | RISC-V | straight-line constant-time code, carry chains | `cswap`, `addp256`, `feAdd`, `feSub` proved through the lift; `feMul121666` open |
| [leanVM BLAKE2s](Cases/LeanVM/README.md): a leanVM guest | RISC-V | a second execution context; a hash against [hash-specs](https://github.com/dhsorens/hash-specs) | image and loading only |
| the sig.golf verifier | to be chosen | signature verification end to end | not started |
| hash and bignum routines in the style of [s2n-bignum](https://github.com/awslabs/s2n-bignum) | x86-64, AArch64 | hand-written assembly, flags and carries, the non-RISC-V layers | not started |

Proposals for more targets are welcome: open an issue saying what the program is, where its
binary comes from, and what its specification would be.

## The current state

| layer | roadmap | what exists |
| --- | --- | --- |
| 2 | spec refinement | Nothing generic (`MachineChecked/Refine` is a placeholder). Each case study's specification, for example `Cases/Zip2005/Spec`, connects to its proofs directly. |
| 1 | structured logical program | Nothing yet (`MachineChecked/Logical` is a placeholder). `docs/LogicalMachine.md` sketches it. |
| 0.5 | low logical program | `MachineChecked/Lprog`: linear Jasmin with shared control flow and shared operations (`Op.lean`), independent of any ISA. Programs with a call stack, calls, tail calls, returns checked against the call, and external calls given by an execution context; the judgement is `Ascent.SafeN`. Design: `docs/design/Lprog.md`. |
| 0 → 0.5 | lift 1 | RISC-V: `MachineChecked/RiscV/Lprog`. A program of functions lifts whole: operations, branches, jumps, calls, tail calls, returns and `ecall`s, with SP1's system calls as the context. The transfer theorem carries `SafeN` at Lprog down to `stepSp1`. Not yet: contracts composed by a table, a symbolic executor at Lprog, exit points for lifting part of a program. |
| 0 | ISA | RISC-V: riscv-zkvm, tied to Sail, with the judgement `SafeN` over its `stepSp1`, and the layer-0 proof tools. x86-64: Kraken's x64 semantics is chosen (`docs/ISA.md`) and not yet required; a trusted transcription of Jasmin's stands in. AArch64: DeepMind's arm64-semantics is chosen (`docs/ISA.md`) and not yet required; a trusted hand-written model stands in. |
| -1 | ELF and context | RISC-V on SP1 only: the loader, SP1's acceptance and its system calls. The context is not yet a parameter. |
| all | runs and correspondence | `MachineChecked/Ascent`: one notion of a run and one correspondence, for any step function. Every layer's runs are instances. |

In short: layers -1 to 0.5 are real for RISC-V, layer 0.5 is shared, and layers 1 and 2 are
not started. Most of zip-2005 predates the lift and is proved with the layer-0 tools; new
proofs go through the lift.

## Roadmap steps

1. **Complete the RISC-V lift.** Done for programs (milestone A of `docs/design/Lprog.md`):
   calls, tail calls, returns and system calls run at Lprog, and `write_vectored`'s call to
   `sys_write` uses its callee's contract. Next: a symbolic executor at Lprog (milestone B).
2. **Move zip-2005 onto the lift.** Re-prove its function specifications at Lprog, so the
   end theorem goes through one route. This is also the test of step 1 at scale.
3. **Contracts and composition at layer 0.5,** with the execution context and the calling
   convention as parameters: the contract table stated over Lprog, and SP1 as the first
   instance of a context.
4. **The structured logical program (layer 1)** as Pancake, with Flapjack's semantics, and the
   decompiling lift into it, per function and possibly partial. Recompiling its output with
   Flapjack is the first sanity check.
5. **Program logics at layer 1, and specification refinement (layer 2),** driven by the
   first targets.
6. **AArch64 and x86-64.** For x86-64, require Kraken (which moves the toolchain), state
   the judgement over its x64 semantics and lift its programs into the shared layer 0.5. For
   AArch64, likewise require arm64-semantics, state the judgement over its `Steps` and lift
   into layer 0.5. The s2n-bignum style routines are the first targets here.
7. **Transpiling between instruction sets,** once each ISA has its lift: our decompiler
   followed by Flapjack, catcrypt-compiler or Jasmin, first checked on tests and then proved,
   and the theorems that the figure above commutes.
8. **More targets,** from the list above and from proposals.
