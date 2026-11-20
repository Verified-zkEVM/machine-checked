# Design note: a verified decompiler

The design of the decompiler in [`ROADMAP.md`](../../ROADMAP.md) (the figure, and steps 4 and
7): a program that lifts a binary to linear Jasmin (Lprog) and on to Pancake, with a proof that
recompiling its output gives an equivalent program. RISC-V first; other instruction sets reuse
everything above their own lift. How to use the tool is in
[`Tools/README.md`](../../Tools/README.md).

## Status

The tool runs on RISC-V, AArch64 and x86-64 ELFs and on Flapjack images, and is tested by
recompiling and running ([`scripts/decompile-check`](../../scripts/decompile-check/README.md)).
Proved so far: phase 0, the equivalence of RISC-V's `--proved` lift 1 (`liftProg`) with the
machine, and phase 1's round trip of the Lprog text (`parse_print`). No other lift 1, and
nothing above lift 1, is proved.

| phase | what | status |
| --- | --- | --- |
| 0 | events in the step (#18); `Refines` and `Equivalent`; lift 1's theorem strengthened to equivalence | done for RISC-V's `liftProg`; SP1's context makes no events yet |
| 1 | `decompile --to lprog`, and an Lprog text format with a round-tripping printer and parser | done |
| 2 | Flapjack required; its images as an execution context; the Pancake printer | built, not proved; the printer is here, not upstream; the image context is not yet defined in Lean |
| 3 | lift 2, baseline; recompile and run flapjack-flip's tests | built and tested, not proved |
| 4 | the inverse theorem for Flapjack: lift 1, lift 2, Flapjack's theorem and the bridge | not started |
| 5 | structure, pass by pass | `if`/`while` built, not proved; variables, frames, types not started |
| 6 | SP1 guests from Rust; other instruction sets | built and tested for SP1, AArch64 and x86-64, not proved |

The catcrypt-compiler exporter (§4) is not started.

## Goal

```
lake exe decompile --to lprog   BINARY     # linear Jasmin (Lprog), as text
lake exe decompile --to pancake BINARY     # Pancake source, for Flapjack
```

For each target, recompiling the output with that target's compiler gives a program equivalent
(not identical) to the original. Each decompilation step is to come with a theorem that it
inverts the corresponding compilation step, up to that equivalence.

## 1. One pipeline, two exits

```
binary ──lift 1──▶ Lprog ──lift 2──▶ Pancake ──▶ Flapjack recompiles     (general)
 (per ISA)           │   (once, for every ISA)
                     └──▶ export to catcrypt-compiler's linear form       (its fragment only;
                          ──▶ catcrypt-compiler recompiles                 refuses the rest)
```

- **Lift 1** takes an instruction set's code into Lprog (`lprog/Lprog`, layer 0.5).
- **Lift 2** takes Lprog into Pancake (layer 1). It is written and proved once, over Lprog, so
  a new instruction set needs only its own lift 1 and execution context. It depends on the
  calling convention and execution context as parameters, not on the instruction set.
- The two targets are two stops on one path, not two decompilers. A decompiler per target
  would duplicate decoding, control-flow recovery and their proofs for each instruction set.

**The middle language is this repository's Lprog**, not catcrypt-compiler's linear form.
"Linear Jasmin" names the style: registers, labels, jumps. Lprog has flat memory, branches,
indirect jumps, calls, tail calls, returns, external calls and many functions.
catcrypt-compiler's form has memory as named arrays, and its verified RISC-V back end compiles
only straight-line blocks (64-bit arithmetic, loads and stores into arrays), one function at a
time. Going through Lprog avoids those limits; they apply only at the optional exporter, which
refuses what is outside the fragment. If a shared Lprog is agreed with catcrypt-compiler (the
shared library proposed in #16), it must stay as general as this one.

## 2. Equivalence

A program refines another when, for every way the environment may answer its external calls,
it makes the same external calls with the same data and ends with the same final status. Two
programs are equivalent when each refines the other. Return values and memory are compared only
through what they make observable. This is `Refines` and `Equivalent` of the
[flapjack-flip](https://github.com/dhsorens/flapjack-flip) challenge (`FlapjackFlip/Spec.lean`),
generalised over the step function and execution context. It lives in
`lprog/Lprog/Ascent/Refine.lean`, beside `SafeN`, and needs a step that yields the events it
makes observable (#18).

## 3. What "inverse" means

For a compilation step `compile : A → B` and a decompilation step `decompile : B → A`:

> if `decompile b = ok a`, then `compile a` is equivalent to `b`.

Each such theorem has three parts:

1. **The lift is sound in both directions:** `b` and `a` are equivalent.
2. **The compiler is correct:** `a` and `compile a` are equivalent. This is the compiler's own
   theorem.
3. **A bridge**, where the compiler's theorem is over its own machine model rather than this
   repository's semantics ([`docs/ISA.md`](../ISA.md)).

End to end, for Pancake, the theorem is flapjack-flip's `DecompilerSound`: whenever the
decompiler succeeds, its output compiles, and the result is equivalent to the input. Refusing
is always sound; what is proved is that an answer, when given, is right.

## 4. The targets

### Flapjack (Pancake)

[Flapjack](https://github.com/pirapira/flapjack) compiles Pancake source text to RISC-V bytes
as a library function, and has a parser. Its Pancake syntax and semantics are layer 1; this
repository defines no Pancake of its own. Flapjack lacks a printer from syntax tree to text;
this repository has one (`pancake/Pancake/Print.lean`), to be contributed upstream.

Flapjack's compiler theorem is over its own RISC-V model, derived from L3, and says every
behaviour of the machine is a behaviour of the source, up to running out of memory. So part 3
above is a bridge from that model to riscv-zkvm on the instructions Flapjack emits; the other
direction of the equivalence comes from determinism.

Flapjack itself is on Lean v4.33.1; this repository is on v4.36. It is required at its branch
`lean-v4.36-frontend`, where the five syntax modules needed build on both releases. Its
semantics does not build here yet ([`Packages.md`](Packages.md) §1).

### catcrypt-compiler

An exporter from Lprog to catcrypt-compiler's linear form, on the fragment its RISC-V back end
compiles, with a theorem that the lift inverts its encoder there. The kernels it
emits are the first examples (four were a case study here, in the tree at tag
`with-zip2005`). Wider coverage follows catcrypt-compiler's back end.

## 5. Lift 2

- **Baseline.** Each Lprog function becomes a Pancake function that loops over a program
  counter and dispatches on it, with registers as globals and memory as Pancake's flat memory.
  Unreadable and total, it gives an end-to-end decompiler before any structure is recovered,
  and is to be proved once.
- **Structure**, as passes over the baseline, each an untrusted proposal with a verified check
  and a fallback when the check fails: merging blocks, loops and conditionals, registers to
  locals, stack slots to locals, calls with arguments.

## 6. Inputs, simplest first

1. **Flapjack's own images** (flapjack-flip's `.fjimg`): one layout, one calling convention,
   external calls by a known convention, 120 tests and a generator. This also adds a second
   execution context beside SP1, which makes the context a real parameter.
2. **SP1 guests compiled from Rust:** system calls as events, the binary's memory inside
   Pancake's.
3. **Other instruction sets,** through their own lift 1.

## 7. What is built

**Phase 0.** `lprog/Lprog/Ascent/Refine.lean`, and `MachineChecked/RiscV/Lift/Equiv.lean`
(`refines_lift`, `lift_refines`, `equivalent_of_entry`). The machine refines the lifted program
outright; the other direction holds for a lifted program that never goes `wrong`. Both need the
outermost return address to lie outside the code.

**Phase 1.** `lprog/Lprog/Text.lean` (`parse_print` proves the round trip on tokens; the tool
checks the step from tokens to text on what it writes) and `decompile --to lprog`.

**Phases 2, 3, 5 and 6: a tool that runs, with nothing proved.** These were built ahead of
phase 4, to have a working tool before the proofs.

- **Lift 1 for linked programs**, shared by all three instruction sets
  (`lprog/Lprog/Linked.lean`: functions, labels, calls, tail calls, computed jumps among
  candidates). Each instruction set gives its registers and the lift of one instruction:
  - RISC-V (`MachineChecked/RiscV/Lift/Whole.lean`): what `liftProg` covers, plus far calls,
    jump tables, indirect calls and tail calls, calls that link through `t0`, and the nine RV64IM
    instructions riscv-zkvm's `Instr` lacks (`RiscV/Lift/Decode.lean`). It is intended to become
    the lift the theorems are about.
  - AArch64 (`MachineChecked/ARM/Lift/`): arm64-semantics' decoder; integer instructions, with
    the four flags as registers.
  - x86-64 (`MachineChecked/X86/Lift/`): this repository's own decoder for the integer
    instructions, since Kraken has none; five flags; partial register writes; the return address
    on the stack, carried in Lprog's link register by a register of the lift's own.
  - Flapjack images (`RiscV/Lift/Flat.lean`, `RiscV/Flapjack/`): code without functions.
- **Dead flag writes** (`lprog/Lprog/Dead.lean`): flags cost a write wherever an instruction
  sets them and are mostly never read; these writes are dropped within a function, assuming
  nothing outside it.
- **Lift 2** (`MachineChecked/Logical/Lift.lean`): a Pancake function per function and a call
  per call, with Lprog's two return checks, so the Pancake program gives up where the Lprog
  program goes `wrong`.
- **Structure** (`MachineChecked/Logical/Structure.lean`): `if` and `while` from the dominator
  tree, for each function whose control flow is reducible and that Flapjack compiles in
  reasonable time as one piece; a loop over the blocks otherwise.
- **Environments** (`MachineChecked/Logical/Guest.lean`, `RiscV/Sp1/`, `ARM/Bare.lean`,
  `X86/Bare.lean`): the guest's memory at its own addresses, and a system call as one FFI call.
- **Testing**: SP1, AArch64 and x86-64 guests from one set of Rust sources, and Flapjack images,
  all agreeing with their reference after decompiling and recompiling
  ([`scripts/decompile-check`](../../scripts/decompile-check/README.md) has the numbers and
  what they do not show). What each lift does not cover is in
  `MachineChecked/{RiscV,ARM,X86}/LIMITS.md`.

**What the proofs will have to settle**, beyond phase 4 itself (now for several lifts 1, one
lift 2, and SP1's and Flapjack's contexts):

- Lprog's calls link through one register, so a RISC-V call through `t0` is lifted as a jump
  into a copy of its target.
- The execution context of a recompiled guest (a Flapjack image whose heap is the guest's
  address space) is stated only by the test runner.
- A Flapjack image's meaning as an execution context needs an Lprog instance for RISC-V without
  SP1's memory check.
- For AArch64 and x86-64: a simulation from each lift down to its machine model (for x86-64,
  first the lift stated over Kraken's instructions, and a decoder Kraken does not have), and the
  meaning of unaligned accesses, which Pancake does not define.

## 8. Risks

- **Toolchain.** Flapjack on v4.36, and the size of its proof (about 4,000 modules to import its
  correctness theorem).
- **The bridge** from Flapjack's RISC-V model to riscv-zkvm.
- **Address spaces.** The original and the recompiled binary lay out memory differently. For
  Flapjack's images the layout is fixed and shared; for binaries from other compilers the
  original's memory has to live inside Pancake's.
- **Indirect jumps and calls** need candidate lists, from untrusted analysis, checked.
