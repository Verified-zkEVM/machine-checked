# Design note: a verified decompiler

**Status: proposed (2026-11-13).** It plans the decompiler of [`ROADMAP.md`](../../ROADMAP.md)
(the figure, and steps 4 and 7): a program that takes a RISC-V binary and decompiles it up to
linear Jasmin and on to Pancake, with a proof, so that recompiling its output gives an
equivalent program. RISC-V first; the other instruction sets reuse everything above their own
lift.

## Goal

```
lake exe decompile --to lprog   BINARY     # linear Jasmin (Lprog), as text
lake exe decompile --to pancake BINARY     # Pancake source, for Flapjack
```

For each target, recompiling the output with that target's compiler gives a program equivalent
to the original. Equivalent, not identical. The decompiler is verified: each decompilation
step comes with a theorem that it inverts the corresponding compilation step, up to that
equivalence.

## 1. One pipeline, two exits

```
binary ──lift 1──▶ Lprog ──lift 2──▶ Pancake ──▶ Flapjack recompiles     (general)
 (per ISA)           │   (once, for every ISA)
                     └──▶ export to catcrypt-compiler's linear form       (its fragment only;
                          ──▶ catcrypt-compiler recompiles                 refuses the rest)
```

- **Lift 1** takes an ISA's code into Lprog (`MachineChecked/Lprog`, layer 0.5). RISC-V's
  exists (`RiscV/Lprog`, `liftProg`), as a verified function.
- **Lift 2** takes Lprog into Pancake (layer 1). It is written and proved once, over Lprog, so
  another ISA needs only its own lift 1 and execution context.
- The two targets are two stops on one path, not two decompilers. A decompiler per target
  would duplicate decoding, control-flow recovery and their proofs, once per ISA.

**The middle language is our Lprog,** not catcrypt-compiler's linear form. "Linear Jasmin"
names the style: registers, labels, jumps. Lprog has flat memory, branches, indirect jumps,
calls, tail calls, returns, external calls and many functions. catcrypt-compiler's form has
memory as named arrays, and its verified RISC-V back end compiles straight-line blocks only
(64-bit arithmetic, loads and stores into arrays), one function at a time. Decompiling through
Lprog inherits none of that. catcrypt-compiler's limits apply at one optional exit, the
exporter, which refuses what is outside its fragment. When a shared Lprog is agreed with
catcrypt-compiler (the shared library proposed in #16), it must stay as general as this one.

## 2. Equivalence

Two programs are equivalent when each refines the other, and a program refines another when,
for every way the environment may answer its external calls, it makes the same external calls
with the same data and ends in the same final status. Return values and memory are compared
only through what they make observable. This is `Refines` and `Equivalent` of the
[flapjack-flip](https://github.com/dhsorens/flapjack-flip) challenge (`FlapjackFlip/Spec.lean`),
generalised over the step function and the execution context. It lives in `Ascent/`, beside
`SafeN`.

It needs **events in the step** (issue #18): a step yields the events it makes observable.
That issue is now the first piece of work here.

## 3. What "inverse" means

For a compilation step `compile : A → B` and our decompilation step `decompile : B → A`:

> if `decompile b = ok a`, then `compile a` is equivalent to `b`.

Each such theorem has three parts:

1. **Our lift is sound, in both directions:** `b` and `a` are equivalent. Today's transfer
   theorem carries Lprog runs down to the machine only, and is strengthened to this.
2. **The compiler is correct:** `a` and `compile a` are equivalent. This is the compiler's own
   theorem.
3. **A bridge,** where the compiler's theorem is over its own machine model and not over this
   repository's semantics (`docs/ISA.md`).

End to end, for Pancake, the theorem is flapjack-flip's `DecompilerSound`: whenever the
decompiler succeeds, its output compiles, and the result is equivalent to the input.

A decompilation step may fail. Refusing is always sound; what is proved is that an answer,
when given, is right.

## 4. The targets

### Flapjack (Pancake)

[Flapjack](https://github.com/pirapira/flapjack) compiles Pancake source text to RISC-V bytes
as a library function, and has a parser. We use its Pancake syntax and semantics as layer 1;
we do not define our own. What it lacks is a printer from the syntax tree to source text,
which we contribute upstream.

Its compiler's theorem is over its own RISC-V model, derived from L3, and says that every
behaviour of the machine is a behaviour of the source, up to running out of memory. So part 3
above is a bridge from that model to riscv-zkvm on the instructions Flapjack emits, and the
other direction of the equivalence comes from determinism.

Flapjack is on Lean v4.33.1; this repository is on v4.36. It has to build on v4.36 before it
can be required.

### catcrypt-compiler

An exporter from Lprog to catcrypt-compiler's linear form, on the fragment its RISC-V back end
compiles, and the theorem that our lift inverts its encoder there. The kernels in
`Cases/CatCrypt` were emitted by it and are the first examples. Wider coverage follows
catcrypt-compiler's back end.

## 5. Lift 2

- **Baseline.** Each Lprog function becomes a Pancake function that loops over a program
  counter and dispatches on it, with the registers as globals and memory as Pancake's flat
  memory. It is unreadable, total, and proved once. It gives a verified decompiler end to end
  before any structure is recovered.
- **Structure,** as passes over the baseline, each an untrusted proposal with a verified
  check, falling back when the check fails: merging blocks, loops and conditionals, registers
  to locals, stack slots to locals, calls with arguments.

Lift 2 depends on the calling convention and the execution context as parameters, not on the
ISA.

## 6. Inputs, simplest first

1. **Flapjack's own images** (flapjack-flip's `.fjimg`): one layout, one calling convention,
   external calls by a known convention, 120 tests and a generator. This also adds a second
   execution context beside SP1, which makes the context a real parameter.
2. **SP1 guests compiled from Rust:** system calls as events, the binary's memory inside
   Pancake's, per function and possibly partial.
3. **Other instruction sets,** through their own lift 1.

## 7. Order of work

| phase | what | where |
| --- | --- | --- |
| 0 | Events in the step (#18); `Refines` and `Equivalent`; lift 1's theorem strengthened to equivalence | `Ascent/`, `Lprog/`, `RiscV/Lprog/` |
| 1 | `decompile --to lprog`: the executable, and a text format for Lprog with a printer and a parser that round-trip | `Tools/`, `Lprog/` |
| 2 | Flapjack required; its images as an execution context; the Pancake printer, upstream | `lakefile.toml`, `RiscV/` |
| 3 | Lift 2, baseline; recompile and run flapjack-flip's tests as the sanity check | `Logical/` |
| 4 | The inverse theorem for Flapjack: lift 1, lift 2, Flapjack's theorem and the bridge | `Logical/`, `RiscV/` |
| 5 | Structure, pass by pass | `Logical/` |
| 6 | SP1 guests from Rust; then other instruction sets | |

The catcrypt-compiler exporter and its theorem run beside phases 1 to 3.

**Phases 0 and 1 are built.** Phase 0: `Ascent/Refine.lean`, and `RiscV/Lprog/Equiv.lean`
(`refines_lift`, `lift_refines`, `equivalent_of_entry`). The machine refines the lifted
program outright; the other direction is for a lifted program that never goes `wrong`, and
both need the outermost return address outside the code. SP1's context makes no events yet.
Phase 1: `Lprog/Text.lean` (`parse_print`, on tokens; the tool checks the step from tokens to
text on what it writes) and `lake exe decompile --to lprog` (`Tools/README.md`).

**Phases 2 and 3 are built, as a program that runs; nothing in them is proved.** Flapjack is
required for its Pancake syntax, at its branch `lean-v4.36-frontend` (the five modules
needed build on both toolchains). `lake exe decompile --to pancake IMAGE.fjimg` takes a
Flapjack image through lift 1 for code without functions (`RiscV/Lprog/Flat.lean`,
`RiscV/Flapjack/`) and lift 2's baseline (`Logical/Lift.lean`) to Pancake text
(`Logical/Pancake.lean`). The sanity check is `scripts/decompile-check`: 552 binaries
decompiled, recompiled by Flapjack (at flapjack-flip's pin and at its `main`) and run against
the originals, all agreeing; its README
says what that does and does not show. Two things differ from the table: the image's
meaning as an execution context is not defined yet (it needs an Lprog instance for RISC-V
without SP1's memory check), and the printer lives here, not upstream.

**The tool takes whole programs (2026-11-15); still nothing above lift 1 is proved.**
`lake exe decompile --to pancake GUEST.elf` takes an SP1 guest that rustc built to Pancake
that Flapjack compiles. This is phase 6's first half and the start of phase 5, done ahead of
phase 4, to have a tool that runs before the proofs:

- **Lift 1 for a linked program** (`RiscV/Lprog/Whole.lean`): what `liftProg` covers, and far
  calls, jump tables, indirect calls and tail calls, calls that link through `t0`, and the
  nine instructions of RV64IM that riscv-zkvm's `Instr` lacks (`RiscV/Lprog/Decode.lean`).
  Not proved, unlike `liftProg`; it is to become the lift the theorems are about.
- **Lift 2 for many functions** (`Logical/Lift.lean`): a Pancake function for each, a call
  for each call, with the two checks Lprog makes of a return, so the Pancake program gives
  up where the Lprog program goes `wrong`.
- **Structure** (`Logical/Structure.lean`): `if` and `while` from the dominator tree, for
  every function whose control flow is reducible and that Flapjack compiles in reasonable
  time as one piece; a loop over the blocks for the rest. No variables, frames or types yet.
- **SP1's environment** (`RiscV/Sp1/`): the guest's memory at its own addresses, `ecall` as
  one FFI call.
- **The check** (`scripts/decompile-check`): 265 guests in Rust, 39 written for one thing
  each and the rest generated, with SP1's own executor as the reference for what a guest
  does; and the 552 images as before. All agree after decompiling and recompiling. Its
  README has the numbers and what they do not show.

What this leaves of the table: phase 4 whole (now for two lifts 1 and one lift 2, and with
SP1's context beside Flapjack's), the rest of phase 5 (variables, frames, types), and of
phase 6 the other instruction sets. Two things the proofs will have to settle that the tool
only works around: Lprog's calls link through one register, so a call through `t0` is
lifted as a jump into a copy of its target; and the execution context of a recompiled guest
(a Flapjack image whose heap is the guest's address space) is stated only by the runner.

## 8. Risks

- **Toolchain.** Flapjack on v4.36, and the size of its proof (about 4,000 modules to import
  its correctness theorem).
- **The bridge** from Flapjack's RISC-V model to riscv-zkvm.
- **Address spaces.** The original and the recompiled binary lay out memory differently. For
  Flapjack's images the layout is fixed and shared. For binaries from other compilers the
  original's memory has to live inside Pancake's, which is the hard part of input class 2.
- **Indirect jumps and calls** need candidate lists, from untrusted analysis and checked.
