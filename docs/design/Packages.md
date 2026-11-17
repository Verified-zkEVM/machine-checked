# Design note: what this repository exports

**Status: steps 1 and 2 done (2026-11-17); the rest proposed (2026-11-16).** It plans how the decompiler of
[`Decompiler.md`](Decompiler.md) and the logic for reasoning about its output reach people
outside this repository.

## Goal

Two things, for use in the wild:

1. **A decompiler**, `decompile`, built from source for now (`lake build decompile`), with an
   installer later.
2. **Proof libraries** for proving things about the programs it produces: one for Lprog and
   one for Pancake (Flapjack's).

The intended use: run the decompiler on an ELF, get the program as Lean, import the libraries
and prove what you need about it.

Being a light dependency is a goal, not a requirement yet. Building the decompiler may stay
heavy. The layout below makes the libraries light later without moving anything twice.

## 1. Layout: Lake packages in this repository

Lake fetches every package a dependency requires, whichever of its modules one imports. A
light library must therefore be a package of its own. It can still live here: Lake requires a
package in a subdirectory of a repository (`subDir`), as this repository already does for
arm64-semantics, and Flapjack for ZirenDet.

| package | modules | namespaces | holds | requires |
| --- | --- | --- | --- | --- |
| [`lprog/`](../../lprog/README.md) | `Lprog.*` | `Lprog`, `Lprog.Ascent`, `Lprog.ARM`, `Lprog.X86` | `Ascent` (runs, `SafeN`, `Refines`, `Equivalent`, `Corres`), Lprog (syntax, semantics, the rules of `SafeN`, the text format, what lifts are built from), AArch64's and x86-64's registers at Lprog | nothing (Lean's `Std`) |
| [`lprog-riscv/`](../../lprog-riscv/README.md) | `LprogRiscV.*` | `Lprog.RiscV`, `Lprog.RiscV.Machine` | RISC-V at Lprog: the facts about riscv-zkvm's machine it rests on, RISC-V's instance of Lprog (`rvIsa`, `opOf_spec`, `Agree`), SP1's execution context (`sp1Ctx`) and `sp1Ecall_agree` | `lprog/`, riscv-zkvm |
| `pancake/` (not yet) | | | the environments the decompiler's Pancake assumes (SP1's, bare guests'), and lemmas for reasoning about programs in them | Flapjack's semantics |
| the root | `MachineChecked.*`, `Tools.*`, `Cases.*` | `MachineChecked`, … | `decompile` and the other tools, the machine models and the lifts (`MachineChecked/<ISA>/Lift`), the theorems that relate them (`Equiv.lean`), the layer-0 proof tools, `Tools/Test`, the case studies | `lprog/`, `lprog-riscv/` by path; riscv-zkvm, Kraken, arm64-semantics, Flapjack, Mathlib |

The proof libraries are three, not one: their requirements differ (nothing; riscv-zkvm;
Flapjack), and so do their users. A proof about Lprog never needs Flapjack, and one about an
AArch64 program never needs riscv-zkvm.

**RISC-V is moved, not restated.** RISC-V's registers are riscv-zkvm's and SP1's system calls
are riscv-zkvm's `sp1Ecall`, so `lprog-riscv` requires riscv-zkvm rather than restating them
(which would be a second model of SP1 to keep in step). The machine-level modules of the root
(`MachineChecked/RiscV`: `Safe`, `Sym`, the checker) stay there; of them, the instance needs
only the lemmas about reading a state after an update and `isCSRS`, which moved with it
(`Lprog.RiscV.Machine`).

**Two rules of Lean and Lake shape the names.**

- *A module belongs to the library one of whose roots is a prefix of its name, or one of whose
  globs matches it.* The root's library has the root `MachineChecked`, so no other package can
  have modules under `MachineChecked`: Lprog's modules are `Lprog.*`.
- *Lean finds a module through the first directory on its search path that has the module's
  root.* So two packages cannot share a root either: `lprog-riscv`'s modules are
  `LprogRiscV.*`, while its declarations are in `Lprog.RiscV`, as Lean libraries often name
  modules after the package and namespaces after the concept.

**The root's per-instruction-set lifts are `MachineChecked.<ISA>.Lift`**, not `.Lprog` as
before: inside a namespace ending in `Lprog`, `Lprog` would mean that namespace and not the
package.

Flapjack's Pancake semantics imports no Mathlib, but the Flapjack package requires Mathlib and
ZirenDet; until its semantics is a package of its own (a request upstream), `pancake/` is as
heavy as Flapjack.

## 2. From the decompiler to Lean, checked by the kernel

The decompiler writes text (Lprog's, or Pancake). A proof needs Lean. `decompile --to lean`
writes, for a binary:

1. **its words**, as Lean data (as `gen-image` does for the case studies' images);
2. **the decompiled program**, one module per function, as readable terms to prove things
   about;
3. **for each function, a theorem that its term is the lift of the words**: `(liftProg fns)[i]?
   = some f_i`, by `decide +kernel`. The kernel evaluates the lift; the tool that wrote the
   term is not trusted. `native_decide` is not used (CI refuses it).

What is left to trust is that the words in the Lean file are the ELF's. The kernel cannot read
a file, so this is not closed, only narrowed: a Lean command reads the ELF when the module is
built and adds the words it finds as a theorem, so what is trusted is that command, the ELF
reader it shares with the tool, and which file its path names when the module is built. Those
modules must also be as the tool wrote them; a symbol's name is escaped where it appears. A
word misread does not give a false theorem about the binary: the equivalence takes the code at
each function's address as a hypothesis (`CodeAt` in `equivalent_of_entry`), which then does
not hold of the machine. The details are in `Tools/README.md`, "As Lean".

**What the theorem buys depends on the lift.** It says the term is what the lift computes.
That says something about the binary only where the lift has a theorem of its own: today
RISC-V's `liftProg` (the `--proved` route), with `Equiv.lean`'s equivalence, which compares
how a run ends and not the state it ends in. For the whole-program lift, the AArch64 and
x86-64 lifts and lift 2 to Pancake, the term is exactly what an unproved Lean function
computes: nothing worse than today, and no guarantee about the binary. Phase 4 of
`Decompiler.md` is what changes that.

### The experiment

First done on the `--proved` route with a prototype, before the tool had the mode
(now `decompile --to lean`, [`Tools/ToLean.lean`](../../Tools/ToLean.lean)),
built with `lean` module by module, eight at a time, on an Apple M3 Max:

| binary | functions | instructions | Lean written | checked | build, all modules | slowest module |
| --- | --- | --- | --- | --- | --- | --- |
| `experiments/leanvm/out/blake2s.elf` | 6 (3 more left out, `main` among them: a word does not decode) | 702 | 156 KB | 6 | 5 s | 2.7 s |
| `experiments/zip-2005/out/baseline.elf` | 304 | 41,631 | 11 MB | 304 (one with a raised limit, below) | 53 s (331 s of CPU) | 15 s |

A term changed by one immediate fails: the kernel says the theorem is false.

**The kernel's check is affordable;** what took work was getting large terms through the
elaborator, not the check. What the emitter must do, learnt on zip-2005:

- **Data, not code.** The modules are `noncomputable`: the code generator gives up on a list of
  a few thousand elements, and the kernel does not need code.
- **Words per function, as `Nat`.** One list of every word took the elaborator past its
  limit; a `BitVec 32` literal costs an instance search each.
- **Long lists as `List.flatten` of short ones.** A literal of thousands, or a long chain of
  `++`, is too deep for the elaborator (zip-2005's `compress256` is 9,333 instructions).
- **No long literal inside one instruction.** One function holds 218 indirect calls whose
  candidates are every function, `[0, 1, …, 303]`; `List.range 304` is the same term in a few
  characters. The `--proved` lift gives every indirect call every function (a limit noted in
  #32).
- **Even so, that function's check went deeper than the kernel allows by default**: it
  compares 218 lists of 304, and checked only with `maxRecDepth` raised. The tool splits each
  function's theorem instead: the kernel decides its header and its body in parts of 128
  instructions apart, and a lemma (`getElem?_eq_of_chunks`) gives the whole. With that, every
  function of zip-2005 checks with no limit raised, the longest in 12 s; all of them in 74 s on
  8 cores ([`Tools/README.md`](../../Tools/README.md)).

## 3. Flapjack can take the term, not the text

Lift 2 already builds Flapjack's own syntax (`Flapjack.Pancake.PanLang`) and then prints it,
for Flapjack to parse back. In Lean the printer and the parser can go: the term goes straight
to Flapjack's compiler. Two things to settle with Flapjack:

- **An entry point that takes the syntax.** Its command line takes source text
  (`NativeSource.compile`). The functions that compile syntax are inside it (the
  `compileProg` family, over `DeclHOL width`); whether lift 2's declarations are that type or
  need converting is to be checked, and a stable entry point asked for.
- **What it proves.** Flapjack proves passes of its compiler. If it proves the whole compiler,
  the loop binary → Lprog → Pancake → binary lacks one proof only: lift 2's.

## 4. Upstreams: import, do not vendor

**catcrypt-compiler.** `Ascent/Run.lean` and `Ascent/Corres.lean` are ported from it at
`69ffea9f` and changed since (`Ascent/PROVENANCE.md`); Lprog follows its design. Importing it
instead is not practical: its package requires Mathlib, CatCrypt-core, ParamTransfer and
hax-lean, at another Lean version. The proposal in #16 (open; `docs/notes/SHARED-LIBRARY.md`
on its branch) is the way out, the other way round: the generic layer (`SContract`, `SafeN`,
Lprog, and a relational `RefinesR` of which catcrypt-compiler's `RefinesP`/`RefinesO` and our
`Corres` are instances) moves into a package with no Mathlib that both projects require, in a
repository of its own under a neutral name. **`lprog/` is the interim form of that package**:
in this repository until the move #16 proposes is agreed with catcrypt-compiler. #16 also puts
calls and returns as a field of `Isa` (#19) before the package is made. The ported code goes
into it with its attribution, under the dual MIT/Apache-2.0 licence #16 proposes, and
catcrypt-compiler requires it. Then nothing is vendored either way. Until it does, the port is
a fork: its upstream commit stays recorded.

**Flapjack** is a dependency, not vendored. Its pin is a commit only on its branch
`lean-v4.36-frontend`; it needs a tag or a protected branch so that the pin cannot vanish.

**Keeping up.** A scheduled CI job builds against each upstream's latest commit and opens a
pull request that moves the pin when that builds. The real cost is the Lean version: everything
in one build is on one release. This repository is on v4.36.0-rc2, catcrypt-compiler on v4.35,
Flapjack on v4.33.1 with a branch for v4.36. #16 proposes a common stable release with
catcrypt-compiler, moved together; Flapjack is not party to #16, and is to be asked.

## 5. Order of work

| step | what | done when |
| --- | --- | --- |
| 1 | `lprog/` as a package: `Ascent`, Lprog, AArch64's and x86-64's registers; `lprog-riscv/`: RISC-V's instance and SP1's context, moved; the root requires both by path | done: the root builds as before, no theorem changes its statement, and a project outside this repository that requires `lprog/` alone builds and fetches nothing else |
| 2 | `decompile --to lean` (RISC-V, `--proved` route first), with the check against the ELF | done: blake2s and zip-2005 build completely, and a changed word or term fails. This replaces "the zip-2005 modules build in CI's time": the ELFs are not in the repository, so these runs are local, and CI checks a changed term on a small program (`Tools/Test/ToLean.lean`) |
| 3 | `--to lean` for the other routes, and for Pancake as Flapjack's syntax | each route's terms checked against its lift |
| 4 | `pancake/`, on Flapjack's semantics; ask Flapjack for a semantics package and a syntax entry point | a proof about a decompiled guest's Pancake imports `pancake/` only |
| 5 | Ascent's port into `lprog/` with catcrypt-compiler (#16), and the pins kept up by CI | catcrypt-compiler requires `lprog/` |
| 6 | an installer: release binaries of `decompile` from CI | |

## 6. Open questions

- The packages' names. `lprog` and `pancake` are placeholders.
- Whether the words-to-term theorem should be per function, as in the experiment, or one for
  the program, and how a proof about one function uses it.
- How a proof about the Lprog term reaches the binary for routes other than `--proved`: by
  proving those lifts (phase 4), or by relating each to `liftProg`.
