# Design note: what this repository exports

How the decompiler of [`Decompiler.md`](Decompiler.md), and the libraries for reasoning about its
output, reach users outside this repository: package layout, `decompile --to lean`, and the
upstream dependencies.

## Status

| step | what | status |
| --- | --- | --- |
| 1 | `lprog/` and `lprog-riscv/` as packages | done |
| 2 | `decompile --to lean` for the `--proved` route, checked against the ELF | done |
| 3 | `--to lean` for the other routes, and for Pancake | first form done; Flapjack images not covered |
| 3a | certificates for large functions | first step done: the lift is local, and parts are checked by `kernel_eq` ([`Automation.md`](Automation.md), item 6); certificates not started |
| 4 | `pancake/` on Flapjack's semantics | first form (syntax, conventions, printer); semantics waits on Flapjack |
| 5 | Ascent moved into a package shared with catcrypt-compiler (#16); pins kept up by CI | not started |
| 6 | an installer | not started |

Details are in [§5](#5-order-of-work).

## Goal

1. **A decompiler**, `decompile`, built from source for now (`lake build decompile`), with an
   installer later.
2. **Proof libraries** for the programs it produces: one for Lprog and one for Pancake
   (Flapjack's).

The intended workflow: run the decompiler on an ELF, get the program as Lean, import the
libraries, and prove what you need about it.

Being a light dependency is a goal, not yet a requirement; building the decompiler may stay
heavy. The layout below lets the libraries become light later without moving anything twice.

## 1. Layout: Lake packages in this repository

Lake fetches every package a dependency requires, whichever of its modules one imports, so a
light library must be a package of its own. It can still live here: Lake can require a package
in a subdirectory of a repository (`subDir`), as this repository does for arm64-semantics.

| package | modules | namespaces | holds | requires |
| --- | --- | --- | --- | --- |
| [`lprog/`](../../lprog/README.md) | `Lprog.*` | `Lprog`, `Lprog.Ascent`, `Lprog.ARM`, `Lprog.X86` | `Ascent` (runs, `SafeN`, `Refines`, `Equivalent`, `Corres`); Lprog (syntax, semantics, the rules of `SafeN`, the text format, the building blocks of lifts, `lsym`); AArch64's and x86-64's registers | nothing (Lean's `Std`) |
| [`lprog-riscv/`](../../lprog-riscv/README.md) | `LprogRiscV.*` | `Lprog.RiscV`, `Lprog.RiscV.Machine` | RISC-V at Lprog: the facts about riscv-zkvm's machine it rests on, RISC-V's instance (`rvIsa`, `opOf_spec`, `Agree`), SP1's execution context (`sp1Ctx`, `sp1Ecall_agree`) | `lprog/`, riscv-zkvm |
| [`pancake/`](../../pancake/README.md) | `Pancake.*` | `Pancake` | programs over Flapjack's syntax, the environment the decompiler's Pancake assumes, and the printer; Flapjack's semantics once it builds here | Flapjack, Mathlib |
| the root | `MachineChecked.*`, `Tools.*`, `Examples.*` | `MachineChecked`, … | `decompile` and the other tools, the machine models and lifts (`MachineChecked/<ISA>/Lift`), the theorems relating them (`Equiv.lean`), the layer-0 proof tools, `Tools/Test`, the examples | `lprog/`, `lprog-riscv/`, `pancake/` by path; riscv-zkvm, Kraken, arm64-semantics, Flapjack, Mathlib |

There are three proof libraries, not one, because their requirements (nothing; riscv-zkvm;
Flapjack) and their users differ. A proof about Lprog never needs Flapjack, and one about an
AArch64 program never needs riscv-zkvm.

**RISC-V is moved, not restated.** RISC-V's registers are riscv-zkvm's and SP1's system calls are
riscv-zkvm's `sp1Ecall`, so `lprog-riscv` requires riscv-zkvm rather than restating them (which
would be a second model of SP1 to keep in step). The machine-level modules (`MachineChecked/RiscV`:
`Safe`, `Sym`, the checker) stay in the root; the instance needs only the lemmas about reading
a state after an update and `isCSRS`, which moved with it (`Lprog.RiscV.Machine`).

**Two Lean and Lake rules shape the names.**

- *A module belongs to the library one of whose roots is a prefix of its name, or one of whose
  globs matches it.* The root library has the root `MachineChecked`, so no other package can
  have modules under `MachineChecked`: Lprog's modules are `Lprog.*`.
- *Lean finds a module through the first directory on its search path that has the module's
  root.* So two packages cannot share a root either: `lprog-riscv`'s modules are `LprogRiscV.*`,
  while its declarations are in `Lprog.RiscV`.

The root's per-instruction-set lifts are `MachineChecked.<ISA>.Lift`, not `.Lprog`: inside a
namespace ending in `Lprog`, `Lprog` would refer to that namespace rather than the package.

**Flapjack's semantics.** It imports no Mathlib, but the Flapjack package requires Mathlib and
ZirenDet, and at the pinned commit its semantics does not build on this repository's Lean
(v4.36): the pinned branch ports only the syntax. So `pancake/` has the syntax and the
conventions, and gets the semantics when Flapjack's builds here. Until that semantics is a
package of its own (a request upstream), `pancake/` is as heavy as Flapjack.

## 2. From the decompiler to Lean, checked by the kernel

The decompiler writes text; a proof needs Lean. `decompile --to lean` writes, for a binary:

1. **its words** (or, for the other routes, its bytes and layout) as Lean data;
2. **the decompiled program**, one module per function, as readable terms;
3. **for each function, a theorem that its term is the lift of that data**, e.g.
   `(liftProg fns)[i]? = some f_i`. The kernel evaluates the lift (`kernel_eq` on the
   `--proved` route, `decide +kernel` on the others); the tool that wrote the term is not
   trusted. `native_decide` is not used (CI refuses it).

**What is left to trust** is that the data in the Lean file is the ELF's. The kernel cannot read
a file, so this is narrowed rather than closed: a Lean command (`check_elf_words`, or
`check_elf_input` on the other routes) reads the ELF when the module is built and adds the data
it finds as a theorem. What is trusted is that command, the ELF reader it shares with the tool,
which file its path names at build time, and that the modules are as the tool wrote them. A
misread word does not give a false theorem about the binary: the equivalence takes the code at
each function's address as a hypothesis (`CodeAt` in `equivalent_of_entry`), which then does
not hold of the machine. The details, module by module, are in
[`Tools/README.md`](../../Tools/README.md), "As Lean".

**What the theorem buys depends on the lift.** It says the term is what the lift computes. That
says something about the binary only where the lift has a theorem of its own: today RISC-V's
`liftProg` (the `--proved` route), with `Equiv.lean`'s equivalence, which compares how a run ends
and not the state it ends in. For the whole-program lifts, the AArch64 and x86-64 lifts and lift
2, the term is exactly what an unproved Lean function computes: no guarantee about the binary.
Phase 4 of `Decompiler.md` is what changes that.

**What the emitter must do**, learnt on zip-2005 (304 functions, 41,631 instructions). Checking
in the kernel is affordable; getting large terms through the elaborator took the work:

- **Data, not code.** The modules are `noncomputable`: the code generator gives up on lists of a
  few thousand elements, and the kernel does not need code.
- **Words per function, as `Nat`.** One list of every word exceeded the elaborator's limits; a
  `BitVec 32` literal costs an instance search each.
- **Long lists as `List.flatten` of short ones.** A literal of thousands of elements, or a long
  chain of `++`, is too deep for the elaborator (zip-2005's `compress256` is 4,039 instructions).
- **No long literal inside one instruction.** A candidate list of every function is written
  `List.range 304`, not `[0, 1, …, 303]`.
- **Split each function's theorem.** The kernel checks the header and the body in parts of 128
  instructions separately, and `getElem?_eq_of_chunks` gives the whole. With that, every
  function of zip-2005 checks with no limit raised. Build times are in `Tools/README.md`.

## 3. Flapjack can take the term, not the text

Lift 2 already builds Flapjack's own syntax (`Flapjack.Pancake.PanLang`) and then prints it for
Flapjack to parse back. In Lean the printer and parser can be skipped: the term can go straight
to Flapjack's compiler. Two things to settle with Flapjack:

- **An entry point that takes syntax.** Its command line takes source text
  (`NativeSource.compile`). The functions that compile syntax are inside it (the `compileProg`
  family, over `DeclHOL width`); whether lift 2's declarations are that type or need converting
  is to be checked, and a stable entry point requested.
- **What it proves.** Flapjack proves passes of its compiler. If it proves the whole compiler,
  the loop binary → Lprog → Pancake → binary lacks only one proof: lift 2's.

## 4. Upstreams: import, do not vendor

**catcrypt-compiler.** `Ascent/Run.lean` and `Ascent/Corres.lean` are ported from it at
`69ffea9f` and changed since (`lprog/Lprog/Ascent/PROVENANCE.md`); Lprog follows its design.
Importing it is not practical: it requires Mathlib, CatCrypt-core, ParamTransfer and hax-lean,
at another Lean version. The proposal in #16 (open; `docs/notes/SHARED-LIBRARY.md` on its branch)
goes the other way: the generic layer (`SContract`, `SafeN`, Lprog, and a relational `RefinesR`
of which catcrypt-compiler's `RefinesP`/`RefinesO` and this repository's `Corres` are instances)
moves into a Mathlib-free package that both projects require, in its own repository under a
neutral name, under the dual MIT/Apache-2.0 licence #16 proposes. #16 also makes calls and
returns a field of `Isa` (#19) first. **`lprog/` is the interim form of that package.** Until
the move, the port is a fork, with its upstream commit recorded.

**Flapjack** is a dependency, not vendored. Its pin is a commit that exists only on its branch
`lean-v4.36-frontend`; it needs a tag or protected branch so that the pin cannot vanish.

**Keeping up.** A scheduled CI job is to build against each upstream's latest commit and open a
pull request moving the pin when that builds. The real cost is the Lean version: everything in
one build is on one release. This repository is on v4.36.0-rc2, catcrypt-compiler on v4.35,
Flapjack on v4.33.1 with a branch for v4.36. #16 proposes a common stable release with
catcrypt-compiler, moved together; Flapjack is not party to #16 and is to be asked.

## 5. Order of work

| step | what | done when / state |
| --- | --- | --- |
| 1 | `lprog/` as a package (`Ascent`, Lprog, AArch64's and x86-64's registers); `lprog-riscv/` (RISC-V's instance and SP1's context, moved); the root requires both by path | **done**: the root builds as before, no theorem changed its statement, and an outside project requiring only `lprog/` builds and fetches nothing else |
| 2 | `decompile --to lean`, RISC-V `--proved` route, with the check against the ELF | **done**: blake2s and zip-2005 build completely, and a changed word or term fails. The ELFs are not in the repository, so these runs are local; CI checks a changed term on a small program (`Tools/Test/ToLean.lean`) |
| 3 | `--to lean` for the other routes, and for Pancake as Flapjack's syntax | **first form**: `decompile --to lean [--pancake]` for RISC-V, AArch64 and x86-64, each term checked against its lift (`Tools/README.md`, "The other routes"). The kernel checks small and medium functions; large ones need step 3a. Flapjack images are not covered |
| 3a | the kernel's work on large functions: check certificates the tool writes (labels, live flags) instead of re-evaluating the lift | the largest function of a bare guest checks in seconds |
| 4 | `pancake/` on Flapjack's semantics; ask Flapjack for a semantics package and a syntax entry point | **first form**: `pancake/` with Flapjack's syntax, the environment's conventions (lift 2 takes them from it) and the printer. The semantics waits on Flapjack (§1). A written `Pancake.lean` still imports the root's `Tools.ToLean` (for `program` and `kernel_eq`), so a proof about it does not yet need only `pancake/` |
| 5 | Ascent's port into `lprog/` with catcrypt-compiler (#16), and pins kept up by CI | catcrypt-compiler requires `lprog/` |
| 6 | an installer: release binaries of `decompile` from CI | |

## 6. Open questions

- The packages' names: `lprog` and `pancake` are placeholders.
- Whether the data-to-term theorem should be per function, as now, or one for the program, and
  how a proof about one function uses it.
- How a proof about the Lprog term reaches the binary on routes other than `--proved`: by proving
  those lifts (phase 4), or by relating each to `liftProg`.
