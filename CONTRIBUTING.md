# Contributing to MachineChecked

Contributions are welcome: new examples and case studies, proofs of more functions, better automation,
support for more instruction sets, fixes and documentation.

## Where to start

**Get in touch first.** The project is young and its design is still moving, so before you
start work, please reach out to the maintainer, Derek Sorensen, for example on the
[Lean Zulip](https://leanprover.zulipchat.com). A short conversation about what you have in mind
and where it fits saves work on both sides.

- [`ROADMAP.md`](ROADMAP.md): the layers, where the code stands, and what is next. The best
  place to see where a contribution fits.
- [`README.md`](README.md): the idea, how to use the tools, and the layout.
  [`MachineChecked/README.md`](MachineChecked/README.md) goes through the framework directory
  by directory.
- [`docs/Walkthrough.md`](docs/Walkthrough.md): one complete proof (`gcd`) done the
  intended way: lifted to Lprog, proved there, and carried down to the machine.
  [`Examples/README.md`](Examples/README.md) has the rest of the examples.
- [`docs/Architecture.md`](docs/Architecture.md): the judgement and the contract table.
- [`docs/ELF.md`](docs/ELF.md) §4: what is trusted.
- [`AGENTS.md`](AGENTS.md): the entry point for AI agents.

Issues tagged `good first issue` or `help wanted` are good places to begin. If you are unsure
where to start, open an issue and ask.

### Larger contributions

Before a large piece of work, open an issue describing it. Examples are a new instruction set,
a new program logic, or a new case study. For a design that will take more than a few pull
requests, write a short design note in `docs/` first. It should state the goal, the key
definitions and theorems, what will be trusted, and the open choices. Agreeing on these early
saves rework.

## Ground rules

These hold for every change. A pull request that breaks one is not merged.

### Proofs

- **No `sorry`, no `axiom`, no `native_decide`.** `bv_decide` is allowed. Check with
  `#print axioms`: a theorem may depend on `propext`, `Classical.choice` and `Quot.sound`,
  plus the certificate axioms of any `bv_decide` it uses, and nothing else.
- **Zero warnings.** The build is warning-free, and CI fails on any warning. Fix a warning
  rather than silencing it: do not disable a linter with `set_option` or `nolint`. If a warning can only be fixed by
  a signature change or another decision for the maintainers, say so in the pull request.
- **No vacuous results.** A specification must constrain states the program actually reaches.
  Every premise that remains in a top-level theorem needs a witness that it is satisfiable,
  that is, that it holds on the reference run. A contract quantified over states that never
  occur proves nothing.
- **Untrusted producers, trusted checker.** Tools may generate images, annotations and
  certificates, but the Lean kernel re-checks everything they produce. Nothing in
  `MachineChecked/` imports `Tools/`; proofs in `Examples/` and `Cases/` import it only through
  the modules `decompile --to lean` wrote (`Tools.ToLean`, for `check_elf_words`).

### Semantics and trust

- **One semantics per instruction set.** For RISC-V it is riscv-zkvm's `stepSp1`, for
  x86-64 Kraken's x64 semantics, and for AArch64 DeepMind's arm64-semantics, each used
  unmodified at its pinned revision. Do not add a second semantics for any of them. If another
  model is ever needed, prove it against the one there is.
- **Trusted models are named.** An instruction-set model may be trusted only if it is listed
  on the trust ladder (`docs/ELF.md` §4). Every model is to be verified against its canonical
  specification (`docs/ISA.md`) in the end.
- **One judgement.** Function specifications are stated as `SafeN` in continuation form: at
  the machine (`MachineChecked/RiscV/Safe.lean`), and at Lprog as `Isa.Contract`
  (`lprog/Lprog/Contract.lean`), carried down by `SafeN.of_isa_contract`
  (`MachineChecked/RiscV/Lift/Contract.lean`; `SafeN.of_contract` in `Transfer.lean` for a
  postcondition over a machine state). Results proved by
  different tools compose through the contract table.
- **One of each concept.** One notion of a run (`lprog/Lprog/Ascent/Run.lean`), one
  correspondence (`lprog/Lprog/Ascent/Corres.lean`), one logical machine per layer, and one
  route from an ISA up to it (its lift). Do not add a second version of a data structure or
  a second refinement step beside an existing one; extend or generalise the existing one.

### Dependencies

- Mathlib may be imported, but keep imports to what a file needs.
- Code taken from another project is *ported*, not added as a dependency. It is copied, owned,
  and adapted until it passes these rules. Record its origin in the module header and in the
  directory's `PROVENANCE.md`, and keep its licence notice.
- The Lean toolchain is kept at the newest version the dependencies allow.

## Workflow

### Building and checking

```sh
lake exe cache get
lake build                                # the framework and the tools (the default)
lake build Examples                       # every example
lake build Cases                          # every case study
lake build Examples.RustBasic             # one module and what it imports
lake env lean path/to/File.lean           # check one file
```

Building everything takes a few minutes from a fresh clone after `lake exe cache get`, and under
a minute once the dependencies are built. Lake's `warning: building from source; failed to
fetch GitHub release` for riscv-zkvm on the first build is harmless: the dependency is pinned
to a commit, which has no release archive.

Continuous integration (`.github/workflows/ci.yml`) runs one job, `build`, on every pull
request (about 8 minutes on a GitHub runner):

- a search of the sources for `sorry`, `axiom` and `native_decide`;
- `lake build MachineChecked Tools Examples Cases`: the framework, the tools, the examples and
  every case study, failing on any warning;
- `python3 scripts/decompile-check/check.py limits`: the instruction tables in each
  `LIMITS.md` match what `decompile --table` generates;
- `scripts/to-lean-check/check.sh`: `decompile --to lean` end to end on a small ELF;
- `scripts/AxiomCheck.lean` (framework) and `scripts/AxiomCheckCases.lean` (examples and case
  studies):
  the listed theorems use only the standard axioms and `bv_decide` certificates.

Before opening a pull request:
1. Build every module you touched and every module that imports it. A change to a widely
   imported file means `lake build MachineChecked Tools Examples Cases`, as CI runs it.
2. Confirm the build has no warnings.
3. Run `#print axioms` on the theorems you added or changed, and add the main ones to
   `scripts/AxiomCheck.lean` (framework) or `scripts/AxiomCheckCases.lean` (examples and
   case studies).
4. If you changed a lift, run `check.py limits`; if you changed `Tools/ToLean.lean`, run
   `scripts/to-lean-check/check.sh`.

### Pull requests

**Titles** follow `<type>(<optional scope>): <subject>`.
- Types: `feat`, `fix`, `proof` (new or changed proofs), `doc`, `refactor`, `perf`, `test`,
  `chore`, `ci`.
- The scope is a directory or case, such as `riscv/sym`, `lprog`, `examples` or `hardening`.
- The subject is imperative and lower case, with no final full stop: `feat(lprog): lift
  indirect jumps with candidate lists`.

**Descriptions** say:
- what the change does and why;
- what is now proved that was not (and what was assumed before);
- anything left open;
- the checks you ran.

Link the issue it closes.

**One change per pull request.** A new tool and a proof that uses it can be two pull requests.
That keeps review possible and history readable.

**Statements are an interface.** If you change the statement of a theorem others use, fix the
callers in the same pull request, or keep the old name as a deprecated alias:

```lean
@[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name
```

### Commits

Write commit messages in the imperative, with a short first line and a body that explains why.
Keep commits buildable where you can.

## Adding an example

An example is a small function with its source here, verified down to the machine
([`Examples/README.md`](Examples/README.md)). RISC-V only: the AArch64 and x86-64 lifts are not
proved.

1. Put the source under `Examples/src/c/` or `Examples/src/rust/`.
2. Add a line for it to `Examples/build.sh` and run the script (after `lake build decompile`).
   It compiles the source to `Examples/elf/` and writes the generated modules,
   `Examples/Gen/<Module>.lean` and `Examples/Gen/<Module>/`. Commit the ELF and the modules;
   do not edit the modules.
3. Write `Examples/<Module>.lean`: for each function a contract at Lprog, proved with `lsym`
   (`<function>_contract`), and the same statement about the machine through
   `SafeN.of_isa_contract` (`<function>_correct`). `Examples/Basic.lean` is the shortest model.
   Import the file from `Examples.lean`.
4. Add a row to the table in `Examples/README.md`. A function that is lifted and not proved
   goes in the "Not verified yet" table, with what was tried.
5. Add each `_correct` theorem to `scripts/AxiomCheckCases.lean`.

## Adding a case study

A case study is for what an example is not: a binary from elsewhere, a program rather than a
function, or code chosen to break the tools.

1. Pin the binary: commit it, or record how it was built and its digest.
2. Lift it (RISC-V only: the AArch64 and x86-64 lifts are not proved): `lake exe decompile --to lean --proved BINARY . Cases.<Name>.Gen` writes the
   lifted functions, checked against the ELF ([`Tools/README.md`](Tools/README.md)).
   `Cases/Hardening/build.sh` is an example. For a whole-program theorem from the loaded
   image, also generate the image with `lake exe gen-image` and prove its facts in
   `Cases/<Name>/Loaded.lean` (as `Cases/LeanVM/Blake2s` does).
3. Prove function contracts at Lprog with `lsym`, one module per function or family. Reuse
   the runtime specifications where the code is shared.
4. Carry them to the machine (`SafeN.of_isa_contract`, or `SafeN.of_contract`) and compose them into a theorem about the
   binary's accepting runs.
5. Add `Cases/<Name>/README.md`, saying where the binary came from and under what licence its
   code is, and a row to `Cases/README.md`.

## Style

Follow the Lean community's conventions (Mathlib's style and naming guides) unless a rule here
says otherwise. When in doubt, match the surrounding code.

### Files and namespaces

- Files are `UpperCamelCase.lean`. A file's namespace mirrors its path:
  `MachineChecked/RiscV/Sym/Mem.lean` is `MachineChecked.RiscV.Sym`.
- Keep lines under 100 characters, and indent by 2 spaces.
- Every new file is reachable from its library root: `MachineChecked.lean` for the framework,
  `Examples.lean` for an example, the case's root module for a case.

### Naming

- Types and structures are `UpperCamelCase`, definitions are `lowerCamelCase`, and theorems
  are `snake_case`.
- A theorem's name describes its statement: `_of_` separates the conclusion from the
  hypotheses (`regs_of_agree`, `noCodeAt_of_codeWithin`), and standard words name standard
  facts (`refl`, `symm`, `trans`, `congr`, `mono`, `ext`, `iff`).
- Name a declaration for what it says, never for where it came from or when it was written.
  Do not use paper numbering, phase codes or dates in names. Put citations in the module
  header instead.
- A function's specification is `<function>_spec`, and a case's top theorem says what it
  proves.

### Proofs

- **Make the structure visible.** Prefer named intermediate lemmas to long monolithic proofs,
  and put a lemma that recurs into the module that owns the definition.
- **Use automation on well-scoped goals.** `simp`, `omega`, `bv_decide`, `decide` and `grind`
  are all welcome as terminal steps, or after a step that leaves a clear goal.
- **Keep big literals away from `omega` and the kernel.** On machine code, concrete addresses
  and 64-bit constants are everywhere. State a generic lemma over a variable and instantiate
  it, rather than letting `omega` or `decide` work on huge numerals in a large context.
- **Be careful with resource limits.** Avoid raising `maxHeartbeats` or `maxRecDepth`. When it
  is needed (generated images and long symbolic runs do need it), scope it to one declaration
  with `set_option … in`.
- **Profile before optimising.** Find the expensive declaration and tactic, then narrow the
  proof. Do not make repository-wide tactic substitutions without measured evidence.

### Documentation

- **Module headers.** Every file starts with a block comment that names the module and says
  what it contains and how it fits, in a few sentences. It also gives the origin of ported
  code. Look at any file in `MachineChecked/` for the shape.
- **Docstrings.** Every definition and every main theorem has a `/-- … -/` docstring that
  says what it means, not how it is proved.
- **READMEs.** When you add, remove or move a file, update the `README.md` of its directory.
  When you change what is trusted, update `docs/ELF.md` §4.
- **Clear prose.** Write plain, direct English. Use backticks for Lean names, and spell out
  what a theorem guarantees and under which assumptions.

## Conduct

Be respectful and constructive. Assume good faith, critique work rather than people, and help
newcomers find their way. Report unacceptable behaviour to the maintainers.

## Licensing

By contributing, you agree that your contributions are licensed under the repository's licence
(the `LICENSE` file at its root). Code ported from other projects keeps its original licence
notice, as recorded in the `PROVENANCE.md` of its directory.
