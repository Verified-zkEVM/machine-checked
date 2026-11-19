# MachineChecked

Formally verify machine code directly in Lean.

> [!WARNING]
> **Early days.** MachineChecked is a young research project, and it is changing quickly: its
> layers, interfaces and file layout will move as the design settles. Some layers exist only on
> paper, some proofs rest on premises that are still open, and the AArch64 and x86-64 models are
> trusted rather than verified. The [roadmap](ROADMAP.md) says what exists and what doesn't. Read
> a result here as evidence, not yet as an audit: check exactly what each theorem states and
> assumes before relying on it. Questions, issues and feedback are very welcome.
>
> **Want to contribute?** Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) first, and get in
> touch before starting work.

MachineChecked proves things about the binary a compiler produced, not about its source. The
compiler and assembler are not trusted. What is trusted is the model of the instruction set,
the Lean kernel, and the step that reads the binary into Lean ([trust ladder](docs/ELF.md#4-what-is-trusted-and-the-trust-ladder)).

## How it works

A binary is lifted upward through a stack of layers; a specification is refined downward;
proofs happen where they meet.

```
  layer 2     specification refinement     high-level spec, refined downward     (not started)
                   ▲
  layer 1     structured logical program   Pancake: variables, structured control flow
                   ▲  lift 2: decompilation (not yet proved)
  layer 0.5   low logical program (Lprog)  registers, flat memory, labels; one language for every ISA
                   ▲  lift 1: translation (proved for RISC-V)
  layer 0     ISA                          the instruction set's model: RISC-V, AArch64, x86-64
                   ▲  loading
  layer -1    ELF and context              image, layout, system calls, halting, calling convention
```

1. **Load.** Tools read the ELF and write Lean; the kernel re-checks what they claim.
2. **Run on the ISA model.** For RISC-V this is [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm)'s
   `stepSp1`, the step function SP1 executes. Every final theorem is stated here.
3. **Lift.** Each function is translated into Lprog. For RISC-V a simulation proof carries
   anything proved at Lprog back down to the machine.
4. **Prove at Lprog,** with the symbolic-execution tactic `lsym` and function contracts that
   compose across calls.

### Status

| | RISC-V | AArch64 | x86-64 |
| --- | --- | --- | --- |
| ISA model | riscv-zkvm (tied to Sail) | DeepMind's [arm64-semantics](https://github.com/google-deepmind/code-verification/tree/main/arm64-semantics) | [Kraken](https://github.com/AeneasVerif/kraken)'s x64 model |
| Lift to Lprog | proved (simulation) | tested, not proved | tested, not proved |
| Decompile to Pancake | tested by recompiling | tested by recompiling | tested by recompiling |
| Proofs about real binaries | yes ([`Examples/`](Examples/README.md), [`Cases/`](Cases/README.md)) | no | no |

The ISA models are dependencies used unmodified at pinned commits ([`docs/ISA.md`](docs/ISA.md)).
Details, targets and next steps: [`ROADMAP.md`](ROADMAP.md).

What is verified here is functions, not a whole program:

- [`Examples/`](Examples/README.md): 20 small functions in C and Rust, from straight-line
  code to loops over memory, a call and a table in read-only data. Each has a contract at
  Lprog and a theorem about riscv-zkvm's machine alone. `chacha20_block` and SHA-256's
  schedule and compression are lifted there but not proved.
- [`Cases/Hardening`](Cases/Hardening/README.md): C written to break the tools, and `memcmp`
  and `write_vectored` of an SP1 guest's runtime.

No guest is verified end to end in this repository. A whole guest, zip-2005 (an SP1 guest
that checks a Zcash Orchard statement), has its verification in its own repository,
[zip-2005-asm](https://github.com/dhsorens/zip-2005-asm).

## Getting started

The toolchain is pinned in `lean-toolchain` and installed by [elan](https://github.com/leanprover/elan).

```sh
lake exe cache get              # Mathlib's prebuilt oleans
lake build                      # the framework and the tools
lake build Examples             # the examples: every image and every proof
lake build Cases                # the case studies
lake env lean path/to/File.lean # check one file
```

From a fresh clone, after `lake exe cache get`, building all of it takes a few minutes; once
the dependencies are built, under a minute. On the first build Lake prints `warning: building
from source; failed to fetch GitHub release` for riscv-zkvm. It is harmless: the dependency
is pinned to a commit, which has no release archive.

## How to use it

### 1. Decompile a binary

`decompile` reads an ELF for RV64IM, AArch64 or x86-64 (not stripped, not position-independent).

```sh
lake exe decompile --to pancake guest.elf out.pnk          # readable Pancake
lake exe decompile --to lprog   guest.elf out.lprog        # Lprog text
lake exe decompile --to lprog --proved guest.elf           # RISC-V: the lift the theorems are about
```

Code the lift does not cover becomes an explicit trap (`l_trap(n)` / `abort`) rather than
being dropped, so the output either behaves like the binary or says where it stops. The
`--proved` lift is stricter: a function with an instruction it cannot take is left out whole,
and the output says which instruction and why. What each
instruction set does not cover is listed in its `LIMITS.md`
([RISC-V](MachineChecked/RiscV/LIMITS.md), [AArch64](MachineChecked/ARM/LIMITS.md),
[x86-64](MachineChecked/X86/LIMITS.md)).

### 2. Generate Lean to prove against

Proofs about a binary go in a Lake project of their own, which requires this repository and
uses the same `lean-toolchain`:

```toml
[[require]]
name = "machine-checked"
git = "https://github.com/Verified-zkEVM/machine-checked"

[[lean_lib]]
name = "MyProject"
```

In that project (for RISC-V; the `--proved` lift is the one the theorems are about):

```sh
lake exe decompile --to lean --proved guest.elf . MyProject.Gen
```

This writes `MyProject/Gen.lean` and `MyProject/Gen/`:

- `Words.lean`: each function's instruction words, checked against the ELF when the module is
  built (`check_elf_words`), and `fns`, the functions they decode to.
- `F<i>.lean`: function `i`'s lift as a term `f<i>`, with `f<i>_eq : (liftProg fns)[i]? = some f<i>`,
  checked by the kernel.
- `Gen.lean`: imports everything, and lists which index is which symbol.

The ELF path is read relative to where the module is built, and the namespace's directory
(`MyProject/Gen/`) must not already exist. See [`Tools/README.md`](Tools/README.md) for the
other routes and what each one trusts.

### 3. Prove a function's contract

A contract (`Isa.Contract`) says: from a precondition on entry, the function returns in a state
satisfying a postcondition. `lsym` steps the lifted body symbolically, uses callees' contracts
at calls, and leaves the goals it cannot close.

The example in this step and the next is for `Examples/elf/basic.elf` of this repository as
`guest.elf` ([`Examples/README.md`](Examples/README.md)), whose function 0 is `add3` at
`0x10000`: two additions and a return. The two Lean snippets, one after the other, are one
file, `MyProject.lean`, which `lake build` checks:

```lean
import MyProject.Gen
import LprogRiscV.Lsym
import MachineChecked.RiscV.Lift.Contract  -- for step 4

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift
open MyProject.Gen

theorem add3_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  apply hk
  exact ⟨by simp only [lsym_simp]; ac_rfl, fun r h => by simp [lsym_simp, h], rfl⟩
```

The precondition says the return address (`x1`) and the stack pointer (`x2`) are the frame's.
The postcondition: `x10` is the sum, every other register and the memory are kept. `lsym`
steps the body; what is left is the postcondition.

How to use `lsym`, and its limits: [`docs/design/Automation.md`](docs/design/Automation.md).
A loop is a lemma at its head, proved by induction;
[`docs/Walkthrough.md`](docs/Walkthrough.md) does one, and [`Examples/`](Examples/README.md)
has more.

### 4. Carry it down to the machine

For RISC-V, `SafeN.of_isa_contract`
([`RiscV/Lift/Contract.lean`](MachineChecked/RiscV/Lift/Contract.lean)) turns a contract at
Lprog into a theorem about riscv-zkvm's machine with the binary's functions in its code
(`Loaded fns s`). Continuing the file of step 3:

```lean
open MachineChecked.RiscV MachineChecked.RiscV.Sym

theorem hok : ProgOk fns := by decide

theorem add3_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = s.getReg .x10 + s.getReg .x11 + s.getReg .x12 →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode add3_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts]; simpa [regsOf] using h10
```

Read it as: a machine `s` at `add3`'s entry, with the binary's functions in its code, is safe
if every state `t` it may return in is. `SafeN` is safety of riscv-zkvm's `stepSp1` for `k`
steps; nothing in the statement is about the lift. It says what holds if the function
returns, not that it does. [`docs/Walkthrough.md`](docs/Walkthrough.md) follows a function
with a loop through every step.

### 5. Check what it rests on

```lean
#print axioms add3_correct
```

Only `propext`, `Classical.choice`, `Quot.sound`, and `bv_decide` certificates are expected
(for `add3_correct`, the first three). The repository has no `sorry`, `axiom` or
`native_decide`; CI enforces this.

## Repository map

```
MachineChecked/   the framework, by layer                       (MachineChecked/README.md)
  RiscV/          RISC-V on SP1: loader, judgement, the proved lift, layer-0 proof tools
  ARM/, X86/      AArch64 and x86-64: semantics (dependencies) and their lifts
  Logical/        layer 1: Pancake and lift 2
  Refine/         layer 2: placeholder
lprog/            package: Lprog, its semantics, runs (Ascent), contracts, lsym
lprog-riscv/      package: RISC-V at Lprog, SP1's execution context
pancake/          package: Pancake as the decompiler writes it
Tools/            untrusted tools: decompile, gen-image, infer-contracts; their tests
Examples/         small functions in C and Rust, each verified down to the machine
                                                                (Examples/README.md)
Cases/            case studies: code written to break the tools, functions of a guest's
                  runtime, a loaded image                       (Cases/README.md)
scripts/          CI checks: axioms, decompile-check, to-lean-check
docs/             guides and design notes
```

The packages `lprog`, `lprog-riscv` and `pancake` can be required on their own
([`docs/design/Packages.md`](docs/design/Packages.md)).

## Documentation

Start with:
- [`docs/Walkthrough.md`](docs/Walkthrough.md): one function, `gcd`, from its source to a
  theorem about the machine.
- [`Examples/README.md`](Examples/README.md): the examples, what is verified of each, and how
  their proofs are written.
- [`Tools/README.md`](Tools/README.md): the decompiler and `--to lean`, and what each route trusts.
- [`docs/design/Automation.md`](docs/design/Automation.md): `lsym` in practice.

Reference:
- [`ROADMAP.md`](ROADMAP.md): the layers, current state, targets and next steps.
- [`MachineChecked/README.md`](MachineChecked/README.md): the framework, directory by directory.
- [`docs/Architecture.md`](docs/Architecture.md): the judgement and the contract table.
- [`docs/ELF.md`](docs/ELF.md): loading, and what is trusted.
- [`docs/ISA.md`](docs/ISA.md): the specification of each instruction set.
- [`docs/design/`](docs/design/): design of Lprog, the decompiler, packages and automation.
- [`docs/LogicalMachine.md`](docs/LogicalMachine.md): a sketch of layer 1.
- [`RELATED.md`](RELATED.md): related work.

## Contributing

Contributions are welcome. While the project is young, please get in touch with the maintainer,
Derek Sorensen, before starting work, for example on the [Lean Zulip](https://leanprover.zulipchat.com).
Then see [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Licence

Apache-2.0 ([`LICENSE`](LICENSE)). Code ported from other projects keeps its original licence
notice, recorded in the `PROVENANCE.md` of its directory. The binaries under `Cases/` come from
programs under their own licences; each case's README says which.
