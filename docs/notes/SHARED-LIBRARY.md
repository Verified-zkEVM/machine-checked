> **Status (2026-10-27): proposal, revised after review by the catcrypt-compiler maintainers
> (PR #16).** It supersedes the arrangement in [`CATCRYPT-PORT.md`](CATCRYPT-PORT.md) (port, do
> not depend).

# A library shared with catcrypt-compiler

MachineChecked and catcrypt-compiler both prove that machine code computes a stated function,
by an ascent from the machine to a logical program. They share their origins (MachineChecked's
`Ascent` and `Lprog` came from catcrypt-compiler), and both need the same generic pieces.
Instead of two copies that drift apart, the generic pieces should be one package that both
require.

## The arrangement

- **One package, required by both.** Working name `ascent`. It depends on Lean core only, not
  Mathlib. A Lake workspace has one Mathlib revision, so a Mathlib-free package does not force
  the two users onto the same one. MachineChecked's `Ascent` and `Lprog` already import nothing
  else; catcrypt-compiler's generic layer uses only `Set` notation and `Relator`, both
  replaceable. The model is `spitters/CatCrypt-core`, which catcrypt-compiler already requires
  in the same way. Licence: dual MIT/Apache-2.0.
- **What it holds** (generic: no instruction set, no execution context):
  - runs (`steps`, `Reaches`) over a step relation with events,
    `step : σ → Outcome (σ × List E) → Prop`, whose outcomes are a state, `trap` (safe) or
    `wrong` (unsafe);
  - correspondence, starting from catcrypt-compiler's `RefinesP` and `RefinesO`, with
    MachineChecked's `Corres` over `Reaches` and catcrypt-compiler's `CorresIsaRun` as
    instances;
  - the safety judgement `SafeN`, which ignores events, with contracts in continuation form
    and the bridge `SafeN.of_reaches`;
  - `SContract`: total, framed contracts with a two-run constant-time field, generic in state,
    locations and trace;
  - the low logical program, Lprog: expressions, typed operations, syntax, and the step
    relation with a call stack and external calls, where the effect of calls and returns is a
    field of the instruction set;
  - later, a symbolic executor at Lprog (MachineChecked's milestone B).
- **Machine models**, in the shared package or a second small one: catcrypt-compiler's
  `IsaMachine` and its x86-64, AArch64 and RV64 models and decoders. MachineChecked's copies of
  the x86-64 and AArch64 models are then deleted. The RV64 model is based on riscv-zkvm's RV64IM
  decode and execute, keeping catcrypt-compiler's Zkt leakage; MachineChecked proves that
  `stepSp1` refines it outside `ecall`.
- **What stays with each user.**
  - MachineChecked: riscv-zkvm's `stepSp1` and the RISC-V lift onto Lprog, the ELF loader and
    SP1's context, the trust ladder, the case studies.
  - catcrypt-compiler: the compiler, its dialects, its backends, the cryptographic proofs, and
    the Jasmin export, which keeps Jasmin's linear syntax with a proved translation from the
    shared Lprog.
- **Layer 1.** catcrypt-compiler's `NFProg` (an intrinsically typed program over a dialect, with
  a denotation, a leakage semantics and a proved compilation to Lprog) over a word-level dialect
  is the seed of the shared layer 1. It needs a dialect with flat memory and pointers, of which
  named regions are a proved abstraction, and a relational reading of external calls. The first
  form of lift 2 needs no new simulation proof: an untrusted decompiler proposes a program `P`,
  its compilation `exportR P` gives a reference Lprog, and catcrypt-compiler's validator checks
  the lifted Lprog against it. This accepts code that differs from catcrypt-compiler's output
  by register allocation and scheduling. Code from rustc and LLVM, such as zip-2005, needs a
  more general checker.

| MachineChecked | catcrypt-compiler | VeIR / MLIR |
|---|---|---|
| layer 1 | `NFProg` over `jasminDialect` | arith, memref |
| — | — | llvm, riscv: SSA over ISA operations |
| layer 0.5 | Lprog (shared) | — |
| layer 0 | `IsaMachine` instances | — |

## Agreed

1. **Licence:** dual MIT/Apache-2.0.
2. **No Mathlib** in the shared package.
3. **Outcomes:** `trap` and `wrong` are distinct.
4. **Events in the step**, ignored by `SafeN`, with `E = Unit` for SP1; external-call
   specifications return events too.
5. **Calls:** the effect of a call and the check of a return are a field of the instruction
   set, so that x86's pushed return address fits as well as a link register.
6. **Correspondence** starts from `RefinesP`/`RefinesO`.
7. **RV64:** catcrypt-compiler keeps its own RV64 machine, based on riscv-zkvm's decode and
   execute, and `stepSp1` is proved to refine it outside `ecall`.
8. **Syntax:** typed operations and a generic state; the array operands `arr`/`arrIdx` stay or
   are expressible as `load`/`store`.

## Open

1. **Home and name** of the package, and whether the machine models go in it or in a second
   package.
2. **Relational correspondence.** `RefinesP` takes a partial function `C → Option D`; Lprog's
   step is a relation (an external call has many results). Either a relational `RefinesP`, or
   `Corres` as an instance only on deterministic machines.
3. **`SContract` and `SafeN`.** `SContract` is total (a run exists), which suits kernels;
   `SafeN`'s contracts are partial, because a whole program may trap or panic. Both stay; is
   there a bridge from `SContract` to a `SafeN` contract on deterministic machines? Composing
   `ct` across `Lcall` needs its own rule.
4. **Toolchain.** The package that requires riscv-zkvm (for the RV64 model) inherits its
   toolchain: v4.33.0 on the `sp1-backend` branch that has `stepSp1`, against v4.33.1 in
   catcrypt-compiler. Either that branch moves to v4.33.1 (upstream work; MachineChecked keeps
   riscv-zkvm unmodified) or both pin a common version. The Mathlib-free generic package avoids
   the problem.
5. **Leakage.** Whether the event type follows catcrypt-compiler's leakage model exactly, and
   where speculative constant time lives: a speculative semantics over the shared Lprog, or per
   backend, as in catcrypt-compiler's x86 backend today.
6. **CatCrypt kernels.** Requiring catcrypt-compiler for its kernel proofs pulls in its whole
   closure (Mathlib, CatCrypt-core, ParamTransfer, Veir, CompPoly, hax-lean). Until that is
   practical, MachineChecked keeps its own proofs of the kernels it verifies.

## Order of work

1. **Agree this note** (PR #16).
2. **MachineChecked aligns milestone A** (PR #17): events in the step, and calls and returns as
   a field of the instruction set.
3. **Create the package**, jointly. MachineChecked moves `Ascent` (runs, outcomes, `SafeN`) and
   `Lprog`; catcrypt-compiler moves `RefinesP`/`RefinesO` and `SContract`; the `Corres`
   instances are reconciled. Each project then requires it and deletes its copies, on its own
   schedule.
4. **Machine models.** `IsaMachine` and the models move; the RV64 model is rebased on
   riscv-zkvm; MachineChecked proves that `stepSp1` refines it outside `ecall`; the toolchains
   are aligned.
5. **Layer 1**, from `NFProg`; lift 2 by validation for catcrypt-compiler's kernels first, a
   general checker for rustc code later.
