> **Status (2026-11-11): agreed, the design of record (PR #16).** Revised after two reviews by
> the catcrypt-compiler maintainers. It supersedes the arrangement in
> [`CATCRYPT-PORT.md`](CATCRYPT-PORT.md) (port, do not depend).

# A library shared with catcrypt-compiler

MachineChecked and catcrypt-compiler both prove that machine code computes a stated function,
by an ascent from the machine to a logical program. They share their origins (MachineChecked's
`Ascent` and `Lprog` came from catcrypt-compiler), and both need the same generic pieces.
Instead of two copies that drift apart, the generic pieces should be one package that both
require.

## The arrangement

- **One package, required by both,** in a repository of its own under a neutral name (working
  name `ascent`). It depends on Lean core only, not Mathlib. A Lake workspace has one Mathlib
  revision, so a Mathlib-free package does not force the two users onto the same one. The model
  is `spitters/CatCrypt-core`, which catcrypt-compiler already requires in the same way.
  Licence: dual MIT/Apache-2.0.
- **Getting there is a move on one side and a refactor on the other.** MachineChecked's
  `Ascent` and `Lprog` import nothing outside themselves. On catcrypt-compiler's side,
  `RefinesP`/`RefinesO` (`HaxAscent/Ascent/Refines.lean`) import nothing, and `SContract` is
  close: its closure reaches `Mathlib.Data.BitVec`, `Data.Set.Disjoint`, `Order.SetNotation`
  and `Tactic.Abel`, through `SepLogic/ByteMem` and `SepLogic/Core`. catcrypt-compiler's Lprog
  and its machine models are not: the closures of `VIR/LprogIsa` (112 modules) and
  `VIR/IsaMachine` (159) reach 19 Mathlib modules, CatCrypt-core's `Heap`/`Location`, Nominal
  and ParamTransfer, through `JasminLsemMemChecked` and the Jasmin types. Their semantics must
  be split from the CatCrypt-core heap before they can move.
- **What it holds** (generic: no instruction set, no execution context):
  - runs (`steps`, `Reaches`) over a step relation with events,
    `step : σ → Outcome (σ × List E) → Prop`, whose outcomes are a state, `trap` (safe) or
    `wrong` (unsafe);
  - correspondence: a relational `RefinesR (step : C → D → Prop)`, with a progress clause as
    well as the related end, and catcrypt-compiler's `RefinesP` (at
    `fun c d => sem c = some d`) and `RefinesO` as its deterministic instances; MachineChecked's
    `Corres` over `Reaches` and catcrypt-compiler's `CorresIsaRun` are instances too;
  - the safety judgement `SafeN`, which ignores events, with contracts in continuation form
    and the bridge `SafeN.of_reaches`;
  - `SContract`: total, framed contracts with a two-run constant-time field, generic in state,
    locations and trace, and a bridge from `SContract` to a `SafeN` contract on deterministic
    machines, so that a kernel's `SContract` serves as a contract at an `Lcall` (the route of
    `SafeN.of_corres`; the `ct` field has no counterpart, since `SafeN` ignores events);
  - the low logical program, Lprog: expressions, typed operations, syntax, and the step
    relation with a call stack and external calls, where the effect of calls and returns is a
    field of the instruction set;
  - later, a symbolic executor at Lprog (MachineChecked's milestone B).
- **Machine models,** in a second package, so that the generic package does not inherit
  riscv-zkvm's toolchain: catcrypt-compiler's `IsaMachine` and its x86-64, AArch64 and RV64
  models and decoders. MachineChecked's copies of the x86-64 and AArch64 models are then
  deleted. The RV64 model is based on riscv-zkvm's RV64IM decode and execute, keeping
  catcrypt-compiler's Zkt leakage; MachineChecked proves that `stepSp1` refines it outside
  `ecall`. catcrypt-compiler has deferred its AArch64 and RV64 work for now, so this package
  comes after the generic one.
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
  the lifted Lprog against it. Once catcrypt-compiler replaces the validation of every pass
  except allocation by proofs, the validator compares across register allocation only, so it
  accepts code that differs from catcrypt-compiler's output by register allocation. Tolerating
  scheduling needs a checker of its own. Code from rustc and LLVM, such as zip-2005, needs a
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
6. **Correspondence** is a relational `RefinesR` with a progress clause; `RefinesP`/`RefinesO`
   are its deterministic instances.
7. **RV64:** catcrypt-compiler keeps its own RV64 machine, based on riscv-zkvm's decode and
   execute, and `stepSp1` is proved to refine it outside `ecall`.
8. **Syntax:** typed operations and a generic state; the array operands `arr`/`arrIdx` stay or
   are expressible as `load`/`store`.
9. **`SContract` and `SafeN`** both stay, with a bridge from `SContract` to a `SafeN` contract
   on deterministic machines, in the package.
10. **Home:** the generic package in a repository of its own under a neutral name; the machine
    models in a second package.
11. **Toolchain:** a common pinned version, v4.35.0 now (catcrypt-compiler's) and v4.36 after
    catcrypt-compiler's upgrade. The Mathlib-free generic package follows both projects; only
    the machine-model package, which requires riscv-zkvm, needs riscv-zkvm's `sp1-backend`
    (v4.33.0 today) at the common version. That is upstream work: MachineChecked keeps
    riscv-zkvm unmodified.

## Open

1. **Name** of the package.
2. **Constant time across calls.** Composing `SContract`'s `ct` across `Lcall` needs its own
   rule.
3. **Leakage.** Whether the event type follows catcrypt-compiler's leakage model exactly, and
   where speculative constant time lives: a speculative semantics over the shared Lprog, or per
   backend, as in catcrypt-compiler's x86 backend today.
4. **CatCrypt kernels.** Requiring catcrypt-compiler for its kernel proofs pulls in its whole
   closure (Mathlib, CatCrypt-core, ParamTransfer, Veir, CompPoly, hax-lean). Until that is
   practical, MachineChecked keeps its own proofs of the kernels it verifies.

## Order of work

1. **Agree this note** (PR #16).
2. **MachineChecked aligns milestone A** (PR #17, merged without them): events in the step
   (#18), and calls and returns as a field of the instruction set (#19), as follow-up PRs
   before the package is created.
3. **Create the package**, jointly, in two stages.
   - First, what moves as it is: MachineChecked's `Ascent` (runs, outcomes, `SafeN`) and
     `Lprog`, and catcrypt-compiler's `RefinesP`/`RefinesO`, as instances of `RefinesR`. The
     `Corres` instances are reconciled.
   - Then `SContract`, once its Mathlib imports are replaced, with its bridge to `SafeN`.
   - Each project then requires the package and deletes its copies, on its own schedule.
     catcrypt-compiler's Lprog joins the shared one after its semantics are split from the
     CatCrypt-core heap.
4. **Layer 1**, from `NFProg`; lift 2 by validation for catcrypt-compiler's kernels first, a
   general checker for rustc code later.
5. **Machine models**, when catcrypt-compiler takes up AArch64 and RV64 again. `IsaMachine` and
   the models move to the second package, after the same split from the CatCrypt-core heap; the
   RV64 model is rebased on riscv-zkvm; MachineChecked proves that `stepSp1` refines it outside
   `ecall`; riscv-zkvm's `sp1-backend` moves to the common toolchain. Neither step 3 nor step 4
   waits on this step.
