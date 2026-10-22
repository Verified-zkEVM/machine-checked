> **Status (2026-10-22): proposal, to agree with the catcrypt-compiler maintainers.** It
> supersedes the arrangement in [`CATCRYPT-PORT.md`](CATCRYPT-PORT.md) (port, do not depend).

# A library shared with catcrypt-compiler

MachineChecked and catcrypt-compiler both prove that machine code computes a stated function,
by an ascent from the machine to a logical program. They share their origins (MachineChecked's
`Ascent` and `Lprog` came from catcrypt-compiler), and both need the same generic pieces.
Instead of two copies that drift apart, the generic pieces should be one package that both
require.

## The arrangement

- **One package, required by both.** Working name `ascent`. It depends on Lean core and
  Mathlib only, so that its toolchain is easy to keep in step with both users. The model is
  `spitters/CatCrypt-core`, which catcrypt-compiler already requires in the same way.
- **What it holds** (generic: no instruction set, no execution context):
  - runs (`steps`, `Reaches`);
  - correspondence, `Corres`, in catcrypt-compiler's total-correctness form;
  - the safety judgement `SafeN` over a step relation with `trap` and `wrong` outcomes, with
    contracts in continuation form, and the bridge `SafeN.of_reaches`;
  - the low logical program: expressions, syntax, the step relation with a call stack and
    external calls, and the shared operations;
  - later, a symbolic executor at Lprog (MachineChecked's milestone B).
- **What stays with each user.**
  - MachineChecked: riscv-zkvm's `stepSp1` and the RISC-V lift onto Lprog, the ELF loader and
    SP1's context, the trust ladder, the case studies.
  - catcrypt-compiler: the compiler, its dialects, its x86 and RV64 backends, the
    cryptographic proofs.
- **Machine models.** The x86-64 and AArch64 models MachineChecked copied are required from
  wherever catcrypt-compiler keeps them, not copied. If catcrypt-compiler adopts riscv-zkvm's
  `stepSp1` for its RV64 backend, the RISC-V lift can move into the shared package too.
- **CatCrypt kernels.** MachineChecked imports the kernels and catcrypt-compiler's proofs of
  them, and proves only the bridge to `stepSp1`, instead of re-proving each kernel.

## What has to be agreed

1. **Home, name and licence.** MachineChecked is Apache-2.0; catcrypt-compiler is MIT.
2. **Toolchain.** A Lake workspace has one toolchain. catcrypt-compiler is on Lean v4.33.1;
   MachineChecked is on v4.33.0, because `stepSp1` exists only on riscv-zkvm's `sp1-backend`
   branch. Either that branch moves to v4.33.1 (upstream work; MachineChecked keeps
   riscv-zkvm unmodified) or both pin a common version. This blocks requiring
   catcrypt-compiler directly; the small shared package is less sensitive to it.
3. **The shape of the shared concepts.** MachineChecked's design note
   [`docs/design/Lprog.md`](../design/Lprog.md) is the proposal for Lprog and `SafeN`. Where
   it changes a concept catcrypt-compiler already has, the change is agreed, not imposed:
   - `Corres` stays in catcrypt-compiler's form (the run is defined and ends related). The
     note's §5 restates it in continuation form; for the shared package, that statement
     becomes a contract over `SafeN` beside `Corres`, not a replacement for it.
   - Lprog's syntax: catcrypt-compiler's `Lopn` carries a mnemonic string with operand lists;
     the proposal has typed operations, a register type parameter, calls, tail calls,
     external calls and `Labort`. The Jasmin export would target the new syntax, or keep a
     translation.
4. **RV64.** Whether catcrypt-compiler's RV64 backend moves to riscv-zkvm's `stepSp1`.

## Order of work

1. Agree items 1–3 with the maintainers.
2. Create the package from MachineChecked's `MachineChecked/Ascent` and `MachineChecked/Lprog`
   (after milestone A) and catcrypt-compiler's generic ascent, reconciled. MachineChecked
   requires it and deletes its copies; catcrypt-compiler follows on its own schedule.
3. Align the toolchains, then require catcrypt-compiler's kernels and machine models.
