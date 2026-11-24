# Roadmap: rustc's lean verifiers on x86-64 and AArch64

The goal: prove what rustc emits for three verifiers, on x86-64 and on AArch64, down to each
instruction set's model, by this repository's route (lift to Lprog, prove there, transfer down).
SIMD is out of scope here and comes after.

The verifiers and their specifications are those of
[leanEthereum/leanVM#837](https://github.com/leanEthereum/leanVM/pull/837), which proves the same
code directly on each instruction set over Kraken. That pull request is the reference: its
build, its specifications and its six end theorems.

## The end state

Six theorems, each pinned to Lean's three axioms and with no contract hypothesis:

| | AArch64 | x86-64 |
| --- | --- | --- |
| `lean_xmss::verify` | `xmss_verify_correct` | `xmss_verify_correct` |
| `lean_sphincs::verify` | `sphincs_verify_correct` | `sphincs_verify_correct` |
| the `no_std` leanVM verifier | `leanvm_verify_correct` | `leanvm_verify_correct` |

Each says what #837's says: from the function's entry in rustc's code, with the inputs laid out
as stated and enough stack, the machine **always** returns to the caller, with the stack pointer
restored, the callee-saved registers unchanged, memory unchanged outside the stack frame (and,
for leanVM, its decoded-proof and working areas), and in `X0` / `rax` the verdict of the
specification: `LeanXmss.verifyWithKeccak`, `Sphincs.verifyWithKeccak`, or `Proof.fromBytes`
then `verifyWith`, as `1` or `0`. A panic is never reached.

What differs from #837, by design:

- **AArch64 is stated over [arm64-semantics](ISA.md#aarch64-deepminds-arm64-semantics)**, which
  runs on bytes: no assembler, parser or layout model is trusted, and the theorem is about the
  linked binary. #837's AArch64 model is Kraken's.
- **The proofs go through Lprog**: one judgement, one tactic (`lsym`) and one way of stating
  contracts for both instruction sets, each lift proved once.

## What "better" means

The same theorems as #837, no weaker, and five claims against it, each measured:

1. **Less is trusted.** On AArch64 the theorem is about the linked bytes. On both instruction
   sets `GotAt` and the constant tables are facts checked against the image, not assumptions.
2. **Less proof per function**: lines of proof and build time, on the same functions.
3. **One statement for both instruction sets**: a function's contract is written once, over a
   neutral ABI. How much of the proof is shared is measured, not promised.
4. **Proofs survive a recompile**: change the rustc version or a flag, and count what breaks.
5. **A third instruction set is cheap**: RISC-V's lift is proved already.

Claim 2 is tested first (M0.5), before the infrastructure is built on it.

## The code

From #837's build (`formal/native/rustc/build.sh`): rustc 1.99.1, `*-unknown-linux-musl`,
`opt-level=3`, one codegen unit, fat LTO into a static library, `panic=abort` with a handler that
traps (`ud2`, `udf #0`), no SIMD (`-sse,-sse2`; `-neon`). Its committed assembly, per
instruction set:

| | functions | instructions |
| --- | --- | --- |
| leanXMSS and leanSPHINCS (one module) | 14 | about 4,200 |
| leanVM | 137 | about 15,500 |

What it asks of the tools:

- **Instructions.** Integer only. Every instruction kind the code uses is already lifted by
  `decompile` on both instruction sets (the `LIMITS.md` tables); the panic traps become
  `Labort`, so a proof shows them unreachable, as the end theorems require.
- **No system calls** on either instruction set: the execution context is empty.
- **Calls through the GOT** on x86-64: `memcpy` and `memset` (50 call sites), and about 110
  calls through a register. In a statically linked image the GOT is part of the image, so #837's
  assumption `GotAt` becomes a fact checked against it.
- **Constant data**: 17 read-only sections in leanVM (tables and constants the code reads).

## Where it lives

Under [`Examples/`](../Examples/README.md), as `Examples/LeanVerifiers/`, with a directory for
each instruction set as the other examples have (`ARM/`, `X86/`), the images in `Examples/elf/`
and the build that makes them beside `Examples/build.sh`. It is a Lake library of its own with
its own CI job: it depends on #837's specification packages and is some 150 functions per
image, and `lake build Examples` should need neither.

## Milestones

Each milestone ends in something checked. M0.5 is the gate; M1 to M3 are infrastructure; M4
and M6 are the proofs; M5 can run beside M2 to M4.

### M0. Groundwork

- **Input.** Link each static library into a statically linked, non-position-independent
  executable for each instruction set, with a stub entry, since `decompile` takes executables
  only. Check that each function's bytes are rustc's (as #837's `faithful.sh` does for its
  parse), pin the images by sha256, and record that the GOT slots hold `memcpy` and `memset`.
  *Done when* `decompile --to lprog` lifts every function of the four images with no `abort`
  but at the panic traps.
- **Specifications as a dependency.** Build #837's model packages (`Native`, `NativeRustc`,
  `NativeRustcVm` and the specifications they import) from this repository. They are on Lean
  v4.36.0, this repository on v4.36.0-rc2. *Done when* a module here imports
  `NativeRustc.Xmss.Verify` and the build has no warnings.
- **Constant data** ([#76](https://github.com/Verified-zkEVM/machine-checked/issues/76)): the
  read-only words the functions read, checked against the ELF like code, so a table is a fact,
  not an assumption. Needed on all three instruction sets, starting with the two here.

### M0.5. The early pilot

`keccak_f` and `memcpy` of the AArch64 signature image, each with its contract at Lprog against
#837's models, proved with `lsym` on the lift as it is (not yet proved, so nothing follows about
the machine). It measures claim 2: lines of proof and build time against #837's for the same
two functions.

*Done when* both contracts are proved and the numbers are written down. This is the gate: if
the route is not clearly cheaper, M3 is rethought before M1 and M2 are built.

### M1. One transfer theorem for any instruction set

RISC-V's simulation (`MachineChecked/RiscV/Lift/Transfer.lean`) is written against `stepSp1`.
Make it generic: an instruction set supplies, per instruction kind, that the lift of the
instruction matches one machine step; the framework gives `transfer`, `SafeN.of_contract` and
the equivalence. Built on `lprog/Lprog/Ascent` (`Refines.of_sim`).

- Calls and returns as a field of `Isa`
  ([#19](https://github.com/Verified-zkEVM/machine-checked/issues/19)): x86-64 keeps the return
  address on the stack.
- Flags as values ([#9](https://github.com/Verified-zkEVM/machine-checked/issues/9)): both
  instruction sets branch and select on flags (`cmov`, `setcc`, `csel`, `ccmp`).
- The execution context as a parameter
  ([#6](https://github.com/Verified-zkEVM/machine-checked/issues/6)), with the empty context for
  these verifiers and SP1 for RISC-V.

*Done when* RISC-V's transfer theorem is an instance of the generic one and every example still
checks.

### M2. Total correctness

`SafeN` is partial correctness: a run that traps or never ends meets every postcondition. The
end theorems say the verifier always returns.

- A judgement at Lprog for runs that end, with a loop rule over a measure (the total form of
  [#65](https://github.com/Verified-zkEVM/machine-checked/issues/65)) and contracts that compose
  with it.
- `lsym` carrying it: a function proved total by stepping, with loops by measure.
- Transfer to the machine: `Ascent.Equivalent` already preserves how a run ends (returning,
  trapping, running on), so a total judgement at Lprog with the lift's equivalence gives the
  machine's.

*Done when* a RISC-V example is proved total and the theorem holds of `stepSp1`.

### M3. Contracts and automation at the size of this code

- **The calling convention in contracts**
  ([#75](https://github.com/Verified-zkEVM/machine-checked/issues/75)) and **a shared memory
  vocabulary** ([#21](https://github.com/Verified-zkEVM/machine-checked/issues/21)), stated over
  an instruction-set-neutral ABI (argument `i`, result, stack pointer, callee-saved, frame), so
  that a function's contract is written once and instantiated for each instruction set: the
  statement is shared even where the proofs are not.
- **`lsym` at scale** ([#66](https://github.com/Verified-zkEVM/machine-checked/issues/66)):
  constant cost per step, so that unrolled Keccak and leanVM's largest functions are stepped
  in minutes. Measured on a RISC-V function of 700 instructions before and after.

*Done when* a contract over the neutral ABI is proved for RISC-V and its statement typechecks
for the other two, and `lsym`'s cost per step is flat on the benchmark.

### M4. AArch64

- **The judgement** over arm64-semantics' `Step`, with the empty context.
- **The lift proved**, by the M1 framework, for the integer instructions the code uses: about 65
  kinds, listed by `decompile --kinds` on the images.
- **The ladder** ([`Examples/`](../Examples/README.md)) recompiled for AArch64 and proved: the
  route end to end on small code.
- **The pilot**: `keccak_f`, `memcpy` and `memset` from the signature image, against #837's
  models. A checkpoint: if the effort per function is not well below #837's, revisit M3 before
  going on.
- **The verifiers**: leanXMSS and leanSPHINCS (14 functions), then leanVM (137), each function
  with its contract, composed to the three end theorems.

### M5. x86-64: the lift proved

Kraken's model is over assembly, not bytes, and this repository's x86-64 decoder is its own
(checked against LLVM, not proved). Choose in a design note between:

- **Lifting from Kraken's syntax**: parse rustc's assembly with Kraken's parser, checked as #837
  does (print, assemble, compare with rustc's bytes), so the model and the lift read the same
  instructions; or
- **Lifting from bytes** with this repository's decoder, trusted, and a check that each decoded
  instruction is the one Kraken's syntax gives.

Either way, Kraken must cover what the code uses: #837 pins a fork with `bt`/`bts`, indexed
addresses without a base, GOT slots and indirect calls (AeneasVerif/kraken#274). Pin the same,
or wait for it upstream.

Then the judgement over Kraken's step and the lift proved by the M1 framework. This can start
once M1 is done, beside M2 to M4.

### M6. x86-64: the verifiers

The M4 contracts, instantiated for x86-64 through the neutral ABI, proved against the x86-64
lift, and composed to the three end theorems.

## Issues on the way

| issue | where |
| --- | --- |
| [#76](https://github.com/Verified-zkEVM/machine-checked/issues/76) constant data checked against the ELF | M0 |
| [#19](https://github.com/Verified-zkEVM/machine-checked/issues/19), [#9](https://github.com/Verified-zkEVM/machine-checked/issues/9), [#6](https://github.com/Verified-zkEVM/machine-checked/issues/6) | M1 |
| [#65](https://github.com/Verified-zkEVM/machine-checked/issues/65) loop rule | M2, in its total form |
| [#75](https://github.com/Verified-zkEVM/machine-checked/issues/75), [#21](https://github.com/Verified-zkEVM/machine-checked/issues/21), [#66](https://github.com/Verified-zkEVM/machine-checked/issues/66) | M3 |
| [#10](https://github.com/Verified-zkEVM/machine-checked/issues/10) verify or replace the models | M5, for x86-64's decoder and model |
| [#62](https://github.com/Verified-zkEVM/machine-checked/issues/62), [#67](https://github.com/Verified-zkEVM/machine-checked/issues/67) cheap rebuilds, names by symbol | helpful at 150 functions per image; not blocking |
| [#68](https://github.com/Verified-zkEVM/machine-checked/issues/68), [#4](https://github.com/Verified-zkEVM/machine-checked/issues/4), SIMD | not needed here |

## Risks

- **Scale.** About 20,000 instructions per instruction set. #837 took roughly 200,000 lines of
  proof per instruction set for leanVM. Automation (M3) decides whether this route is cheaper;
  the M4 pilot measures it before the bulk of the work.
- **Total correctness** is new at Lprog: its loop rule and its composition with contracts are
  design work, not a port.
- **x86-64's trusted base**: the decoder, or Kraken's parser, plus a Kraken fork until it is
  upstream.
- **The code moving.** #837's build is pinned (rustc, flags, `SHA256SUMS`); the images here are
  pinned by hash, and a new build is a new target.
- **The specifications moving** with #837 while it is open: pin its commit, and follow it when
  it merges.
