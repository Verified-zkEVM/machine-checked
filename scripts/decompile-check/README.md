# decompile-check

Tests `decompile --to pancake` by running. Nothing on the path from a binary to Pancake is
proved yet ([`Tools/README.md`](../../Tools/README.md)), so this is what supports it: decompile
a binary, compile the Pancake output with Flapjack, run both binaries on the same inputs, and
compare their behaviour.

## What is compared

Each kind of input has its own notion of observable behaviour and its own reference machine:

| input | observable behaviour | reference |
| --- | --- | --- |
| Flapjack image | the FFI calls in order (name, configuration bytes, array before and after) and how the run ends | flapjack-flip's machine (riscv-zkvm's `step` and the image conventions) |
| SP1 guest (an ELF built by rustc) | the system calls in order (number, arguments, bytes read or written) and the exit code | SP1's executor |
| bare guest (the same Rust for `aarch64-unknown-none-softfloat` or `x86_64-unknown-none`) | as for an SP1 guest; it has four of SP1's system calls, under the same numbers | Unicorn (QEMU's CPU emulation) |

Two binaries agree on a test when their behaviour is identical on each of five inputs.

Whatever the original instruction set, the Pancake is compiled by Flapjack to RISC-V and run
on the interpreters here, so that only the decompiler is under test. Neither the compiler nor the reference is this repository's. The
interpreters are fast, and each is compared with its reference on every test: with
flapjack-flip's machine output for output and step for step, and with SP1's executor on the
public values, exit code and instruction count. Bare guests are run by Unicorn directly.

## Files

| file | what |
| --- | --- |
| `check.py` | The driver: `build`, `rust`, `reference`, `sp1-reference`, `self-test`, `run`, `mutants`, `limits`. `check.py --help` describes each. |
| `rv64.py` | A plain RV64IM interpreter, shared by the two runners. |
| `fjrun.py` | Runs a Flapjack image on the test inputs and prints its behaviour in `flip-check run`'s format. A long run takes minutes on riscv-zkvm (whose memory is a function) and under a second here. |
| `sp1run.py` | Runs an SP1 guest, or the image a decompiled guest (SP1 or bare) is recompiled to, with SP1's system calls as riscv-zkvm models them. |
| `barerun.py` | Runs a bare AArch64 or x86-64 guest on Unicorn with the same system calls. Needs the Python package `unicorn`. |
| `x86dis.py` | Compares `decompile`'s x86-64 decoder with `llvm-objdump` on every instruction of a guest: where each starts, and its mnemonic. |
| `run/` | Per instruction set, the instruction kinds the tests run; `decompile --table` marks these as run in each `LIMITS.md`. Written by `decompile --kinds` from the output of `sp1run.py --coverage --instructions` or `barerun.py --coverage --instructions`. |
| `sp1ref/` | `sp1ref GUEST.elf ...`: SP1's executor (`sp1-sdk`) on the same inputs. A separate Rust project. |
| `fjc/` | `fjc SOURCE.pnk`: Flapjack's `RiscV.NativeSource.compile` as a command. A separate Lean project on Flapjack's toolchain; the first `lake build` (after `lake exe cache get`) is slow. |
| `rust/` | 41 hand-written guests, each testing one thing: sorting, hashing, trait objects, function pointers, jump tables, 128-bit and floating-point arithmetic, formatting, collections, recursion and tail calls, panics, and inline assembly for instructions and control flow rustc does not emit (`k_asm_*` for RISC-V, `k_arm`, `k_x86`). One source tree for three machines: `src/lib.rs` is shared, on SP1's library for SP1 and on `src/bare.rs` (start-up, stack, allocator, system calls, panic handler, linked by `bare.x`) for bare targets. Files starting with `// SP1 only` (RISC-V assembly, `HashMap`) are not built for bare targets; `k_arm` and `k_x86` run their assembly on their own machine and the same function in Rust on the others. |
| `gen_rust.py` | Random Rust guests: typed arithmetic at every width, loops, `match`, functions, arrays, calls through pointers and trait objects, occasional panics. |
| `gen_asm.py` | Test images of hand-assembled code: every instruction the lift covers with edge-case operands, and compiler-style control flow that follows the calling convention. With `w32`, every 32-bit instruction. |
| `gen_pancake.py` | Random Pancake programs using the whole language: globals, pairs, exceptions, recursion, tail calls, `break`/`continue`, every memory width, distant memory, several FFI names. |
| `hand/` | Hand-written Pancake programs, one per feature. |

## Running it

```sh
lake build decompile
(cd scripts/decompile-check/fjc && lake exe cache get && lake build)
FJC=scripts/decompile-check/fjc/.lake/build/bin/fjc
C=scripts/decompile-check

# SP1 guests: the 41 hand-written and 240 generated (needs SP1's toolchain, `cargo prove`)
python3 $C/check.py rust work guests --seed 1 --count 240
python3 $C/check.py build $FJC guests
python3 $C/check.py run $FJC guests
(cd $C/sp1ref && cargo build --release)
python3 $C/check.py sp1-reference $C/sp1ref/target/release/sp1ref guests

# bare guests for AArch64 and x86-64 from the same sources
# (needs both rustc targets and `pip install unicorn`)
for T in aarch64 x86-64; do
  python3 $C/check.py rust work-$T guests-$T --seed 1 --count 240 --target $T
  python3 $C/check.py build $FJC guests-$T
  python3 $C/check.py run $FJC guests-$T
done
python3 $C/x86dis.py llvm-objdump guests-x86-64/*/guest.elf

# the instruction tables of the LIMITS.md files
python3 $C/check.py limits

# images: 100 assembled, 60 with every 32-bit instruction, 130 generated, 2 by hand
python3 $C/gen_asm.py 1 100 corpus
python3 $C/gen_asm.py 1 60 corpus w32
python3 $C/gen_pancake.py 1 130 corpus
cp -R $C/hand/* corpus/
python3 $C/check.py build $FJC corpus
python3 $C/check.py run $FJC corpus

# flapjack-flip's 120 tests
python3 $C/check.py run $FJC ../flapjack-flip/tests
```

With flapjack-flip built, `check.py reference .../flip-check DIR` confirms on its machine every
`expected.txt` that `build` wrote for an image.

## Results

As of 2026-11-16, with Flapjack at the revision flapjack-flip pins (`95aa081`) as the compiler.

### Guests

One set of Rust sources at `opt-level = 3`, built with SP1 6.10.0 (`cargo prove build`, rustc
1.93) and for `aarch64-unknown-none-softfloat` and `x86_64-unknown-none` (rustc 1.98,
`relocation-model=static` for x86-64).

| | RISC-V (SP1) | AArch64 | x86-64 |
| --- | --- | --- | --- |
| hand-written (`rust/`) | 41 | 36 | 36 |
| generated (`gen_rust.py`, seed 1, 240) that halt on every input | 226 | 227 | 227 |
| **pass** | **267 / 267** | **263 / 263** | **263 / 263** |
| reference | SP1's executor | Unicorn 2.1 | Unicorn 2.1 |
| steps, recompiled / original | 7.0 | 10.4 | 15.5 |
| instructions run by some input | 48% | 32% | 31% |
| instruction kinds lifted, and run | 64, 63 | 91, 91 | 110, 110 |
| one-bit changes reached, and caught | 124, 102 | 71, 38 | 99, 51 |
| functions, and those left as a loop over their blocks | 45,679, 2,740 (6%) | 13,517, 403 (3%) | 13,501, 557 (4%) |

- SP1's executor agrees with `sp1run.py` on all 267 guests: public values, exit code and
  instruction count, on each input.
- The x86-64 decoder agrees with `llvm-objdump` on all 1,062,210 instructions of the 263 guests
  (instruction boundaries and mnemonics; operands are not compared).
- About one run in six ends in a panic (exit code 1, after a message on file 2).
- Every lifted instruction kind is run except RISC-V's `fence`. Some are run only by the
  hand-written assembly guests: `k_asm_*`, `k_arm` (nine kinds), `k_x86` (eleven). The tables
  in each `MachineChecked/{RiscV,ARM,X86}/LIMITS.md` list them.
- The one-bit changes were measured on 2026-11-15 for RISC-V (265 guests) and AArch64 (262).
- A decompiled SP1 guest is 28,000 to 65,000 lines of Pancake; a bare one 5,600 to 64,000 (less
  runtime). Flapjack compiles those timed, up to 45,000 lines, in 5 to 10 seconds.

### Flapjack images

| tests | source | pass | steps, recompiled / original |
| --- | --- | --- | --- |
| flapjack-flip `tests/` | 20 hand-written, 100 from its generator (seed 0) | 120 / 120 | 13.5 |
| flapjack-flip's generator | seeds 1 and 2 | 200 / 200 | 14.2 |
| `gen_pancake.py`, `gen_asm.py`, `hand/` | seed 1: 130, 100, 2 | 232 / 232 | 13.3 |
| `gen_asm.py … w32` | seed 1 | 60 / 60 | 46.8 |

For the first 552, flapjack-flip's machine agreed with `fjrun.py` on every output and step count
(2026-11-13). Coverage and mutation on those, measured then: 76%, 74%, 69% and 96% of
instructions run, and 53/120, 74/200, 45/130 and 65/100 changes caught. The 60 `w32` images have
no independent reference (see below).

## What this does not show

- **It is testing, not proof.** The one-bit-change row measures how sharp the tests are: flip
  the low bit of one value the decompiled program assigns or stores, and see if a test fails.
  For SP1 guests, of 265 changes (one per guest), 124 are reached by some input and 102 of those
  are caught; none of the 141 unreached ones is. The 22 reached but not caught were not traced
  individually. On AArch64 and x86-64 only about half of the reached changes are caught, since
  changes also hit flags and values computed for them, which are read less often
  (`check.py mutants` writes each change and its outcome to `result.txt`). The 33 uncaught on
  AArch64 were inspected: saves and restores of callee-saved registers, differences computed
  only for a comparison, values overwritten before use. A reached change can be invisible when
  its low bit does not matter afterwards. Changes are made to program statements, not to the
  functions that write the memory image (a third of assignments, seldom read; with those, 52 of
  171 reached changes were caught). So a wrong translation of an instruction that the tests run
  and whose result they observe is very likely caught; one in unreached code is not, and about
  half the guests' instructions (panic paths, formatting, unused runtime) are never run.
- **One compiler, one optimisation level.** Every guest comes from rustc at `opt-level = 3`
  (1.93 for SP1, 1.98 for bare). Other compilers, settings and hand-written assembly have other
  shapes; only `rust/src/bin/k_asm_flow.rs` tests some by hand (a jump table in code, a call
  through `t0`, `jalr` with one register as both target and link).
- **No independent reference for 32-bit instructions in images.** flapjack-flip's machine uses
  an older riscv-zkvm that decodes only `addiw` of them. For guests, SP1's executor is the
  reference (`k_asm_w`, and whatever rustc emits); for the 60 `w32` images it is `fjrun.py`,
  whose interpreter was checked against SP1's executor.
- **A bare guest's reference is a processor emulator, not a Lean model.** Unicorn is neither
  arm64-semantics nor Kraken, so agreement of the lifts with those models is not tested. Bare
  images run with unaligned accesses allowed, which Pancake's semantics does not describe
  (`LIMITS.md`).
- **Six system calls**: `HALT`, `WRITE`, `COMMIT`, `COMMIT_DEFERRED_PROOFS`, `HINT_LEN` and
  `HINT_READ`. A guest that uses a precompile (`SHA_EXTEND` and similar) is rejected by the
  runner here, not by the decompiler, and is untested.
- **The machine that runs a recompiled guest is defined only by the runner.** Its heap is the
  guest's whole address space, with Pancake's stack and code above it. No such machine is
  defined in Lean yet.
- **Unrecognised jump tables make the program give up**, not misbehave. Targets are found as
  addresses in data and, on AArch64 and x86-64, as offsets from an address formed just before
  the jump; other table shapes are missed. Every give-up point in the output is numbered and
  described.
- **Image memory.** A decompiled Flapjack image gets half the original heap and stack.
- **Step limits.** Image runs stop at 2,000,000 steps; guests at 20,000,000 (400,000,000 for
  the recompiled guest).
- **Flapjack's compile time** grows with the square of a function's length and much faster
  with loop nesting depth (24 nested loops do not compile in five minutes). Lift 2 therefore
  moves long runs of statements out into separate functions, and leaves a function that would
  nest more than ten loops as a loop over its blocks.
- **No names, variables or types are recovered.** The output is correct on these tests and
  structured, but it is not what the programmer wrote.
