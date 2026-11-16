# decompile-check

**The check of `decompile --to pancake`, by running.** Nothing is proved yet of the path from
a binary to Pancake ([`Tools/README.md`](../../Tools/README.md)), so this is what stands
behind it for now: decompile a binary, compile the Pancake text with Flapjack, run both
binaries on the same inputs, and compare what they do.

There are three kinds of binary, each with its own notion of what a run does and its own
machine to say so.

- **A Flapjack image.** What it does is flapjack-flip's notion: the FFI calls in order, each
  with its name, its configuration bytes and its array before and after, and how the run
  ends. The reference is flapjack-flip's machine (riscv-zkvm's `step` and the image
  conventions).
- **An SP1 guest**, an ELF that rustc built. What it does is its system calls in order, each
  with its number, its arguments and the bytes it reads from memory or writes to it, and
  the exit code. The reference is SP1's own executor.
- **A bare guest**, the same Rust built for AArch64 or x86-64 without an operating system
  (`aarch64-unknown-none-softfloat`, `x86_64-unknown-none`). What it does is its system
  calls and its exit code, as for an SP1 guest: it has four of SP1's system calls, under
  the same numbers. The reference is Unicorn, which is QEMU's emulation of the processor.

Two binaries agree on a test when these are identical on each of five inputs.

Whatever the instruction set of the original, the Pancake is compiled by Flapjack to
RISC-V and run on the interpreter here: the decompiler is what is tested, and a second
compiler from Pancake would test something else.

Neither the compiler nor the judge is this repository's. Flapjack compiles. The runs of
RISC-V code are on the interpreters here, which are fast, and each is compared with its
reference machine on every test: with flapjack-flip's machine output for output and step
for step, and with SP1's executor on the public values, the exit code and the number of
instructions. A bare guest is run by Unicorn itself.

## The pieces

| file | what |
| --- | --- |
| `check.py` | The driver: `build`, `rust`, `reference`, `sp1-reference`, `self-test`, `run`, `mutants`, `limits`. `check.py --help` says what each does. |
| `rv64.py` | A plain RV64IM interpreter, shared by the two runners. |
| `fjrun.py` | Runs a Flapjack image on the test inputs and prints what it does, as `flip-check run` prints it. riscv-zkvm holds memory as a function, so a long run takes minutes there and under a second here. |
| `sp1run.py` | Runs an SP1 guest, or the image that a decompiled guest (SP1 or bare) is recompiled to, in one world: SP1's system calls as riscv-zkvm models them. |
| `barerun.py` | Runs a bare guest for AArch64 or x86-64 on Unicorn, in the same world of system calls. Needs the Python package `unicorn`. |
| `x86dis.py` | Compares the x86-64 decoder of `decompile` with `llvm-objdump` on every instruction of a guest: where each starts, and its name. |
| `run/` | The kinds of instruction the tests run, for each instruction set: what `decompile --table` marks as run in each `LIMITS.md`. Written from `sp1run.py --coverage --instructions` or `barerun.py --coverage --instructions` by `decompile --kinds`. |
| `sp1ref/` | `sp1ref GUEST.elf ...`: SP1's executor (`sp1-sdk`) on the same inputs. A Rust project of its own. |
| `fjc/` | `fjc SOURCE.pnk`: Flapjack's `RiscV.NativeSource.compile` as a command. A Lean project of its own, on Flapjack's toolchain; `lake build` in it (after `lake exe cache get`) takes a while the first time. |
| `rust/` | The guests written by hand, 41 of them, each for one thing: sorting, hashing, trait objects, function pointers, jump tables, 128-bit and floating-point arithmetic, formatting, collections, recursion and tail calls, panics, and inline assembly for the instructions and the control flow rustc does not emit (`k_asm_*` for RISC-V, `k_arm`, `k_x86`). One source for three machines: `src/lib.rs` is what they share, on SP1's library for an SP1 guest and on `src/bare.rs` (a start, a stack, an allocator, the system calls, a panic handler) for a bare one, linked by `bare.x`. A file that starts with `// SP1 only` is not built for the bare targets (RISC-V assembly, and `HashMap`); `k_arm` and `k_x86` run their instructions on their own machine and the same function in Rust on the others. |
| `gen_rust.py` | Random guests in Rust: typed arithmetic of every width, loops, `match`, functions, arrays, calls through pointers and trait objects, and now and then a panic. |
| `gen_asm.py` | Test images of hand-assembled code: every instruction the lift covers, with edge-case operands, and the control flow of a compiler that follows the calling convention. Not from Flapjack. With `w32`, every 32-bit instruction. |
| `gen_pancake.py` | Random Pancake programs that use the whole language: globals, pairs, exceptions, recursion, tail calls, `break` and `continue`, every memory width, memory far from its start, several FFI names. |
| `hand/` | Pancake programs written by hand for one thing each. |

## Running it

```sh
lake build decompile
(cd scripts/decompile-check/fjc && lake exe cache get && lake build)
FJC=scripts/decompile-check/fjc/.lake/build/bin/fjc
C=scripts/decompile-check

# SP1 guests: the 41 by hand and 240 generated (needs SP1's toolchain, `cargo prove`)
python3 $C/check.py rust work guests --seed 1 --count 240
python3 $C/check.py build $FJC guests
python3 $C/check.py run $FJC guests
(cd $C/sp1ref && cargo build --release)
python3 $C/check.py sp1-reference $C/sp1ref/target/release/sp1ref guests

# bare guests for AArch64 and x86-64: the same sources (needs the two rustc targets and,
# for Python, `pip install unicorn`)
for T in aarch64 x86-64; do
  python3 $C/check.py rust work-$T guests-$T --seed 1 --count 240 --target $T
  python3 $C/check.py build $FJC guests-$T
  python3 $C/check.py run $FJC guests-$T
done
python3 $C/x86dis.py llvm-objdump guests-x86-64/*/guest.elf

# the instruction tables of the LIMITS.md
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

With flapjack-flip built, `check.py reference .../flip-check DIR` confirms on its machine
every `expected.txt` that `build` wrote for an image.

## Results

On 2026-11-16, with Flapjack at the revision flapjack-flip pins (`95aa081`) as the compiler.

### Guests

One set of Rust sources, built for three machines: SP1 6.10.0 (`cargo prove build`, rustc
1.93), and `aarch64-unknown-none-softfloat` and `x86_64-unknown-none` (rustc 1.98,
`relocation-model=static` for x86-64), all at `opt-level = 3`.

| | RISC-V (SP1) | AArch64 | x86-64 |
| --- | --- | --- | --- |
| by hand (`rust/`) | 41 | 36 | 36 |
| generated (`gen_rust.py`, seed 1: 240), that halt on every input | 226 | 227 | 227 |
| **pass** | **267 / 267** | **263 / 263** | **263 / 263** |
| reference | SP1's executor | Unicorn 2.1 | Unicorn 2.1 |
| steps, recompiled over original | 7.0 | 10.4 | 15.5 |
| instructions some input runs | 48% | 32% | 31% |
| kinds of instruction lifted, and run | 64, 63 | 91, 91 | 110, 110 |
| one-bit changes reached, and caught | 124, 102 | 71, 38 | 99, 51 |
| functions, and those that are a loop over their blocks | 45,679, 2,740 (6%) | 13,517, 403 (3%) | 13,501, 557 (4%) |

- **SP1's executor agrees with `sp1run.py` on all 267**: the public values, the exit code and
  the number of instructions, on each of the five inputs.
- **The x86-64 decoder agrees with `llvm-objdump`** on all 1,062,210 instructions of the 263
  guests: where each starts, and its name (`x86dis.py`).
- About one run in six ends in a panic (exit code 1, after the message on file 2).
- **Which instructions are lifted, and which of those the tests run**, is the table of each
  instruction set's `LIMITS.md` (`MachineChecked/{RiscV,ARM,X86}/LIMITS.md`). Every lifted
  kind is run but RISC-V's `fence`. Some are run only by the guests that write them by
  hand: `k_asm_*`, `k_arm` (nine kinds), `k_x86` (eleven).
- The one-bit changes of RISC-V were measured on 2026-11-15, on 265 of the guests, and
  AArch64's on 262.
- A decompiled SP1 guest is 28,000 to 65,000 lines of Pancake, a bare one 5,600 to 64,000:
  it has less of a runtime. Flapjack compiled the ones timed, of up to 45,000 lines, in 5
  to 10 seconds.

### Flapjack images

| tests | from | pass | steps, recompiled over original |
| --- | --- | --- | --- |
| flapjack-flip `tests/` | 20 by hand, 100 from its generator, seed 0 | 120 / 120 | 13.5 |
| flapjack-flip's generator | seeds 1 and 2 | 200 / 200 | 14.2 |
| `gen_pancake.py`, `gen_asm.py`, `hand/` | seed 1: 130, 100, and 2 | 232 / 232 | 13.3 |
| `gen_asm.py ... w32` | seed 1 | 60 / 60 | 46.8 |

The first 552 are the binaries of 2026-11-13, when the reference machine agreed with
`fjrun.py` on all of them, step counts included; `fjrun.py` still gives those outputs. An
image is one function and a loop over its blocks, as before. The instructions some input
runs and the one-bit changes caught were measured then: 76%, 74%, 69% and 96% of the
instructions, and 53 / 120, 74 / 200, 45 / 130 and 65 / 100 of the changes. The 60 images
with every 32-bit instruction have no reference machine of their own (below).

### What the tests found on the way

- On AArch64 (2026-11-16): a 32-bit logical operation with a constant kept the high half of
  the constant (arm64-semantics' decoder gives the pattern over 64 bits); six guests showed
  it on the first run.
- On x86-64: the parity flag, which the lift did not keep, is read by rustc's code for the
  parity of a byte (`setnp`), and a conditional jump to another function is a tail call;
  three guests gave up there on the first run. Neither was a wrong result.

- On images (2026-11-13): `jalr` with one register for the link and the target was not
  lifted, and one function for the whole program took Flapjack a quarter of an hour to
  compile.
- On guests: an indirect call reached a function whose address the tool had not found in
  the program (an `auipc` and its `addi` apart), so six guests gave up where they should
  have gone on. Indirect calls now search every function. None of the failures was a wrong
  result: each was the recompiled program saying it gave up.
- Flapjack's time grows with the square of a function's length and much faster with the
  depth of its loops (a function of 24 nested loops does not compile in five minutes). So
  lift 2 deals long runs of statements out to functions, and a function that would nest
  more than ten loops is a loop over its blocks.

## What this does not show

- **It is testing.** The row of one-bit changes in the first table is how sharp: flip the
  low bit of one value the decompiled program assigns or stores, and see whether the test
  fails. For a guest the change is marked, so it is known whether a run reached it: of 265
  changes to SP1 guests, one to a guest, 124 are reached by some input, and 102 of those 124
  are caught. None of the 141 unreached ones is, as it should be. The 22 reached and not
  caught were not traced one by one. On AArch64 and x86-64 about half of the reached changes
  are caught, not four in five: there the changes are also to flags and to the results
  computed for them, which are read less than a register is (`check.py mutants` writes
  each change and its outcome to `result.txt`). The 33 of AArch64 were read: saves and
  restores of callee-saved registers, differences computed only for a comparison, values
  written again before they are used. That is reading, not proof that none could be seen. A change can be reached and show nothing where the low bit of the
  value does not matter afterwards: a saved register its caller no longer reads, a constant
  on the way to another, a comparison that goes the same way. (The changes are to the statements of the program, not to the functions that
  write its memory image, which are a third of the assignments and whose words, most of
  them code, are seldom read: with those included, 52 of 171 reached changes were caught.)
  So a wrong translation of an instruction that the tests run and whose result they show is
  very likely caught; one in code they never reach is not. Half the instructions of the
  guests are never run: panic paths, formatting, the parts of the allocator and of the
  runtime that these programs do not use.
- **One compiler, two versions, one setting.** Every guest is from rustc at `opt-level = 3`:
  1.93 for SP1 6.10.0, 1.98 for the bare targets. Other compilers, other settings and hand-written assembly have other shapes; of
  those only what `rust/src/bin/k_asm_flow.rs` writes by hand is tested (a jump table in
  code, a call through `t0`, `jalr` with one register for target and link).
- **The 32-bit instructions on images have no machine of their own.** flapjack-flip's
  machine is on an older riscv-zkvm that decodes only `addiw` of them. On guests SP1's
  executor is their reference (`k_asm_w`, and whatever rustc emits); on the 60 images the
  reference is `fjrun.py`, on the interpreter that was compared with SP1's executor.
- **A bare guest's reference is an emulator of a processor, not a model in Lean.** Unicorn
  is not arm64-semantics and not Kraken: that the lifts agree with those two is not tested.
  An image of a bare guest runs with unaligned accesses allowed, which Pancake's semantics
  does not describe (`LIMITS.md`).
- **The system calls are five**: `HALT`, `WRITE`, `COMMIT`, `COMMIT_DEFERRED_PROOFS` and the
  two hints. A guest that uses a precompile (`SHA_EXTEND` and the like) is refused by the
  runner here, not by the decompiler, and is untested.
- **The machine that runs a recompiled guest is the runner's.** Its heap is the guest's
  whole address space, with Pancake's stack and code above it. No such machine is defined
  in Lean yet.
- **A jump table the tool does not find makes the program give up**, not go wrong: its
  targets are looked for as addresses in the data and, on AArch64 and x86-64, as offsets
  from an address formed just before the jump; a table of another shape would be missed.
  Every refusal in the output is numbered and described.
- **Memory of an image.** A Flapjack image gets half the heap and half the stack it had.
- **Time.** A run of an image is cut off at 2,000,000 steps and of a guest at 20,000,000
  (400,000,000 for the recompiled one).
- **Nothing recovers names, variables or types.** The output is correct on these tests and
  structured; it is not what the programmer wrote.
