# decompile-check

**The check of `decompile --to pancake`, by running.** Nothing is proved yet of the path from
a binary to Pancake ([`Tools/README.md`](../../Tools/README.md)), so this is what stands
behind it for now: decompile a binary, compile the Pancake text with Flapjack, run both
binaries on the same inputs, and compare what they do.

There are two kinds of binary, each with its own notion of what a run does and its own
machine to say so.

- **A Flapjack image.** What it does is flapjack-flip's notion: the FFI calls in order, each
  with its name, its configuration bytes and its array before and after, and how the run
  ends. The reference is flapjack-flip's machine (riscv-zkvm's `step` and the image
  conventions).
- **An SP1 guest**, an ELF that rustc built. What it does is its system calls in order, each
  with its number, its arguments and the bytes it reads from memory or writes to it, and
  the exit code. The reference is SP1's own executor.

Two binaries agree on a test when these are identical on each of five inputs.

Neither the compiler nor the judge is this repository's. Flapjack compiles. The runs are on
the interpreters here, which are fast, and each is compared with its reference machine on
every test: with flapjack-flip's machine output for output and step for step, and with
SP1's executor on the public values, the exit code and the number of instructions.

## The pieces

| file | what |
| --- | --- |
| `check.py` | The driver: `build`, `rust`, `reference`, `sp1-reference`, `self-test`, `run`, `mutants`. `check.py --help` says what each does. |
| `rv64.py` | A plain RV64IM interpreter, shared by the two runners. |
| `fjrun.py` | Runs a Flapjack image on the test inputs and prints what it does, as `flip-check run` prints it. riscv-zkvm holds memory as a function, so a long run takes minutes there and under a second here. |
| `sp1run.py` | Runs an SP1 guest, or the image that a decompiled guest is recompiled to, in one world: SP1's system calls as riscv-zkvm models them. |
| `sp1ref/` | `sp1ref GUEST.elf ...`: SP1's executor (`sp1-sdk`) on the same inputs. A Rust project of its own. |
| `fjc/` | `fjc SOURCE.pnk`: Flapjack's `RiscV.NativeSource.compile` as a command. A Lean project of its own, on Flapjack's toolchain; `lake build` in it (after `lake exe cache get`) takes a while the first time. |
| `rust/` | The guests written by hand, 39 of them, each for one thing: sorting, hashing, trait objects, function pointers, jump tables, 128-bit and floating-point arithmetic, formatting, collections, recursion and tail calls, panics, and inline assembly for every instruction of RV64IM with edge-case operands and for control flow rustc does not emit. `src/lib.rs` is what they share. |
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

# SP1 guests: the 39 by hand and 240 generated (needs SP1's toolchain, `cargo prove`)
python3 $C/check.py rust work guests --seed 1 --count 240
python3 $C/check.py build $FJC guests
python3 $C/check.py run $FJC guests
(cd $C/sp1ref && cargo build --release)
python3 $C/check.py sp1-reference $C/sp1ref/target/release/sp1ref guests

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

On 2026-11-15, with Flapjack at the revision flapjack-flip pins (`95aa081`) as the compiler.

### SP1 guests

Built with SP1 6.10.0 (`cargo prove build`, rustc 1.93, `opt-level = 3`).

| tests | from | pass | steps, recompiled over original | instructions some input runs | one-bit changes caught |
| --- | --- | --- | --- | --- | --- |
| `rust/` | 39 by hand | 39 / 39 | | | |
| `gen_rust.py` | seed 1: 240, of which 226 halt on every input | 226 / 226 | | | |
| together | | **265 / 265** | 7.1 | 48% | 102 / 265; of the 124 reached, 102 |

- **SP1's executor agrees with `sp1run.py` on all 265**: the public values, the exit code and
  the number of instructions, on each of the five inputs.
- 215 of the 1,325 runs end in a panic (exit code 1, after the message on file 2).
- **Every instruction of RV64IM is run**: all 63, the 14 on 32 bits among them.
- **Structure**: of the 45,358 functions of the 265 guests (most of them the same runtime
  again and again), 42,634 are structured and 2,724 (6%) are a loop over their blocks.
- A decompiled guest is 28,000 to 65,000 lines of Pancake. Flapjack compiled the ones
  timed, of up to 45,000 lines, in 5 to 10 seconds.

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

- **It is testing.** The last column of the first table is how sharp: flip the low bit of
  one value the decompiled program assigns or stores, and see whether the test fails.
  For a guest the change is marked, so it is known whether a run reached it: of 265
  changes, one to a guest, 124 are reached by some input, and 102 of those 124 are caught.
  None of the 141 unreached ones is, as it should be. The 22 reached and not caught were not
  traced one by one. A change can be reached and show nothing where the low bit of the
  value does not matter afterwards: a saved register its caller no longer reads, a constant
  on the way to another, a comparison that goes the same way. (The changes are to the statements of the program, not to the functions that
  write its memory image, which are a third of the assignments and whose words, most of
  them code, are seldom read: with those included, 52 of 171 reached changes were caught.)
  So a wrong translation of an instruction that the tests run and whose result they show is
  very likely caught; one in code they never reach is not. Half the instructions of the
  guests are never run: panic paths, formatting, the parts of the allocator and of the
  runtime that these programs do not use.
- **One compiler, one setting.** Every guest is from rustc 1.93 at `opt-level = 3` for SP1
  6.10.0. Other compilers, other settings and hand-written assembly have other shapes; of
  those only what `rust/src/bin/k_asm_flow.rs` writes by hand is tested (a jump table in
  code, a call through `t0`, `jalr` with one register for target and link).
- **The 32-bit instructions on images have no machine of their own.** flapjack-flip's
  machine is on an older riscv-zkvm that decodes only `addiw` of them. On guests SP1's
  executor is their reference (`k_asm_w`, and whatever rustc emits); on the 60 images the
  reference is `fjrun.py`, on the interpreter that was compared with SP1's executor.
- **The system calls are five**: `HALT`, `WRITE`, `COMMIT`, `COMMIT_DEFERRED_PROOFS` and the
  two hints. A guest that uses a precompile (`SHA_EXTEND` and the like) is refused by the
  runner here, not by the decompiler, and is untested.
- **The machine that runs a recompiled guest is the runner's.** Its heap is the guest's
  whole address space, with Pancake's stack and code above it. No such machine is defined
  in Lean yet.
- **A jump table the tool does not find makes the program give up**, not go wrong: its
  targets are looked for as addresses in the data, and a table of offsets would be missed.
  rustc's are addresses. Every refusal in the output is numbered and described.
- **Memory of an image.** A Flapjack image gets half the heap and half the stack it had.
- **Time.** A run of an image is cut off at 2,000,000 steps and of a guest at 20,000,000
  (400,000,000 for the recompiled one).
- **Nothing recovers names, variables or types.** The output is correct on these tests and
  structured; it is not what the programmer wrote.
