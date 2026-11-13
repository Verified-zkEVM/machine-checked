# decompile-check

**The check of `decompile --to pancake`, by running.** Nothing is proved yet of the path from
a Flapjack image to Pancake ([`Tools/README.md`](../../Tools/README.md)), so this is what
stands behind it for now: decompile a binary, compile the Pancake text with Flapjack, run
both binaries on the same inputs, and compare what they do.

"What they do" is flapjack-flip's notion: the FFI calls in order, each with its name, its
configuration bytes and its array before and after, and how the run ends. Two binaries agree
on a test when these are identical on each of five input streams.

Neither the compiler nor the judge is this repository's. Flapjack compiles; the run is
flapjack-flip's machine (riscv-zkvm's `step` and the image conventions). A wrong
decompilation cannot pass by anything written here.

## The pieces

| file | what |
| --- | --- |
| `check.py` | The driver: `build`, `reference`, `self-test`, `run`, `mutants`. `check.py --help` says what each does. |
| `fjrun.py` | Runs an image on the test inputs and prints what it does, as `flip-check run` prints it. A plain RV64IM interpreter: riscv-zkvm holds memory as a function, so a long run takes minutes there and under a second here. It is used only where the reference machine has been shown to agree with it (`reference`, `self-test`). |
| `fjc/` | `fjc SOURCE.pnk`: Flapjack's `RiscV.NativeSource.compile` as a command. A Lean project of its own, on Flapjack's toolchain; `lake build` in it (after `lake exe cache get`) takes a while the first time. |
| `gen_asm.py` | Test images of hand-assembled code: every instruction the lift covers, with edge-case operands, and the control flow of a compiler that follows the calling convention. Not from Flapjack. |
| `gen_pancake.py` | Random Pancake programs that use the whole language: globals, pairs, exceptions, recursion, tail calls, `break` and `continue`, every memory width, memory far from its start, several FFI names. |
| `hand/` | Programs written by hand for one thing each. |

## Running it

```sh
lake build decompile
(cd scripts/decompile-check/fjc && lake exe cache get && lake build)
FJC=scripts/decompile-check/fjc/.lake/build/bin/fjc
C=scripts/decompile-check

# this repository's tests: 100 assembled, 130 generated, 2 by hand
python3 $C/gen_asm.py 1 100 corpus
python3 $C/gen_pancake.py 1 130 corpus
cp -R $C/hand/* corpus/
python3 $C/check.py build $FJC corpus
python3 $C/check.py run $FJC corpus

# flapjack-flip's 120 tests, and 200 more from its generator
python3 $C/check.py run $FJC ../flapjack-flip/tests
```

With flapjack-flip built, `check.py reference .../flip-check DIR` confirms on its machine
every `expected.txt` that `build` wrote.

## Results

On 2026-11-13, with Flapjack at the revision flapjack-flip pins (`95aa081`):

| tests | from | pass | steps, recompiled over original | instructions some input runs | one-bit changes caught |
| --- | --- | --- | --- | --- | --- |
| flapjack-flip `tests/` | 20 by hand, 100 from its generator, seed 0 | 120 / 120 | 11.9 | 76% | 53 / 120 |
| flapjack-flip's generator | seeds 1 and 2 | 200 / 200 | 12.5 | 74% | 74 / 200 |
| `gen_pancake.py` | seed 1 | 130 / 130 | 11.2 | 69% | 45 / 130 |
| `gen_asm.py` | seed 1 | 100 / 100 | 43.2 | 96% | 65 / 100 |
| `hand/` | | 2 / 2 | | | |

552 binaries. The reference machine agrees with `fjrun.py` on all of them, step counts
included.

What the tests found on the way: `ld32` at an address that names a local is rejected by
Flapjack at this revision (32-bit loads now go by bytes); `jalr` with one register for the
link and the target was not lifted; and one function for the whole program took Flapjack a
quarter of an hour to compile (the blocks are now dealt out to small functions).

## What this does not show

- **It is testing.** The last column is how sharp: flip the low bit of one value the
  decompiled program assigns or stores, and see whether the test fails. Between a third and
  two thirds do. The rest change code no input reaches (a quarter of a Flapjack image, its
  runtime's unused paths) or a value nothing reads afterwards. So a wrong translation of
  an instruction that the tests run and whose result they show is very likely caught; one in
  code they never reach is not.
- **Four instructions are not tested**: `slliw`, `srliw`, `srlw` and `subw`. The lift covers
  them, but the reference machine is flapjack-flip's, on an older riscv-zkvm that does not
  decode them. Flapjack does not emit them.
- **Memory.** The image gets half the heap and half the stack it had, so a program that
  uses more than 2 MiB of either is outside what was tested, and will not behave the same.
- **Time.** A run is cut off at 2,000,000 steps and the recompiled binary takes twelve
  times the steps (more where it divides), so only programs of up to about 150,000 steps
  are compared to the end.
- **One compiler revision.** The Pancake text is compiled with the Flapjack that
  flapjack-flip pins.
