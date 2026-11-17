# Design note: proof automation at Lprog and Pancake

**Status: proposed (2026-11-17); the first spike (items 1 and 2) done, below.** How to make proofs
about decompiled programs cheap: tactics and proof engineering that apply to every instruction
set, since Lprog's operations are shared.

## Where proofs cost today

- **Machine level** has real automation: `RiscV/Sym`'s symbolic executor (`sym_exec`), which
  keeps values in normal forms, names large terms as atoms, tracks memory regions, applies
  function specifications at calls and splits at branches; riscv-zkvm adds separation-logic
  tactics.
- **Lprog** has a rule per instruction (`Lprog.Isa.SafeN.opn`, `.cond`, `.call`, …, and
  RISC-V's `lsafe_*` over the machine state) and nothing that applies them. `memcmp` at Lprog
  (`Cases/Zip2005/Runtime/MemcmpLprog.lean`) is 333 lines, `write_vectored` 904: most of it
  a rule per instruction, register states written out by hand after each block, the frame
  (every register but the clobbered keeps its value), and the postcondition at each return.
- **Pancake** has nothing, and no proof yet connects it to Lprog.
- **`decompile --to lean`** has the kernel evaluate the lift again to check a term, which is
  slow on large functions (`Tools/README.md`).

## The plan, by leverage

1. **A symbolic executor at Lprog (`lsym`)**, after `sym_exec`'s design, simpler at Lprog:
   labels for addresses, no decoding, one set of operations. Steps operations, splits at
   `Lcond`, applies function specifications at `Lcall`, leaves loops to an invariant the user
   gives. Memory needs a shared vocabulary of regions at Lprog first (#21).
2. **Straight-line blocks in one step.** A block of operations is the composition of their
   `Op.eval`s (`SafeN.block`, over `runStraight`); the executor steps blocks, not
   instructions, with `simp` normalising the register file (`updReg_apply`) and `bv_decide`
   for side conditions. A proof that `dropDead` keeps the meaning would let proofs work on the
   smaller program.
3. **Reflection for whole-function properties.** A computable checker with a soundness
   theorem, run by `decide +kernel`: an abstract interpreter (constants, stack offsets,
   intervals) proving that no `Labort` is reachable, that each computed jump lands on a
   candidate, that the program never goes `wrong`: the hypotheses of `equivalent_of_entry`.
4. **Fewer candidates at indirect calls**, by a verified value analysis: today each lists
   every function (218 lists of 304 in one zip-2005 function), which multiplies case splits
   and the kernel's work.
5. **Aborts and functions left out.** Each `Labort` either becomes coverage (`LIMITS.md` says
   what is missing) or is proved unreachable (item 3). A function that does not decode can be
   an external call whose contract is proved at the machine level with `sym_exec`: proved,
   not assumed.
6. **Certificates instead of evaluation** for `--to lean`: prove once that the lift is local
   (an instruction's lift depends on the instruction and a few lookups), have the tool write
   the lookups (labels, live flags), and the kernel checks each instruction alone.
7. **Pancake**: a weakest-precondition tactic over Flapjack's semantics, natural for its
   structured control flow, once that semantics builds here (`pancake/README.md`) and lift 2 or
   Flapjack's compiler theorem makes proofs there pay.

## zip-2005, counted

The `--proved` lift of zip-2005 (304 functions, 41,631 instructions), counted from its Lprog
text (the default lift in brackets where it differs):

| what | count | for the plan |
| --- | --- | --- |
| straight-line code | 92% of the instructions; 83% of that in blocks of 8 or more; the longest block 3,988 (SHA-256, unrolled) | blocks are the largest lever (item 2); the longest needs atoms too, or the state grows without bound |
| calls | 1,573, about 5 to a function | specifications at calls from the start (item 1) |
| candidates of a computed call | all 304 functions, at each of 1,640 (the default lift gives 1,581 of them one candidate, and 76 are indirect) | item 4 is large and simple: the `--proved` lift can take the default lift's resolution |
| loops (backward branches) | 324, about 1 to a function | an invariant to a loop, given by hand for now |
| aborts | 2 (the default lift: 99 that control may reach, most after a call of a panic, which does not return) | mostly a specification that a function does not return (item 5) |
| functions left out | 3, the panic machinery | small |
| size of a function | median 40, the largest 4,424 | the long tail is a few cryptographic kernels |

## First spike: done

- **`Lprog/Block.lean`**: `Isa.runStraight` runs the operations of a straight-line piece;
  `SafeN.block` steps over the piece at once. For every instruction set.
- **`Lprog/Tactic.lean`**: `lsym hf [stop [pc, …]] [with [lemmas]]` steps a body on every
  branch: labels; operations, computed and substituted, a load's or store's check left to
  `simp_all`; gotos; branches, split, with the condition as `hc`; returns, their conditions
  closed. It stops at the given program counters (a loop's head), and at calls and external
  calls. The simp set `lsym_simp` holds Lprog's evaluation, and an instruction set adds its
  own (`LprogRiscV/Lsym.lean`).
- **`memcmp`** with it (`Cases/Zip2005/Runtime/MemcmpLsym.lean`), against stepping each
  instruction by hand (`MemcmpLprog.lean`), the same contract:

  | | by hand | with `lsym` |
  | --- | --- | --- |
  | the loop and the contract | 206 lines | 126 lines |
  | rules written by hand | 28 | none (two calls of `lsym`) |
  | a raised `maxHeartbeats` | yes | no |
  | time to check | 2.5 s | 6.6 s |

  What is left is what the function means: the invariant at the back edge, and the
  postcondition at each return, the frame (every register not clobbered keeps its value)
  written out three times.

Next, in order: a postcondition helper for the frame, memory and code; calls through a
specification in `lsym` (and `SafeN.block` used for long blocks, with atoms); then item 4,
which the count shows is the cheapest large win; then `write_vectored` (904 lines by hand) as
the first real port.
