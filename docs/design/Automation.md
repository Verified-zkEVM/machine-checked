# Design note: proof automation at Lprog and Pancake

**Status: proposed (2026-11-17); the first spike (items 1 and 2) a second round (calls, item 4, a real port) and a third (proofs that compose, on two instruction sets) done, below.** How to make proofs
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

## Second round: done

- **The frame, once.** `lframe` proves that a register file `lsym` leaves agrees with the one
  it started from outside the registers written; `frame_ofParts` (`LprogRiscV/Lsym.lean`)
  turns that into a postcondition's frame over the machine state.
- **Calls through specifications.** `lsym … using [spec, …]` applies a callee's specification
  at a call or a tail call, names what it gives back (`r'`, `m'`, `hret`, …) and steps on
  after the return (`Tools/Test/Lsym.lean`).
- **Memory.** A load or a store is computed even when its check is not closed: the check is a
  hypothesis (`hm`) of what follows and a goal of its own, in the form the region lemmas give
  it (`isValidDwordAccessSp1 a`, and `noCodeAt m a 8` for a store), and a load reads back
  through the stores before it. Program counters are kept literals, so bodies of a few hundred
  entries step.
- **Item 4, the simple half.** The `--proved` lift gives a `jalr` whose previous instruction is
  an `auipc` of its register (`call`, `tail`) the one function at the address they compute
  (`jalrCands`), and every function otherwise. Any list is sound (`callee_indirect`): a target
  outside it is `wrong`, which a proof of safety excludes. On zip-2005, 1,570 of the 1,640
  computed calls now have one candidate instead of 304; 70 keep all.
- **`write_vectored`** with it (`Cases/Zip2005/Runtime/WriteVectoredLsym.lean`): three
  functions, a loop, a call, a tail call, a system call, stores and loads of a frame, the same
  contracts as `WriteVectored.lean`:

  | | by hand | with `lsym` |
  | --- | --- | --- |
  | the seven theorems | 480 lines | 270 lines |
  | address lemmas | 64 lines (36 lemmas) | none |
  | a raised `maxHeartbeats` | 6 | none |
  | time to check | 4.2 s | 4.2 s |

  What is left: the loop's invariant, the frame (which cells the prologue writes, that other
  memory is unchanged), the postconditions, and the facts about addresses as `simp` writes
  them (`sp + 0xffffffffffffffd0#64 + 40#64`), proved by `bv_decide`. Calls and the system
  call still go through the machine-level rules (`lsafe_call`, `lsafe_tail`, `lsafe_write`),
  whose contracts are stated over a machine state; `using` wants contracts over the register
  file.

- **Item 6, first step.** The lift of an instruction is now local: `liftFrom` hands each
  instruction the one before it, so its lift depends on the instruction, its predecessor, its
  index and `entryOf`, not on decoding the function again (finding the predecessor through
  the program had made `--to lean` quadratic in a function's size). And `--to lean --proved`
  checks a function's parts by `kernel_eq` (`Eq.refl`, evaluated by the kernel) instead of
  `decide +kernel`, which compares every field through `DecidableEq`: on zip-2005's three
  largest functions the check is about 2.5 times faster and the module 30 to 35% faster
  (16 s to 11 s for the largest). What is left is elaborating the term itself, about two
  thirds of the time now. The other routes keep `decide`: there the kernel's unfolding of
  `program.lift` to compare it with a term is far slower than evaluating the decision.

## Third round: proofs that compose, on two instruction sets

- **Contracts over the register file** (`Lprog/Contract.lean`). `Isa.Contract p c f Pre Post`:
  the function at index `f`, from its entry with return address `ret` and stack pointer `top`
  and `Pre ret top regs m`, is safe if every state it returns to with
  `Post ret top regs m r' m'` is. It is stated for any instruction set. `lsym … using [contract]`
  steps a call or a tail call through it (`SafeN.call_contract`, `SafeN.tail_contract`): the
  callee is the contract's, shown by `simp` and `decide` (indirect targets too); the
  precondition and the stack pointer are closed by `simp` if they can be; and the continuation
  is taken up after the return, the postcondition as `hret`. A caller's proof uses its callees'
  contracts and gives its own, so proofs build bottom-up as the program does.
- **Contracts proved over a machine state, kept.** `contract_of_agree`
  (`LprogRiscV/Lsym.lean`) turns a RISC-V contract stated over any machine state the register
  file agrees with into an `Isa.Contract`, by `Agree.refl`, without proving it again.
- **One normal form for addresses** (`lsym_addr`, also in `lsym_simp`): a base plus one
  constant. A subtraction becomes the addition of its negation, sums associate to the right,
  constants fold, and an index `BitVec.ofNat 64 (8 * (2 * j + 1))` becomes
  `BitVec.ofNat 64 (16 * j) + 8#64`. A region lemma's fact about a cell, normalised by
  `simp only [lsym_addr] at h`, is about the address `lsym` computes, so a proof no longer
  bridges two spellings of an address.
- **`write_vectored` again** (`WriteVectoredLsym.lean`). `syscall_write`'s `lsym` proof goes
  through `contract_of_agree`; `sys_write` is proved by `lsym` with its tail call through it;
  and `write_vectored`'s call goes through `sys_write`'s contract:

  | | second round | third round |
  | --- | --- | --- |
  | lines (the same theorems and their helpers) | 270 | 243 |
  | `bv_decide` bridging addresses | 22 | 0 |
  | call rules applied by hand (`lsafe_call`, `lsafe_tail`) | 2 | 0 |
  | time to check | 4.2 s | 3.8 s |

  The system call is still a rule applied by hand (`lsafe_write`): an external call has no
  contract form yet.
- **x86-64** (`Tools/Test/LsymX86.lean`). Two functions are lifted from their bytes by the
  x86-64 lift, and the kernel checks the terms against it. `g` has a contract, and `f`'s,
  proved through `g`'s, steps the call with its push and pop of the return address. The
  instruction set added only its instance to `lsym_simp`. Nothing in `lsym` was RISC-V's; the
  shared set lacked `Width.bits`, which a zero-extension needs and RISC-V's code never had.
  What x86-64 lacks is an instance at Lprog backed by its machine (RISC-V's is `rvIsa` over
  SP1, with the transfer theorem), so the test runs over a model of its memory (doublewords by
  address). A machine-backed instance for x86-64 or AArch64, with a theorem like RISC-V's
  `transfer`, is what would make such proofs about the binary.

Next: a contract form for external calls (the system call above); `SafeN.block` for long
blocks, with atoms; machine-backed instances for x86-64 and AArch64; and the rest of item 6, a
shorter written term for `--to lean` (elaborating it now costs more than checking it), and
per-instruction checks.
