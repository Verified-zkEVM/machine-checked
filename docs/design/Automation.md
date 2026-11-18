# Design note: proof automation at Lprog and Pancake

How to make proofs about decompiled programs cheap: tactics and proof engineering that work for
every instruction set, since Lprog's operations are shared. The main piece today is `lsym`, a
symbolic-execution tactic at Lprog.

**Status** (items refer to [the plan](#the-plan-by-leverage)):

| item | what | status |
| --- | --- | --- |
| 1 | `lsym`, symbolic execution at Lprog | done, in use (`Cases/Zip2005/Runtime/*Lsym.lean`, `Cases/Hardening/`) |
| 2 | straight-line blocks in one step | `SafeN.block` proved; `lsym` does not use it yet |
| 3 | reflection for whole-function properties | not started |
| 4 | fewer candidates at indirect calls | the simple half done (`jalrCands`) |
| 5 | aborts and left-out functions | not started |
| 6 | certificates instead of evaluation for `--to lean` | first step done (local lift, `kernel_eq`) |
| 7 | a weakest-precondition tactic for Pancake | not started; waits on Flapjack's semantics building here |

## Where proofs cost

- **Machine level** has real automation: `RiscV/Sym`'s symbolic executor (`sym_exec`) keeps
  values in normal forms, names large terms as atoms, tracks memory regions, applies function
  specifications at calls and splits at branches. riscv-zkvm adds separation-logic tactics.
- **Lprog** has one rule per instruction (`Lprog.SafeN.opn`, `.cond`, `.call`, …, and
  RISC-V's `lsafe_*` over the machine state). By hand, a proof is mostly applying these rules,
  writing out the register state after each block, the frame (every register not clobbered
  keeps its value) and the postcondition at each return. `memcmp` proved this way
  (`Cases/Zip2005/Runtime/MemcmpLprog.lean`) is 333 lines; `write_vectored`
  (`WriteVectored.lean`) is 906. `lsym` addresses this.
- **Pancake** has no automation, and no proof yet connects it to Lprog.
- **`decompile --to lean`** has the kernel re-evaluate the lift to check each term, which is
  slow on large functions ([`Tools/README.md`](../../Tools/README.md)).

## The plan, by leverage

1. **A symbolic executor at Lprog (`lsym`)**, after `sym_exec`'s design but simpler: labels
   instead of addresses, no decoding, one set of operations. It steps operations, splits at
   `Lcond`, applies function specifications at `Lcall`, and leaves loops to an invariant the
   user supplies. A shared vocabulary of memory regions at Lprog (#21) is still to come.
2. **Straight-line blocks in one step.** A block is the composition of its operations'
   `Op.eval`s (`SafeN.block`, over `runStraight`); the executor would step blocks rather than
   instructions, with `simp` normalising the register file (`updReg_apply`) and `bv_decide` for
   side conditions. A proof that `dropDead` preserves meaning would let proofs work on the
   smaller program (not yet proved).
3. **Reflection for whole-function properties.** A computable checker with a soundness theorem,
   run by `decide +kernel`: an abstract interpreter (constants, stack offsets, intervals)
   proving that no `Labort` is reachable, that each computed jump lands on a candidate, and that
   the program never goes `wrong` — the hypotheses of `equivalent_of_entry`.
4. **Fewer candidates at indirect calls**, by a verified value analysis. Every candidate
   multiplies case splits and kernel work. The simple half is done: a `jalr` whose previous
   instruction is an `auipc` of its register (`call`, `tail`) gets the one function at the
   address they compute (`jalrCands`); any list is sound (`callee_indirect`).
5. **Aborts and left-out functions.** Each `Labort` either becomes coverage (`LIMITS.md` says
   what is missing) or is proved unreachable (item 3). A function that does not decode can be
   treated as an external call whose contract is proved at the machine level with `sym_exec`.
6. **Certificates instead of evaluation** for `--to lean`: prove once that the lift is local
   (an instruction's lift depends on the instruction and a few lookups), have the tool write the
   lookups (labels, live flags), and let the kernel check each instruction alone.
7. **Pancake**: a weakest-precondition tactic over Flapjack's semantics, natural for structured
   control flow, once that semantics builds here (`pancake/README.md`) and lift 2 or Flapjack's
   compiler theorem makes proofs there pay off.

## zip-2005, counted

The `--proved` lift of zip-2005, counted from its Lprog text by `scripts/automation-stats.py`
(its docstring gives the commands). Figures in brackets are for the default lift.

| what | count | relevance |
| --- | --- | --- |
| size | 304 functions, 41,631 instructions; median function 40, largest 4,424 | the long tail is a few cryptographic kernels |
| straight-line code | 92% of instructions; 84% of that in blocks of 8 or more; longest block 3,988 (SHA-256, unrolled) | blocks are the largest lever (item 2); the longest also needs atoms, or the state grows without bound |
| calls | 1,573 calls and 67 tail calls, about 5 per function | specifications at calls (item 1) |
| computed calls and tail calls | all 1,640; 1,569 have one candidate, the rest all 304 functions (default lift: 1,657, of which 1,581 have one candidate) | item 4 |
| loops (backward branches) | 324, about 1 per function | an invariant per loop, by hand for now |
| aborts | 2 (default lift: 316; an earlier count, by hand, found 99 that control may reach, most after a call of a panic function, which does not return) | item 5 |
| functions left out | 3, the panic machinery | small |

## `lsym` today

`lsym` lives in [`lprog/Lprog/Tactic.lean`](../../lprog/Lprog/Tactic.lean) (its module docstring
is the reference). It works for any instruction set; each one adds its own lemmas to the simp
set `lsym_simp` (RISC-V's are in `lprog-riscv/LprogRiscV/Lsym.lean`).

```lean
lsym hf [stop [pc, …]] [with [lemmas]] [using [specs]]
```

The goal is `I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩`, and `hf : p[fn]? = some fd`.
The body of `fd` should be a literal (as `decompile --to lean` writes it, `f<i>`). On every
branch, `lsym`:

- steps over labels and follows `goto`s;
- computes each operation by `simp` (`lsym_simp` plus the `with` lemmas) and substitutes the
  result. A load's or store's memory check is closed if `simp` can; otherwise it becomes the
  hypothesis `hm` and the result is computed anyway (an operation whose check fails traps, and
  a trap is safe). On RISC-V the check is `isValidDwordAccessSp1 a`, and `noCodeAt m a 8`
  for a store: the form the region lemmas give. Loads read back through earlier stores;
- splits at a branch, with the condition as the hypothesis `hc`;
- at a return, leaves goals that the link register and stack pointer are as the call left them,
  plus the postcondition;
- at a call or tail call, with `using [specs]`, applies the first specification that fits —
  either a continuation-form spec or an `Isa.Contract` (below) — names what it returns (`r'`,
  `m'`, `hret`, …) and continues after the return, using `hret` on that path (unfolded by the
  `with` lemmas when the postcondition is a definition).

It stops at a call without a specification, at an external call, at a program counter listed in
`stop`, and at a loop head (a path that returns to a program counter it has already stepped
from is left there, so `stop` is usually unnecessary). Hypotheses that would shadow each other
are renamed apart: the latest is `hc`/`hm`/`hret`, earlier ones `hc_1`, `hm_2`, …, oldest
first. `set_option trace.lsym true` reports why each remaining goal was left: a stop, a loop
head, a step that does not apply (with the last rule's error), running out of depth, a return,
or a side condition. `lsym` raises `maxRecDepth` to 16384 while it runs; a step that still runs
out of depth leaves its goal. Running out of heartbeats stops `lsym` with an error naming the
program counter.

Related pieces:

| name | where | what |
| --- | --- | --- |
| `lstep` | `lprog/Lprog/Tactic.lean` | one step of `lsym` |
| `lframe` | `lprog/Lprog/Tactic.lean` | proves that the register file `lsym` leaves agrees with the original outside the written registers |
| `frame_ofParts` | `lprog-riscv/LprogRiscV/Lsym.lean` | turns that into a postcondition's frame over the RISC-V machine state |
| `Isa.Contract p c f Pre Post` | `lprog/Lprog/Contract.lean` | a function contract over the register file, for any instruction set; `lsym … using` steps calls through it (`SafeN.call_contract`, `SafeN.tail_contract`, in `Tactic.lean`), so proofs compose bottom-up |
| `contract_of_agree` | `lprog-riscv/LprogRiscV/Lsym.lean` | turns a RISC-V contract stated over machine states into an `Isa.Contract` without re-proving it |
| `lsym_addr` | simp set (`lprog/Lprog/Tactic.lean`) | address normal form: a base plus one constant (subtraction as addition of the negation, sums right-associated, constants folded, `ofNat (8 * (2 * j + 1))` as `ofNat (16 * j) + 8#64`, shifts as multiplications). Normalise a region lemma's fact with `simp only [lsym_addr] at h` to match `lsym`'s addresses |
| `SafeN.label_spend` | `lprog/Lprog/Sem.lean` | spends one unit of budget at a label, so a function that never returns can be proved safe by induction on the budget (`Cases/Hardening/Calls.lean`, `stop_contract`) |
| `SafeN.block` | `lprog/Lprog/Block.lean` | steps a straight-line piece at once (item 2; not yet used by `lsym`) |

**Recursion** needs nothing extra when it is on a smaller argument: prove the contract by
induction on the argument and step the recursive call through the induction hypothesis
(`Cases/Hardening/Rec.lean`, `fib`). Recursion that need not terminate would need the budget at
calls (`budget_induction`).

## Results

| proof | by hand | with `lsym` |
| --- | --- | --- |
| `memcmp` (`Cases/Zip2005/Runtime/MemcmpLprog.lean` vs `MemcmpLsym.lean`) | 333 lines, 28 rules applied by hand, raised `maxHeartbeats`; checks in 2.5 s | 140 lines, two calls of `lsym`, no raised limits; 1.9 s |
| `write_vectored`: three functions, a loop, a call, a tail call, a system call (`WriteVectored.lean` vs `WriteVectoredLsym.lean`) | 906 lines, 36 address lemmas, `maxHeartbeats` raised 6 times; 4.2 s | 300 lines, no address lemmas or raised limits, no address facts bridged by `bv_decide`; calls go through `Isa.Contract`s; 2.1 s |
| `Cases/Hardening/` (C compiled by clang) | | the functions the `--proved` lift takes, each against C's meaning, except `popcount`; four of `arith.c`'s twelve are left out for their 32-bit operations; see [its README](../../Cases/Hardening/README.md) |
| x86-64 (`Tools/Test/LsymX86.lean`) | | two functions lifted from bytes, a call through a contract with the return address pushed and popped; only the instruction set's `lsym_simp` instance was added |

What remains for the user in these proofs is what the function means: loop invariants, frames
(which cells the prologue writes, that other memory is unchanged), postconditions, and some
address arithmetic.

On the Hardening programs the lift itself held: every operation matched C at its edges (division
by zero and overflow, high halves of products) and every load's extension. On the 41 Rust
guests built for SP1, the `--proved` lift leaves out 177 of 6,738 functions: 142 for `unimp` (the
illegal instruction rustc emits for a trap) and 35 for the 32-bit operations riscv-zkvm's
machine lacks. A guest's `__udivti3` composes with its callee's contract through a result
returned in memory.

**Cost on straight-line code** (a body of `addi`s and a return):

| instructions | 100 | 200 | 400 |
| --- | --- | --- | --- |
| time | 7 s | 18 s | 63 s |

At the default `maxHeartbeats` (200,000), 100 instructions check and 200 do not (they need about
a million). Time grows with the square of the length; `SafeN.block` (item 2) is meant to fix
this.

**`--to lean`** (item 6, first step). Each instruction's lift depends only on it, its
predecessor, its index and `entryOf` (`liftFrom`), not on decoding the function again. And
`--proved` checks a function's parts by `kernel_eq` (`Eq.refl`, evaluated by the kernel)
instead of `decide +kernel`: on zip-2005's three largest functions the check is about 2.5 times
faster and the module 30 to 35% faster (16 s to 11 s for the largest); elaborating the term is
now about two thirds of the time. The whole-program route keeps `decide`, since there the
kernel's unfolding of `program.lift` to compare it with a term is slower than evaluating the
decision.

## Known limitations and open problems

- **Long straight-line code is slow** (above): `Cases/Hardening`'s 290-instruction `mix` takes
  45 s with `maxHeartbeats` raised tenfold.
- **`bv_omega` after `lsym`** is slow or fails where the same fact alone is instant: it takes
  every hypothesis, and `lsym` leaves many. Workaround: state the arithmetic as separate lemmas
  (`Rec.lean` does).
- **`simp` on `toNat` of a sum with a large literal** (an address below `sp`) produces a proof
  the kernel times out on (a Lean issue). Use `bv_omega` for such facts.
- **Literal spelling.** A hypothesis given to `lsym` that writes a literal as `0` does not close
  a side condition `simp` has written as `0#128`. Workaround: write `0#128` in the contract
  (`Cases/Hardening/Guest.lean`).
- **External calls have no contract form.** System calls still go through machine-level rules
  applied by hand (`lsafe_write`).
- **No machine-backed instance for x86-64 or AArch64.** RISC-V's Lprog instance is `rvIsa` over
  SP1, with a transfer theorem to the machine; the x86-64 test runs over a model of memory
  (doublewords by address). Proofs about AArch64 or x86-64 binaries need such an instance and a
  theorem like RISC-V's `transfer`.
- **`unimp` and 32-bit operations** leave functions out of the `--proved` lift. Taking `unimp`
  as a trap would be the larger gain.
- **Memory regions** have no shared vocabulary at Lprog yet (#21).

## Next steps

1. A contract form for external calls.
2. `SafeN.block` in `lsym` for long blocks, with atoms.
3. Machine-backed Lprog instances for x86-64 and AArch64.
4. The rest of item 6: a shorter written term for `--to lean` (elaborating it now costs more
   than checking it), and per-instruction checks.
