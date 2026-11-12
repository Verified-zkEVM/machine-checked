# Design note: Lprog as a program-level verification layer

**Status: agreed (2026-11-11), after two reviews by the catcrypt-compiler maintainers
(PR #16).** It sets out the design of milestones A–D in [`ROADMAP.md`](../../ROADMAP.md)
steps 1–3 (issues #2–#5). Its generic parts (§1–§5, §8, §10) are to be shared with
catcrypt-compiler ([`docs/notes/SHARED-LIBRARY.md`](../notes/SHARED-LIBRARY.md)); the review
changed calls (§2), external calls (§4), the judgement (§5) and registers (§8), and added
leakage (§10). Milestone A is implemented (#17) without the review's changes, which follow as
#18 (events) and #19 (the call field); [As built](#as-built-milestone-a) at the end records
where the code departs from the text.

## Goal

Today Lprog (`MachineChecked/Lprog`) is a shared target for a lift and nothing more: a step
function over a single body, with shared control flow and shared operations. It has no
programs, no calls, no external calls, no judgement, no contracts and no proof automation, and
every proof that uses it drops to the machine at a call.

This note makes Lprog the layer where proofs happen. A whole program lifts to it; functions
call each other; system calls are external calls with specifications; contracts are stated
and composed there; a symbolic executor proves them. Then zip-2005 is re-proved through it,
and the machine-level proof tools (`RiscV/Sym`, `Exec`, `Frame`, and possibly `Check`) are
retired, so that there is one route from a binary to its specification.

Decided with the maintainer: calls are primitive (with the lift proved correct), frames are
owned regions of flat memory, and registers are behind an interface whose type is a parameter
of the instruction set.

## 1. Programs and state

A program is a list of functions. A function has a name, a body (as today), and a stack bound:

```lean
structure Lfundef (Op Reg : Type) where
  name  : String
  body  : Lcmd Op Reg
  depth : Nat              -- the most stack it uses below its entry sp, callees excluded;
                           -- an untrusted annotation (see Decisions)
```

A state is a stack of activations, the register file and the rest of the machine:

```lean
structure Frame where
  fn  : Nat                -- index of the function in the program
  pc  : Nat                -- index into its body
  ret : BitVec 64          -- the return value the call recorded (§2)
  top : BitVec 64          -- sp after the call's effect: the frame window is [top - depth, top)

structure State (I : Isa) where
  stack : List Frame       -- innermost first; empty when the program has returned
  regs  : I.Regs           -- global, as on the machine
  m     : I.M
```

The register file is global, as on the machine: the calling convention (which registers a
callee preserves) is a property of contracts, not of the semantics. This keeps the lift a
simulation of the machine instead of an abstraction of it, and leaves real abstraction
(registers to variables, frames to locals) to layer 1.

## 2. Primitive calls, and return-address integrity

Where the return address goes is the instruction set's business, not Lprog's: RISC-V and
AArch64 write a link register, x86 pushes it on the stack. So the effect of a call and the
check of a return are a field of `Isa` (§8), and Lprog's rules are stated through it.

- `Lcall f` pushes a frame for `f` at its first instruction. It applies the instruction set's
  call effect, which yields the return value (for RISC-V, the machine return address `pc + 4`,
  written to the link register; for x86, the same address pushed below `sp`). The frame
  records it as `ret`, and `sp` after the effect as `top`. Code that saves and restores the
  return address (as compiled code does) therefore runs unchanged.
- `Lret` pops the frame and continues after the call in the caller. It is defined only if the
  instruction set's return check holds of the frame: for RISC-V, the link register holds `ret`
  and `sp` is back at `top`; for x86, the doubleword at `sp` is `ret`, `sp` is back at `top`,
  and the return pops it. Otherwise it goes `wrong` (§3).
- An indirect call `Lcall [f₁, …, fₖ] r` calls the candidate whose entry the register `r`
  holds, and goes `wrong` if it holds none of them; a control-flow premise in the contract
  (as `Env.Cfi` today) says which candidates a site has.
- A tail call (`jal x0, f`, or `jalr x0` to a candidate entry) lifts to `Ltail f`, which
  replaces the current frame by one for `f` with the same `ret` and `top`, and leaves the
  return address alone. It is defined only if `sp` is back at `top` (the caller has released its
  frame). The callee's `Lret` then returns straight to the caller's caller, as on the machine.

Because `Lret` goes `wrong` on a bad return address, and the judgement (§5) excludes `wrong`,
return-address integrity is proved at Lprog as part of every function's proof. It is what
lets the machine's `jalr x0, 0(ra)` simulate the pop. `RiscV/Frame`, which proves exactly this
property at the machine today, is no longer needed.

## 3. Outcomes: `trap` and `wrong`

A step is a relation, because an external call has many possible results. Each step ends in
one of:

- a **state**;
- **`trap`**: the machine would be stuck too (a memory access SP1 refuses, no code at the pc).
  A trap is *safe*, as in `SafeN` today: a run that stops proves nothing false;
- **`wrong`**: an assumption the lift relies on is violated (a bad return address, an indirect
  target off its list, a frame not restored). `wrong` is *unsafe*: the judgement requires it
  to be unreachable.

The distinction is what makes the transfer to the machine sound: every Lprog outcome other
than `wrong` is matched by the machine (§7). catcrypt-compiler's steps return `Option`, which
conflates the two; the review agreed on separating them.

Each step also yields a list of **events** of a type `E`, the leakage an observer sees (§10):

```lean
step : σ → Outcome (σ × List E) → Prop
```

## 4. External calls

`Lext name` steps by a specification the execution context supplies, a relation between the
state before and the states after (or `trap`). The context is a record:

```lean
structure Context (I : Isa) where
  ext    : String → I.Regs → I.M → Outcome (I.Regs × I.M × List I.E) → Prop
  accept : I.Regs → I.M → Prop     -- for SP1: HALT with exit code 0
```

A specification returns the events of the call as well as its result, so a constant-time
proof can go through an external call.

For SP1, the specifications are restated once from the facts the layer-0 tools prove today
(`Sym/Syscall.lean`, `Check/Ecall.lean`, `Exec/Hint.lean`): `HALT`, `WRITE`, `COMMIT`,
`COMMIT_DEFERRED_PROOFS`, `HINT_LEN`, `HINT_READ` and the accelerators. The lift turns `ecall`
into `Lext` on the id in `t0`. The context is not otherwise parameterised in this pass.

## 5. One judgement, generic

`SafeN` moves to `MachineChecked/Ascent/Safe.lean`, stated for any machine given by a step
relation with outcomes and events, and an accept predicate. It ignores the events:

```lean
def SafeN (step : σ → Outcome (σ × List E) → Prop) (accept : σ → Prop)
    (G : σ → Prop) (n : Nat) (P : Prop) (s : σ) : Prop :=
  -- every run of fewer than n steps from s, along which G holds,
  -- never reaches `wrong`, and ends accepting only if P
```

- RISC-V's `SafeN` becomes the instance at `stepSp1` (deterministic, never `wrong`, with
  `E = Unit`) and `Accepted`, keeping its name and every lemma's name, so nothing that uses it
  changes.
- Lprog's judgement is the instance at `Isa.step` and the context's `accept`.
- The rules (`step`, `of_step`, `steps`, `assume`, `loop`, `loop_measure`, `cases`) are proved
  once, generically.
- **Contracts** are in continuation form with the budget, as today:
  `∀ G n P s, Pre s → (∀ t, Post s t → SafeN … G n P t) → SafeN … G n P s`.
- **Correspondence.** The shared package starts from catcrypt-compiler's `RefinesP` and
  `RefinesO` (`HaxAscent/Ascent/Refines.lean`), forward simulation of an abstract function
  under a precondition. MachineChecked's `Corres` over `Reaches` (one step, iterated) and
  catcrypt-compiler's `CorresIsaRun` (a whole run, ending halted) are instances. `RefinesP`
  takes a partial function `C → Option D`, and Lprog's step is a relation, so the package has
  a relational `RefinesR (step : C → D → Prop)`, with a progress clause as well as the related
  end; `RefinesP` is its instance at `fun c d => sem c = some d`.
- **Correspondence as a contract.** On a relational machine (Lprog with external calls) the
  useful statement is the continuation form,
  `SR m a → P a → (∀ t, SR t (fa a) → SafeN … G n Q t) → SafeN … G n Q m`: every run, not
  some run, must reach a related state or stop safely. Total correctness over `Reaches` implies
  it on a deterministic machine, by `SafeN.of_reaches`, so the CatCrypt kernels' statements
  give contracts directly (`SafeN.of_corres`).
- **`SContract`** (catcrypt-compiler's `SepLogic/Contract.lean`) sits beside `SafeN` in the
  shared package: total (a run exists), framed (a write set), with a two-run `ct` field, and
  generic in state, locations and trace. `SafeN`'s contracts are partial, because a whole
  program may trap or panic; `SContract` suits kernels, which always halt. The package has a
  bridge from `SContract` to a `SafeN` contract on deterministic machines, so that a kernel's
  `SContract` serves as a contract at an `Lcall` (the route of `SafeN.of_corres`); the `ct`
  field has no counterpart, since `SafeN` ignores events. Composing `ct` across `Lcall` needs
  its own rule: open.
- **Composition** is a generic `table_sound`, by strong induction on the budget over a family
  of contracts (the shape of `Check/Sound/Act.lean`'s `table_sound`). At an `Lcall`, the
  callee's contract is used at a smaller budget, which is what makes recursion compose.

## 6. Frames and memory in contracts

The frame window `[top - depth, top)` of each activation is in the state, so contracts can say
"writes only its own frame and these regions". The vocabulary is generalised from the
symbolic executor's (`Sym/Mem.lean`, `Region.lean`, `ByteFold.lean`) to any memory with
doubleword reads and writes:

- `Region base vs m`: the doublewords at `base, base + 8, …` hold `vs`;
- `Unchanged W m m'`: memory outside the regions `W` is unchanged;
- `Disjoint`, `InRegion`, the sub-word reads and writes.

RISC-V's `MachineState` is the instance. Memory stays flat: a pointer into a frame may escape
to a callee (out-parameters, `&mut` locals), which is common in Rust, so frames are regions,
not separate memories. Turning frames into locals is layer 1's job.

## 7. Correctness of the lift

**Transfer.** For a program lifted from an image, `SafeN` at Lprog from a state standing for a
call of a function gives `SafeN` over `stepSp1` from the machine state at its entry. Proof, by
simulation:

- Every machine step is matched by Lprog steps (a label is zero steps; anything else one).
- Inside a function the machine and the lifted code are deterministic; the simulation already
  exists for straight-line code, branches and jumps (`RiscV/Lprog/Lift.lean`).
- At `jal ra`/`jalr` to a candidate: the Lprog call pushes a frame whose `ret` is the address
  the machine put in `ra`. At `jalr x0, 0(ra)`: if Lprog's `Lret` is defined, `ra` is `ret`,
  so the machine returns to the instruction after the call.
- At `ecall`: the context's specification must **over-approximate** `stepSp1`'s `ecall`: every
  machine result is allowed by the specification. This is the one new obligation per
  syscall, proved from the existing facts.
- Lprog `trap` matches a stuck machine; `wrong` is never matched, since the Lprog judgement
  excludes it.

The machine is deterministic, so a forward simulation of every Lprog run that avoids `wrong`
covers the machine's one run, which is what `SafeN` over `stepSp1` needs.

## 8. Registers

`Isa` gets a register type with decidable equality, a stack register, an event type, and the
effect of calls and returns (§2):

```lean
structure Isa where
  Reg : Type
  [decEq : DecidableEq Reg]
  sp   : Reg
  E    : Type                                   -- events (§10); Unit for SP1
  call : (ret : BitVec 64) → Regs → M → Regs × M -- RISC-V: write the link register; x86: push
  retOk : Frame → Regs → M → Option (Regs × M)  -- the return check, and its effect
  ...
```

`call` and `retOk` replace the fixed link register of the first draft; catcrypt-compiler's
`Isa.withCalls` handles x86's push the same way.

The register file is accessed only through `get`/`set` and their lemmas, so its
representation can change later without touching proofs. RISC-V uses riscv-zkvm's own `Reg`,
which removes the translation between register names and `Reg` from the lift. `x0` reads as
zero through the interface.

**Syntax.** Operations are typed (`Op`) and the state is generic, replacing
catcrypt-compiler's mnemonic strings and fixed `LstateMF`. catcrypt-compiler's region proofs
use the array operands `arr` and `arrIdx`; they stay, or are shown expressible as `load` and
`store`. catcrypt-compiler's Jasmin export keeps Jasmin's linear syntax, with a proved
translation from the shared Lprog.

## 9. Automation

A symbolic executor at Lprog, `MachineChecked/Lprog/Sym/`, ported from `RiscV/Sym`:

- **Kept:** the `atom + constant` value normal form, the region and write-set algebra, sub-word
  folding, the omega/simp side-condition provers, the contract-application engine
  (`applySpec`, `discharge`, `readPost`, postcondition splits), branch splitting and pruning,
  `sym_close`.
- **Dropped:** everything that knows RISC-V instructions (`classify`, the `exec_*` lemmas,
  `ecallStep`). The executor dispatches on Lprog's instructions and the shared operations
  (`set`, `load`, `store`, `Lcond`, `Lcall`, `Lext`, `Lret`), so it is independent of the
  instruction set. The ISA enters only through its memory's checks.

It must be measured before the migration: three existing proofs are re-proved with it and
timed against today's (a 58-instruction deserialiser, the 293-instruction allocator, a
235-instruction segment of `main` with fifteen contracts). The target is within about twice
today's build time.

## 10. Leakage and constant time

Constant time and speculative constant time are in scope. The step's events (§3) carry what an
observer sees, under the instruction set's timing regime: addresses accessed, branch
directions, variable-time operations. `SafeN` ignores them. Constant time is a separate
two-run judgement: two runs from states that agree on public data produce equal events, as in
`SContract.ct` and catcrypt-compiler's `IsaMachine.RunL` over `CTLeak` and Lprog `EntryCT`.
Each lift proves that its events match the machine's.

Open: whether the event type follows catcrypt-compiler's leakage model exactly; where
speculative constant time lives (a speculative semantics over the shared Lprog, or per
backend, as in catcrypt-compiler's x86 backend today); and the timing regime for RISC-V
outside SP1 (Zkt).

## 11. Plan

| milestone | delivers | exit test |
| --- | --- | --- |
| A | §1–§5, §7, §8; events in the step (`E = Unit` for SP1); SP1's context; the existing Lprog proofs ported | `write_vectored`'s call to `sys_write` is an Lprog call using a contract, no machine steps by hand |
| B | §9, in the shared package | the three benchmarks re-proved, within about 2× build time |
| C | contracts and the table at Lprog; the runtime (memcpy, memset, memcmp, syscalls, allocator) re-proved; the checker's future decided (issue #12) | the runtime's machine-level statements are unchanged and proved through Lprog |
| D | the rest of zip-2005, bottom-up through the call graph; `RiscV/Sym`, `Exec`, `Frame` deleted | every function on the Lprog route; `guest_run` unchanged |

Each re-proof keeps its machine-level statement (via the transfer theorem), so callers do not
change and the end theorem stays green at every step. `PanicPaths`, the open premise of
`guest_run`, is out of scope.

## Decisions on the points left open

1. **Tail calls are a frame-replacing `Ltail`** (§2), not `Lcall; Lret`. On the machine a tail
   call does not touch `ra`, and the callee returns to the caller's caller. `Lcall; Lret` would
   push a frame the machine never has, and write a link register the machine never writes, so
   the simulation would not hold. `Ltail` is the machine's behaviour exactly. For contracts it
   is a call whose continuation is the caller's own, used at a smaller budget like `Lcall`.
2. **`depth` is an untrusted annotation of the lifted program.** Nothing in the semantics or
   in the lift's correctness depends on it: `Lret` checks only that `sp` is back at `top`, and
   memory is flat. `depth` serves contracts, which name the window `[top - depth, top)` as the
   function's own. A wrong `depth` makes a contract unprovable, never unsound. So it can come
   from any tool: initially the stack bounds `Tools/Infer.lean` already computes (the checker's
   `Iface.depth`), with a per-function override.
3. **The checker is retired, unless milestone C's numbers say otherwise.** Its trusted part
   (the Boolean check and its soundness proof over the machine) is a second proof route, which
   this design exists to remove. Its useful part (inferring footprints, stack bounds and
   indirect-call candidates for every function) moves to `Tools/` as an untrusted producer of
   annotations and draft contracts, which the Lprog executor re-proves. Exception, decided in
   milestone C: if the executor is markedly slower on the 68 functions the checker covers
   today, `Check` is ported to emit Lprog contracts instead.

## As built (milestone A)

Milestone A follows §1–§5, §7 and §8, with these departures. The code is the reference.

- **No events, and a fixed link register.** Milestone A was built before the review: the step
  is `σ → Outcome σ → Prop` with no events (§3, §4; #18), and `Isa` has a fixed `link`
  register instead of the `call` and `retOk` fields (§2, §8; #19). A call writes the link
  register, and a return checks it and `sp`.

- **`Lext` takes no name.** SP1's context (`RiscV/Lprog/Lift.lean`, `sp1Ctx`) is not restated
  per system call: its specification is "the outcome of riscv-zkvm's own `sp1Ecall` on a
  machine state the Lprog state stands for". Over-approximation (§7) then holds by definition,
  and per-call facts are lemmas over it (`lsafe_write` in `RiscV/Lprog/Rules.lean`). Accepting
  is an `ecall` with `t0 = 0` (`HALT`) and exit code 0, or an empty stack.
- **`Labort`.** An instruction the lift does not cover lifts to `Labort`, which goes `wrong`.
  A proof that reaches one fails, instead of silently stopping.
- **The postcondition is a predicate of the final state**, `Q : σ → Prop`, not a `Prop`.
  `RiscV.SafeN` is the instance at `fun _ => P`, so its statement is unchanged.
- **The transfer quantifies over every budget** (`AllSafe` in `RiscV/Lprog/Transfer.lean`):
  `SafeN` at Lprog for all `n` gives `SafeN` over `stepSp1` for the given `N`. A Lprog step can
  be matched by zero machine steps (a label), so budgets do not line up one to one; contracts
  proved for every budget, as all of them are, lose nothing.
- **Straight-line blocks run over the machine.** `reaches_block` and `corres_block`
  (`RiscV/Lprog/Block.lean`) are proved directly over `stepSp1`, not through the lift: a block
  is not a whole function, and under partial correctness a lifted block cannot hand control
  back to code outside the lifted program. Giving a lifted program exit points is #20.
- **Indirect calls and tail calls take every function as a candidate** (`List.range
  fs.length`). The control-flow premise of §2 is a hypothesis of the rules (`lsafe_call`,
  `lsafe_tail`: the register holds some function's base), not a narrowed list.
- **A lifted function carries its address.** `Fn` (`RiscV/Lprog/Lift.lean`) is `{name, base,
  prog, depth}`, with the decoded instructions as constants in the case file; `ProgOk` asks
  only that bases are 4-aligned.
- **Return-address alignment is asked only of inner frames** (`RetOk`): the outermost
  frame's return value is the caller's, unconstrained, and the machine continues at
  `ra &&& ~~~1`.
- **Not yet built:** `table_sound` (§5) and the memory vocabulary of §6. Contracts compose by
  hand, as in `Cases/Zip2005/Runtime/WriteVectored.lean`, until milestone C needs the table (#21).
