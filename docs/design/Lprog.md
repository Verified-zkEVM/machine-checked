# Design note: Lprog as a program-level verification layer

The design that makes Lprog (`lprog/Lprog`, layer 0.5) the layer where proofs about programs
happen: whole programs, calls, external calls, contracts and automation. It covers milestones
A–D of [`ROADMAP.md`](../../ROADMAP.md) steps 1–2 (issues #2–#5). Accepted 2026-10-22.

## Status

| milestone | what | status |
| --- | --- | --- |
| A | programs, calls, outcomes, external calls, the generic judgement, the transfer theorem (§1–§5, §7, §8) | done; departures from the text in [As built](#as-built-milestone-a) |
| B | automation at Lprog (§9) | in progress, as the tactic `lsym` ([`Automation.md`](Automation.md)) rather than a port of `RiscV/Sym`; `memcmp` and `write_vectored` re-proved with it; §9's three benchmarks not yet |
| C | contracts and the contract table at Lprog; the runtime re-proved; the checker's future (#12) | `Isa.Contract` built (`lprog/Lprog/Contract.lean`); `table_sound` at Lprog and the memory vocabulary of §6 not built |
| D | the rest of zip-2005 through Lprog; `RiscV/Sym`, `Exec`, `Frame` deleted | not started; zip-2005 is now in [zip-2005-asm](https://github.com/dhsorens/zip-2005-asm) |

The code is the reference where it and this note differ.

## Goal

Make Lprog the layer where proofs happen. A whole program lifts to it; functions call each
other; system calls are external calls with specifications; contracts are stated and composed
there; a symbolic executor proves them. Then zip-2005 is re-proved through it and the
machine-level proof tools (`RiscV/Sym`, `Exec`, `Frame`, possibly `Check`) are retired, leaving
one route from a binary to its specification.

Decided with the maintainer: calls are primitive (with the lift proved correct), frames are
owned regions of flat memory, and registers sit behind an interface whose type is a parameter
of the instruction set.

## 1. Programs and state

A program is a list of functions. A function has a name, a body and a stack bound:

```lean
structure Lfundef (Op Reg : Type) where
  name  : String
  body  : Lcmd Op Reg
  depth : Nat              -- the most stack it uses below its entry sp, callees excluded;
                           -- an untrusted annotation (see Decisions)
```

(As built, it also has `addr`, the value a pointer to the function holds.) A state is a stack of
activations, the register file and the rest of the machine:

```lean
structure Frame where
  fn  : Nat                -- index of the function in the program
  pc  : Nat                -- index into its body
  ret : BitVec 64          -- the value the link register held at the call
  top : BitVec 64          -- sp at the call: the frame window is [top - depth, top)

structure State (I : Isa) where
  stack : List Frame       -- innermost first; empty when the program has returned
  regs  : I.Regs           -- global, as on the machine
  m     : I.M
```

The register file is global, as on the machine: the calling convention (which registers a
callee preserves) is a property of contracts, not of the semantics. This keeps the lift a
simulation of the machine rather than an abstraction, and leaves real abstraction (registers to
variables, frames to locals) to layer 1.

## 2. Primitive calls and return-address integrity

- `Lcall f` pushes a frame for `f` at its first instruction. It sets the link register to a
  return value the instruction set supplies (for RISC-V, `pc + 4`) and records it as the frame's
  `ret`, with the current `sp` as `top`. Code that saves and restores the link register runs
  unchanged.
- `Lret` pops the frame and continues after the call. It is defined only if the link register
  holds the frame's `ret` and `sp` is back at `top`; otherwise it goes `wrong` (§3).
- An indirect call `Lcall [f₁, …, fₖ] r` calls the candidate whose entry `r` holds, and goes
  `wrong` if it holds none of them. A control-flow premise in the contract says which
  candidates a site has.
- A tail call (`jal x0, f`, or `jalr x0` to a candidate entry) lifts to `Ltail f`, which
  replaces the current frame with one for `f` with the same `ret` and `top`, and leaves the link
  register alone. It is defined only if `sp` is back at `top`. The callee's `Lret` returns
  straight to the caller's caller, as on the machine.

Because `Lret` goes `wrong` on a bad return address, and the judgement (§5) excludes `wrong`,
return-address integrity is proved at Lprog as part of every function's proof. That is what
lets the machine's `jalr x0, 0(ra)` simulate the pop, and makes `RiscV/Frame` (which proves
this property at the machine level) unnecessary.

## 3. Outcomes: `trap` and `wrong`

A step is a relation, since an external call may have many results. Each step ends in one of:

- a **state**;
- **`trap`**: the machine would be stuck too (a memory access SP1 refuses, no code at the pc).
  A trap is *safe*, as in `SafeN`: a run that stops proves nothing false;
- **`wrong`**: an assumption the lift relies on is violated (a bad return address, an indirect
  target off its list, a frame not restored). `wrong` is *unsafe*: the judgement requires it to
  be unreachable.

This distinction makes the transfer to the machine sound: every Lprog outcome other than
`wrong` is matched by the machine (§7).

## 4. External calls

`Lext` steps by a specification the execution context supplies, a relation between the state
before and the states after (or `trap`):

```lean
structure Context (I : Isa) where
  ext    : String → I.Regs → I.M → Outcome (I.Regs × I.M) → Prop
  accept : I.Regs → I.M → Prop     -- for SP1: HALT with exit code 0
```

As built, `Lext n` takes a number, and the context also carries the events each call makes
(`Context I E` in `lprog/Lprog/Sem.lean`). The lift turns `ecall` into `Lext`. For SP1, the
context is `sp1Ctx` (see As built).

## 5. One generic judgement

`SafeN` is stated once, in `lprog/Lprog/Ascent/Safe.lean`, for any machine given by a step
relation with outcomes and an accept predicate:

```lean
def SafeN (step : σ → Outcome σ → Prop) (accept : σ → Prop)
    (G : σ → Prop) (n : Nat) (P : Prop) (s : σ) : Prop :=
  -- every run of fewer than n steps from s, along which G holds,
  -- never reaches `wrong`, and ends accepting only if P
```

- RISC-V's `SafeN` is the instance at `stepSp1` (deterministic, never `wrong`) and `Accepted`,
  keeping its name and every lemma's name.
- Lprog's judgement is the instance at `Isa.step` and the context's `accept`.
- The rules (`step`, `of_step`, `assume`, `stuck`, `loop`, `loop_measure`, `budget_induction`,
  `of_reaches`) are proved once, generically (`lprog/Lprog/Ascent/Safe.lean`).
- **Contracts** are in continuation form with the budget:
  `∀ G n P s, Pre s → (∀ t, Post s t → SafeN … G n P t) → SafeN … G n P s`.
- **Correspondence is a contract.** `Ascent.Corres` is restated in this form:
  `SR m a → P a → (∀ t, SR t (fa a) → SafeN … G n Q t) → SafeN … G n Q m`. On a relational
  machine (Lprog with external calls) every run, not some run, must reach a related state or
  stop safely. The older form over `Reaches` (total correctness) implies it on a deterministic
  machine, by `SafeN.of_reaches`, so statements in that form (the CatCrypt kernels', in the tree
  at tag `with-zip2005`) remain valid and give contracts directly (RISC-V's
  `SafeN.of_corres`).
- **Composition** is a generic `table_sound`, by strong induction on the budget over a family of
  contracts (the shape of `Check/Sound/Act.lean`'s `table_sound`). At an `Lcall` the callee's
  contract is used at a smaller budget, which is what makes recursion compose. Not yet built at
  Lprog (milestone C).

## 6. Frames and memory in contracts

Each activation's frame window `[top - depth, top)` is in the state, so contracts can say
"writes only its own frame and these regions". The vocabulary is to be generalised from the
symbolic executor's (`Sym/Mem.lean`, `Region.lean`, `ByteFold.lean`) to any memory with
doubleword reads and writes:

- `Region base vs m`: the doublewords at `base, base + 8, …` hold `vs`;
- `Unchanged W m m'`: memory outside the regions `W` is unchanged;
- `Disjoint`, `InRegion`, the sub-word reads and writes.

Memory stays flat: a pointer into a frame may escape to a callee (out-parameters, `&mut`
locals), which is common in Rust, so frames are regions, not separate memories. Turning frames
into locals is layer 1's job. Not yet built (#21).

## 7. Correctness of the lift

**Transfer.** For a program lifted from an image, `SafeN` at Lprog from a state standing for a
call of a function gives `SafeN` over `stepSp1` from the machine state at its entry. By
simulation:

- Every machine step is matched by Lprog steps (a label is zero steps; anything else one).
- Inside a function the machine and the lifted code are deterministic; the simulation for
  straight-line code, branches and jumps is in `RiscV/Lift/Lift.lean`.
- At `jal ra`/`jalr` to a candidate, the Lprog call pushes a frame whose `ret` is the address the
  machine put in `ra`. At `jalr x0, 0(ra)`, if `Lret` is defined then `ra` is `ret`, so the
  machine returns to the instruction after the call.
- At `ecall`, the context's specification must **over-approximate** `stepSp1`: every machine
  result is allowed by the specification.
- An Lprog `trap` matches a stuck machine; `wrong` is never matched, since the judgement
  excludes it.

The machine is deterministic, so a forward simulation of every Lprog run that avoids `wrong`
covers the machine's one run, which is what `SafeN` over `stepSp1` needs. The theorem is
`transfer` in `MachineChecked/RiscV/Lift/Transfer.lean`.

## 8. Registers

`Isa` has a register type with decidable equality, a link register and a stack register:

```lean
structure Isa where
  Reg : Type
  [decEq : DecidableEq Reg]
  link : Reg
  sp   : Reg
  ...
```

The register file is accessed only through `get`/`set` and their lemmas, so its representation
can change without touching proofs. RISC-V uses riscv-zkvm's own `Reg`, which removes the
translation between register names from the lift. `x0` reads as zero through the interface.

## 9. Automation

The plan was to port `RiscV/Sym` to Lprog, keeping its instruction-set-independent parts (value
normal forms, region algebra, contract application, branch splitting) and dispatching on Lprog's
instructions instead of RISC-V's. What was built instead is `lsym`, a tactic written directly
over Lprog, independent of the instruction set ([`Automation.md`](Automation.md)). The exit test
still stands: re-prove three existing proofs (a 58-instruction deserialiser, the
293-instruction allocator, and a 235-instruction segment of `main` with fifteen contracts)
within about twice their current build time.

## 10. Plan

| milestone | delivers | exit test |
| --- | --- | --- |
| A | §1–§5, §7, §8; SP1's context; the existing Lprog proofs ported | `write_vectored`'s call to `sys_write` is an Lprog call using a contract, no machine steps by hand |
| B | §9 | the three benchmarks re-proved, within about 2× build time |
| C | contracts and the table at Lprog; the runtime (memcpy, memset, memcmp, syscalls, allocator) re-proved; the checker's future decided (#12) | the runtime's machine-level statements are unchanged and proved through Lprog |
| D | the rest of zip-2005, bottom-up through the call graph; `RiscV/Sym`, `Exec`, `Frame` deleted | every function on the Lprog route; zip-2005's end theorem unchanged |

Each re-proof keeps its machine-level statement (through the transfer theorem), so callers do
not change and the end theorem stays green throughout.

## Decisions

1. **Tail calls are a frame-replacing `Ltail`** (§2), not `Lcall; Lret`. On the machine a tail
   call does not touch `ra`, and the callee returns to the caller's caller. `Lcall; Lret` would
   push a frame and write a link register the machine never has, so the simulation would fail.
   For contracts, `Ltail` is a call whose continuation is the caller's own, used at a smaller
   budget like `Lcall`.
2. **`depth` is an untrusted annotation.** Nothing in the semantics or the lift's correctness
   depends on it: `Lret` checks only that `sp` is back at `top`, and memory is flat. `depth`
   serves contracts, which name `[top - depth, top)` as the function's own. A wrong `depth`
   makes a contract unprovable, never unsound, so it can come from any tool: initially the
   stack bounds `Tools/Infer.lean` computes (the checker's `Iface.depth`), with a per-function
   override.
3. **The checker is retired, unless milestone C's numbers say otherwise.** Its trusted part (the
   Boolean check and its soundness proof over the machine) is a second proof route, which this
   design exists to remove. Its useful part (inferring footprints, stack bounds and
   indirect-call candidates) moves to `Tools/` as an untrusted producer of annotations and draft
   contracts, which the Lprog automation re-proves. Exception: if that is markedly slower on the
   68 functions the checker covers, `Check` is ported to emit Lprog contracts instead.

## As built (milestone A)

Milestone A follows §1–§5, §7 and §8 with these departures:

- **Registers are a function**, `Reg → BitVec 64`, read by application and written by `updReg`
  (`lprog/Lprog/Sem.lean`), not behind the `get`/`set` interface above.

- **External calls are numbered, and SP1's are not restated per call.** `Lext n` takes a
  number. SP1's context (`sp1Ctx`, `lprog-riscv/LprogRiscV/Sp1Ctx.lean`) has as its
  specification "the outcome of riscv-zkvm's `sp1Ecall` on a machine state the Lprog state
  stands for", so over-approximation (§7) holds by definition, and per-call facts are lemmas
  over it (`lsafe_write` in `RiscV/Lift/Rules.lean`). Accepting is an `ecall` with `t0 = 0`
  (`HALT`) and exit code 0, or an empty stack. It makes no events yet.
- **`Labort`.** An instruction the lift does not cover lifts to `Labort`, which goes `wrong`. A
  proof that reaches one fails rather than silently stopping.
- **The postcondition is a predicate of the final state**, `Q : σ → Prop`, not a `Prop`.
  `RiscV.SafeN` is the instance at `fun _ => P`, so its statement is unchanged.
- **The transfer quantifies over every budget** (`AllSafe` in `RiscV/Lift/Transfer.lean`):
  `SafeN` at Lprog for all `n` gives `SafeN` over `stepSp1` for the given `N`. An Lprog step
  can match zero machine steps (a label), so budgets do not line up one to one; contracts proved
  for every budget, as all are, lose nothing.
- **Straight-line blocks run over the machine.** `reaches_block` and `corres_block`
  (`RiscV/Lift/Block.lean`) are proved directly over `stepSp1`, not through the lift: a block is
  not a whole function, and under partial correctness a lifted block cannot hand control back to
  code outside the lifted program. Giving a lifted program exit points is follow-up work.
- **Indirect call candidates.** `liftProg` gives a `jalr` preceded by an `auipc` of its register
  the one function at the address they compute, and every function otherwise (`jalrCands` in
  `RiscV/Lift/Lift.lean`). Any list is sound (`callee_indirect`): a target outside it is
  `wrong`, which a safety proof excludes. The control-flow premise of §2 is a hypothesis of the
  rules (`lsafe_call`, `lsafe_tail`: the register holds some function's base).
- **A lifted function carries its address.** `Fn` (`RiscV/Lift/Lift.lean`) is `{name, base,
  prog, depth}`, with the decoded instructions as constants in the case file; `ProgOk` asks only
  that bases are 4-aligned.
- **Return-address alignment is required only of inner frames** (`RetOk`): the outermost
  frame's return value is the caller's, unconstrained, and the machine continues at
  `ra &&& ~~~1`.
- **Contracts** are `Isa.Contract` over the register file (`lprog/Lprog/Contract.lean`), composed
  through `lsym … using`; there is no `table_sound` at Lprog yet.
