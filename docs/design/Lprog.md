# Design note: Lprog as a program-level verification layer

**Status: proposal, for review.** It fixes the design of milestones A–D in
[`ROADMAP.md`](../../ROADMAP.md) steps 1–3 (issues #2–#5). Nothing here is implemented yet.

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
  depth : Nat              -- the most stack it uses below its entry sp, callees excluded
```

A state is a stack of activations, the register file and the rest of the machine:

```lean
structure Frame where
  fn  : Nat                -- index of the function in the program
  pc  : Nat                -- index into its body
  ret : BitVec 64          -- the return value the link register held at the call
  top : BitVec 64          -- sp at the call: the frame window is [top - depth, top)

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

- `Lcall f` pushes a frame for `f` at its first instruction. It sets the link register to a
  return value the instruction set supplies (for RISC-V, the machine return address `pc + 4`)
  and records it as the frame's `ret`, with the current `sp` as `top`. Code that saves and
  restores the link register (as compiled code does) therefore runs unchanged.
- `Lret` pops the frame and continues after the call in the caller. It is defined only if the
  link register holds the frame's `ret` and `sp` is back at `top`. Otherwise it goes `wrong`
  (§3).
- An indirect call `Lcall [f₁, …, fₖ] r` calls the candidate whose entry the register `r`
  holds, and goes `wrong` if it holds none of them; a control-flow premise in the contract
  (as `Env.Cfi` today) says which candidates a site has.
- Tail calls lift to `Lcall` followed by `Lret`, or directly as a jump to another function's
  entry with the frame replaced; the choice is left to the implementation.

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
than `wrong` is matched by the machine (§7).

## 4. External calls

`Lext name` steps by a specification the execution context supplies, a relation between the
state before and the states after (or `trap`). The context is a record:

```lean
structure Context (I : Isa) where
  ext    : String → I.Regs → I.M → Outcome (I.Regs × I.M) → Prop
  accept : I.Regs → I.M → Prop     -- for SP1: HALT with exit code 0
```

For SP1, the specifications are restated once from the facts the layer-0 tools prove today
(`Sym/Syscall.lean`, `Check/Ecall.lean`, `Exec/Hint.lean`): `HALT`, `WRITE`, `COMMIT`,
`COMMIT_DEFERRED_PROOFS`, `HINT_LEN`, `HINT_READ` and the accelerators. The lift turns `ecall`
into `Lext` on the id in `t0`. The context is not otherwise parameterised in this pass.

## 5. One judgement, generic

`SafeN` moves to `MachineChecked/Ascent/Safe.lean`, stated for any machine given by a step
relation with outcomes and an accept predicate:

```lean
def SafeN (step : σ → Outcome σ → Prop) (accept : σ → Prop)
    (G : σ → Prop) (n : Nat) (P : Prop) (s : σ) : Prop :=
  -- every run of fewer than n steps from s, along which G holds,
  -- never reaches `wrong`, and ends accepting only if P
```

- RISC-V's `SafeN` becomes the instance at `stepSp1` (deterministic, never `wrong`) and
  `Accepted`, keeping its name and every lemma's name, so nothing that uses it changes.
- Lprog's judgement is the instance at `Isa.step` and the context's `accept`.
- The rules (`step`, `of_step`, `steps`, `assume`, `loop`, `loop_measure`, `cases`) are proved
  once, generically.
- **Contracts** are in continuation form with the budget, as today:
  `∀ G n P s, Pre s → (∀ t, Post s t → SafeN … G n P t) → SafeN … G n P s`.
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

`Isa` gets a register type with decidable equality, a link register and a stack register:

```lean
structure Isa where
  Reg : Type
  [decEq : DecidableEq Reg]
  link : Reg
  sp   : Reg
  ...
```

The register file is accessed only through `get`/`set` and their lemmas, so its
representation can change later without touching proofs. RISC-V uses riscv-zkvm's own `Reg`,
which removes the translation between register names and `Reg` from the lift. `x0` reads as
zero through the interface.

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

## 10. Plan

| milestone | delivers | exit test |
| --- | --- | --- |
| A | §1–§5, §7, §8; SP1's context; the existing Lprog proofs ported | `write_vectored`'s call to `sys_write` is an Lprog call using a contract, no machine steps by hand |
| B | §9 | the three benchmarks re-proved, within about 2× build time |
| C | contracts and the table at Lprog; the runtime (memcpy, memset, memcmp, syscalls, allocator) re-proved; the checker's future decided (issue #12) | the runtime's machine-level statements are unchanged and proved through Lprog |
| D | the rest of zip-2005, bottom-up through the call graph; `RiscV/Sym`, `Exec`, `Frame` deleted | every function on the Lprog route; `guest_run` unchanged |

Each re-proof keeps its machine-level statement (via the transfer theorem), so callers do not
change and the end theorem stays green at every step. `PanicPaths`, the open premise of
`guest_run`, is out of scope.

## Open points for review

1. **Tail calls:** `Lcall; Lret`, or a frame-replacing jump (§2)?
2. **`depth` per function:** taken from the checker's inference, or proved per function at
   Lprog? (The window only needs to be large enough for the contract.)
3. **The checker:** emit Lprog contracts, or retire it once the executor covers its ground?
   To be decided in milestone C, with numbers.
