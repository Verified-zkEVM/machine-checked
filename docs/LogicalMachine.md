# The structured logical program: a design sketch

A design sketch, not implemented. It describes what layer 1 of [`ROADMAP.md`](../ROADMAP.md)
should eventually provide: an ISA-independent program with typed variables and structured
control flow, over which program logics are proved.

**What exists today.** Layer 1 is Pancake, with Flapjack's syntax, in `MachineChecked/Logical`
([README](../MachineChecked/Logical/README.md)). Lift 2 takes an Lprog program (layer 0.5,
`lprog/Lprog`) to a Pancake program with recovered functions and structured control flow.
Nothing about lift 2 is proved yet, and it does not recover variables or types: registers stay
global variables and the stack stays memory. The sketch below is the target for that layer:
variables, typed state, and program logics on top. The name `LogicalProgram` and the
pseudocode are illustrative; no such definitions exist in the code.

## Purpose

`LogicalProgram` is the target of logical decompilation. It removes architectural detail
(register allocation, program counters, instruction sequences, stack offsets) and keeps the
computation and the effects needed for verification. For example, RISC-V code that uses `x5`,
`x6` and concrete addresses might become a state with variables such as:

- `i : Nat`
- `acc : BitVec 32`
- `hashState : Vector (BitVec 32) 8`
- `inputPtr : Addr`

## What it contains

- Typed logical state, chosen per program rather than a fixed register file.
- Control flow: basic blocks, branches, loops, calls and returns.
- Pure computation, with first-class bitvector operations.
- Explicit effects: loads and stores, later atomics, fences and external interactions.
- Optional observations: memory accesses, branches, instruction or cycle costs.

It does not contain ISA-specific concepts (`x0..x31`, `jal`, encodings), a particular program
logic (Hoare, separation logic, Iris), or application-specific specifications (SHA-256,
XMSS).

## Relation to the ascent

The ascent (`lprog/Lprog/Ascent`: runs and correspondences for any step function) sits below
`LogicalProgram`. Decompilation constructs an abstraction relation between machine states and
logical states,

    Rep : RiscV.State -> LogicalState -> Prop

and proves a refinement, roughly `RISC-V program ⊑ LogicalProgram`. For example:

    RISC-V:                         LogicalProgram:
      x5 = base + 4*x6                while i < n:
      lw x7, 0(x5)                      x   := load32(base + 4*i)
      add x8, x8, x7                    acc := acc + x
      addi x6, x6, 1                    i   := i + 1
      ...

The decompiler's internal symbolic states are proof infrastructure and need not be part of
the public `LogicalProgram` interface.

## The intended proof chain

    Binary ⊑ LogicalProgram ⊑ algorithmic specification

The first refinement is the decompilation problem; the second is the program-correctness
problem. Keeping them separate makes the logical layer reusable across ISAs, and lets
different program logics (functional correctness, separation logic, constant time and
noninterference, cost, later concurrency) work over the same decompiled program without
changing the decompilation interface.

## Pseudocode

```
/-- Observable effects a logical program may perform. -/
inductive Effect where
  | load   (addr : Expr) (width : Width)
  | store  (addr : Expr) (width : Width) (value : Expr)
  | event  (e : ObsEvent)
  -- later: atomic, fence, external

/-- Terminator of a basic block. -/
inductive Terminator where
  | goto    (target : Label)
  | branch  (cond : Expr) (ifTrue ifFalse : Label)
  | ret     (value : Option Expr)

/-- Straight-line logical operations. -/
inductive Stmt where
  | assign (x : Var) (e : Expr)
  | effect (x : Option Var) (e : Effect)
  | assert (p : Expr)          -- optional, for proof structure

structure Block where
  params : List Var
  body   : List Stmt
  term   : Terminator

structure LogicalProgram where
  entry  : Label
  blocks : Label → Option Block
```
