# The structured logical program: a design sketch

> **Status (2026-10-21): a sketch of layer 1, not implemented.** In
> [`ROADMAP.md`](../ROADMAP.md)'s terms this is the *structured logical program* (layer 1):
> variables, structured control flow, function contracts. What exists is the layer below it,
> the *low logical program* (layer 0.5): `MachineChecked/Lprog`, CatCrypt's linear Jasmin
> (`Lprog`) with operations shared by every instruction set (`Lprog/Op.lean`). RISC-V lifts
> into it (`MachineChecked/RiscV/Lprog`). The lift from layer 0.5 into the structured program
> sketched here is decompilation, per function and possibly partial. The home for this layer
> is `MachineChecked/Logical/`.

## LogicalProgram: an ISA-independent logical machine

Introduce a small, ISA-independent intermediate machine (`LogicalProgram`) between concrete ISA semantics and higher-level program reasoning.

### Purpose

`LogicalProgram` is the target of **logical decompilation**. It removes irrelevant architectural details (register allocation, PCs, instruction sequences, stack offsets, etc.) while preserving the computational structure and effects needed for verification.

For example, RISC-V code manipulating `x5`, `x6`, and concrete memory addresses might be logically decompiled into a state containing meaningful variables such as:

- `i : Nat`
- `acc : BitVec 32`
- `hashState : Vector (BitVec 32) 8`
- `inputPtr : Addr`

### Core design

A `LogicalProgram` should provide:

- **Typed logical state**, chosen per program rather than a fixed register file.
- **Control flow**: basic blocks, branches, loops, calls/returns.
- **Pure computation**: especially first-class bitvector operations.
- **Explicit effects**: loads, stores, and eventually atomics/fences/external interactions.
- **Optional observations/traces**: memory accesses, branches, instruction/cycle costs, etc.

It should *not* contain:

- RISC-V-specific concepts such as `x0..x31`, `jal`, instruction encodings, etc.
- A particular program logic (Hoare logic, separation logic, Iris, etc.).
- Application-specific specifications such as SHA-256 or XMSS.

### Relationship to ASCENT-style logical decompilation

ASCENT-style reasoning sits **below `LogicalProgram`**.

Its job is to construct/prove an abstraction relation between concrete machine states and logical states:

    Rep : RiscV.State -> LogicalState -> Prop

and establish a simulation/refinement theorem roughly of the form:

    RISC-V program ⊑ LogicalProgram

For example:

    RISC-V:
      x5 = base + 4*x6
      lw x7, 0(x5)
      add x8, x8, x7
      addi x6, x6, 1
      ...

                │
                │ ASCENT-style logical decompilation
                ▼

    LogicalProgram:
      while i < n:
        x   := load32(base + 4*i)
        acc := acc + x
        i   := i + 1

The internal symbolic states used by ASCENT are decompiler/proof infrastructure; they need not be part of the public `LogicalProgram` abstraction.

### Overall verification stack

    Cryptographic / mathematical specification
                    ▲
                    │ correctness / refinement
                    │
             Program logic(s)
       Hoare / separation / relational /
          cost / concurrency / etc.
                    ▲
                    │
              LogicalProgram
        ISA-independent logical machine
                    ▲
                    │
        ASCENT-style logical decompilation
          + simulation/refinement proof
                    │
             ISA semantics
       RISC-V initially; x86/ARM later
                    ▲
                    │
               ELF loading
                    ▲
                    │
                  Binary

The intended proof chain is therefore:

    Binary / RISC-V
          ⊑
    LogicalProgram
          ⊑
    Algorithmic specification

The first refinement is the **logical decompilation problem**; the second is the **program correctness problem**.

This separation makes the logical layer reusable across ISAs and allows different program logics to operate over the same decompiled program. In particular, functional correctness, separation logic, constant-time/noninterference, cost reasoning, and eventually concurrency can be added without changing the fundamental decompilation interface.

## Rough Lean Pseudocode

```
/-- Observable effects a logical program may perform. -/
inductive Effect where
  | load   (addr : Expr) (width : Width)
  | store  (addr : Expr) (width : Width) (value : Expr)
  | event  (e : ObsEvent)
  -- perhaps later:
  | atomic ...
  | fence ...
  | external ...

/-- Terminator of a basic block. -/
inductive Terminator where
  | goto    (target : Label)
  | branch  (cond : Expr) (ifTrue ifFalse : Label)
  | ret     (value : Option Expr)

/-- Straight-line logical operations. -/
inductive Stmt where
  | assign (x : Var) (e : Expr)
  | effect (x : Option Var) (e : Effect)
  | assert (p : Expr)          -- optional, useful for proof structure

structure Block where
  params : List Var
  body   : List Stmt
  term   : Terminator

structure LogicalProgram where
  entry  : Label
  blocks : Label → Option Block
```