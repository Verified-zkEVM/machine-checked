# Architecture: the judgement and the contract table

How results about a whole binary are stated and composed. This is current for RISC-V on SP1;
x86-64 and AArch64 have no judgement yet. The layers are described in
[`ROADMAP.md`](../ROADMAP.md), and what is trusted in [`ELF.md`](ELF.md) §4.

## The judgement

`SafeN G n P s` (`MachineChecked/RiscV/Safe.lean`): every accepting state reached from `s` in
fewer than `n` steps, along a run whose every state satisfies the guard `G`, satisfies `P`.
Accepting means SP1's `HALT` with exit code 0 (`Accepted`). It is partial correctness: a run
that traps, rejects or diverges is safe. The guard carries premises about runs, such as the
targets of indirect jumps; with `G = fun _ => True` it is plain safety.
`Safe G P s := ∀ n, SafeN G n P s`.

A function specification is in step-indexed continuation form:

    ∀ G n P s, s.pc = entry → Pre s → (∀ t, Post s t → SafeN G n P t) → SafeN G n P s

The same budget `n` appears on both sides. This lets a caller's proof use a callee's
specification inside an induction on the budget, which covers loops, recursion, and functions
that call back into their caller. A step never raises the budget a proof needs
(`SafeN.of_step`), so symbolic execution carries `n` through unchanged.

## Structural specifications

A function's structural specification is derived by the contract checker
(`MachineChecked/RiscV/Check`), or proved by hand where the checker cannot:

- `Pre`: the code is the image's; `D ≤ sp ≤ STACK_TOP`, where `D` is the function's
  worst-case stack use including callees; and premises `reqs` over the entry registers.
- `Post`: `t.pc = ra & ~1`; `sp`, `gp`, `tp` and `s0`–`s11` hold their entry values; and
  memory outside the footprint `W(entry)` is unchanged. `W` is the frame window
  `[sp - D, sp)`, plus regions given by entry registers (`a0 + k`, with a constant or
  entry-register length), plus constant addresses.
- A function that cannot return has `Post = False`. Calls to it are how "noreturn" is proved
  rather than assumed.
- No accepting halt inside a function. A halt's exit code must be provably nonzero (a `req`
  if it comes from an argument).

## The contract table

The contract table maps each entry address to a specification. The checker proves a
function's specification from its certificate, assuming its callees' specifications.
Composition is a strong induction on the budget over the whole table (`table_sound`). At a
call site, a callee's `reqs` and footprint are instantiated with the caller's abstract
argument values; each is then either discharged there or becomes one of the caller's own
`reqs`. An indirect call or tail call takes a list of candidate targets and a control-flow
premise (`CfiOk`) that the target is on it.

## Proving a table entry

An entry is either derived by the checker or proved by hand. Hand proofs should go through
the lift: lift the function to Lprog (`MachineChecked/RiscV/Lift`), prove a contract there,
and carry it down to `stepSp1` with the transfer theorem (`transfer`, `SafeN.of_contract`,
`SafeN.of_isa_contract`).
[`Walkthrough.md`](Walkthrough.md) shows this end to end.

The older route is symbolic execution over the machine (`MachineChecked/RiscV/Sym`,
`MachineChecked/RiscV/Exec`). Most of zip-2005 was proved with it while it was a case study
here (the tree at tag `with-zip2005`). Whether these layer-0 tools
move up onto the lift or stay as a fallback is an open question in the roadmap.
