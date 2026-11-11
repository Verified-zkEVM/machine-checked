# Architecture: the judgement and the contract table

How results about a whole binary are stated and composed, today for RISC-V on SP1. The layers
these sit in are described in [`ROADMAP.md`](../ROADMAP.md); what is trusted is in
[`ELF.md`](ELF.md) §4.

**Judgement.** `SafeN n P s`: every accepting state reached from `s` in fewer than `n` steps
satisfies `P`. `Safe P s := ∀ n, SafeN n P s`. A function specification is in continuation
form, *step-indexed*:

    ∀ P n s, s.pc = entry → pre s → (∀ t, post s t → SafeN n P t) → SafeN n P s

The same budget `n` appears on both sides. This is what lets a caller's proof use a callee's
specification inside an induction on the budget. That covers loops, recursion, and a
function that calls back into its caller. Executor proofs carry `n` through unchanged, since a
step preserves `SafeN n`.

**Structural specification** of a function. It is derived by the frame checker, or proved
by hand where the checker cannot:
- `pre`: the code is the image's; `D ≤ sp ≤ STACK_TOP`, where `D` is the function's
  worst-case stack use, callees included; and the premises `reqs` over the entry registers.
- `post`: `t.pc = ra & ~1`; `sp`, `gp`, `tp` and `s0`–`s11` hold their entry values; and
  memory outside the footprint `W(entry)` is unchanged. `W` is the frame window
  `[sp - D, sp)` plus regions given by entry registers (`a0 + k`, length a constant or an
  entry register) and constant addresses.
- A function that cannot return has `post = False`. Calls to it are how "noreturn" stops
  being an assumption.
- No internal accepting halt. A halt's exit code must be provably nonzero (a `req` if it
  comes from an argument).

**Contract table.** A map from entry address to specification. Each entry is derived by
the checker or proved with the executor. The checker proves a function's specification from
its certificate, assuming its callees' specifications. Composition is a strong induction on
the budget over the whole table. A callee's `reqs` and footprint are instantiated at the
call site with the caller's abstract argument values. The result is either discharged
there, or becomes the caller's own `req`. An indirect call or tail call takes a candidate
list and a control-flow premise (`CfiOk`) that the target is on it.

**Two ways to prove a table entry.** An entry is either derived by the checker
(`MachineChecked/RiscV/Check`) or proved by hand. A hand proof is preferably done at the low
logical program (`MachineChecked/RiscV/Lprog`): the function is lifted, a contract is proved
for it at Lprog, and the contract is carried down to `stepSp1` by the lift's transfer theorem
(`transfer`, `SafeN.of_contract`).
The older route, symbolic execution over the machine (`MachineChecked/RiscV/Sym`,
`MachineChecked/RiscV/Exec`), is what the zip-2005 proofs use; it is layer-0 tooling, and
whether it moves up onto the lift or stays as a fallback is an open question of the roadmap.
