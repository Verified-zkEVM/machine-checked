---
name: formal-verification
description: >
  Prove a loaded image meets its high-level specification, from the
  bytecode through to that spec. Use when verifying machine code, ascending
  from a decoded image to a formal spec, or reviewing whether a theorem
  actually states what the bytecode does.
disable-model-invocation: true
argument-hint: "[case]"
---

# Formal verification

Adapted for MachineChecked from [dhsorens/skills](https://github.com/dhsorens/skills)
`formal-verification`. This copy is the host's. Do not fetch the library
copy to "correct" a binding.

You run the verification pass: from the bytecode of a loaded image to
the high-level specification that image is claimed to meet. Success is
a real disagreement with the run, a vacuous claim exposed, or a theorem
that connects the loaded bytecode to that spec with an explicit trust
base. A green proof of a weak or mis-aimed statement is not progress.

Do **not** treat this as a source-code diff. Honesty about what the
theorems cover is [coverage.md](coverage.md).

`$ARGUMENTS` names the case (the image and its spec). When it is empty,
use the case the session is about.

## Host bindings

| binding | this host |
| --- | --- |
| bytecode | The loaded image and `riscv-zkvm`'s SP1 machine: `MachineState`, `stepSp1`. The dependency is pinned in `lakefile.toml` and left unmodified. Image facts live under `Cases/<case>/` (`Loaded.lean`, `Image/`). Host wrappers: `MachineChecked/RiscV/Exec`, `MachineChecked/RiscV/Load`. |
| spec | The high-level claim about what that bytecode computes. The user names it, otherwise the case module and `docs/TO-VERIFY.md`. Blake2s: BLAKE2s-256 of the advice bytes, length and digest committed (`Cases/LeanVM/Blake2s/Loaded.lean`). zip-2005: the guest program over the verified runtime (`docs/PLAN.md`, `docs/TO-VERIFY.md`). |
| proofs | `MachineChecked/RiscV/` (framework) and `Cases/` (`Cases/Zip2005`, `Cases/LeanVM`). |
| observation | `SafeN` / `Safe` and `Iface.HoldsN` / `Iface.Holds` in `MachineChecked/RiscV/Check/Spec.lean`. Accepting is `Accepted`: SP1 `HALT` with exit code 0. |
| state rel | `AState.Holds` (`MachineChecked/RiscV/Frame/Sound.lean`). Checker interfaces: `Pre`, `Post`, `Env` (`MachineChecked/RiscV/Check/Domain.lean`, `Check/Spec.lean`). |
| queue | `docs/PLAN.md` |
| contract | `docs/PLAN.md` (the judgement and the Rules) and `README.md` |
| doctrine | `AGENTS.md` and `docs/PLAN.md` § Rules |
| base | `main` |
| gates | `lake build`, zero warnings. No `sorry`, no new `axiom`, no `native_decide`. `bv_decide` is allowed (it adds a `…_native.bv_decide.ax_…` axiom). Otherwise `#print axioms` shows only `propext`, `Classical.choice`, and `Quot.sound`. |
| assumptions | `none` as a file. Standing trust is `docs/PLAN.md` § Rules and `docs/ELF.md` §4. A new hypothesis that restricts the domain goes in the theorem and is noted in `docs/PLAN.md`. Do not create `Assumptions.lean` to have somewhere to write. |
| mismatches | `none` as a file. Historical false contracts are `docs/ELF.md` §1 (T1, T4, T5, Heap). A new disagreement is written into `docs/PLAN.md` before the proof is weakened. Do not create `docs/mismatches.md`. |
| coverage | `docs/PLAN.md`. There is no separate matrix. Do not create one. |
| scars | `docs/ELF.md` §1 |
| attack | `none` |
| prover | `none` |
| forbidden | editing `riscv-zkvm`; importing `zip-2005-asm`; hand-editing generated modules under `Cases/*/Image/`; `sorry`; a new `axiom`; `native_decide`; a `Co-authored-by` trailer |

Start at the image and at `stepSp1`, `SafeN`, and `Iface.HoldsN` as they
are today. Inspect them. Do not guess shapes or theorem names.

This skill does not open a PR and does not merge. The hunt list below
is how a review of the claim should read.

## The pass

Carry the proof from the bytecode to the spec.

1. **Bytecode.** Read the loaded image: layout, decoded words, entry.
   The machine is `stepSp1`. Confirm the decode facts the case already
   has, and state the ones the ascent needs.
2. **Spec.** State the high-level specification in Lean: the property
   of an accepting run that a caller of this case actually cares about.
   Read the case before writing it. The spec names its inputs, its
   result, and the halt it considers success.
3. **Observation.** Fix what the spec may mention before proving. On
   this host that is `Accepted`, the return convention, callee-saved
   registers, memory outside the footprint and the protected regions,
   and the owned invariant. Caller-saved scratch and bytes inside the
   frame window stay out of the spec unless the spec names them.
4. **Ascent.** Prove the loaded state satisfies the spec. Along the way:
   image well-formedness; a specification for every function on the
   path from the entry to the spec (`Iface.HoldsN`, or `Safe G False`
   when the function cannot return); the runtime the real load actually
   executes (entry, syscalls, allocator, panics), so every hypothesis
   is inhabited by that load; composition of the contract table by
   induction on the budget; the top theorem from the loaded state to
   the spec.
5. **Gates.** `lake build` the modules the pass touched, with zero
   warnings. No `sorry`, no new `axiom`, no `native_decide`.
6. **Record.** Update `docs/PLAN.md` so it matches the theorems. A
   disagreement between `stepSp1` and the spec is written there before
   any statement is weakened. Follow [coverage.md](coverage.md).

The top theorem is the result of the pass. A function specification,
a runtime lemma, or a relation is part of that proof.

## Host reading

`SafeN G n P s` (`Check/Spec.lean`): every accepting state reached from
`s` in fewer than `n` steps, on a run whose states satisfy `G`, satisfies
`P`. A run that traps, rejects, or diverges is safe. A function
specification is continuation-form, the same budget on both sides:

```lean
theorem example_spec (hG : ∀ x, G x → env.Cfi x) :
    ∀ (P : Prop) (s : MachineState), s.pc = σ.entry → Pre env C σ s →
      (∀ t, Post env σ s t → SafeN G n P t) → SafeN G n P s
```

That is `Iface.HoldsN`. A function that cannot return has a false
postcondition (`Safe G False` / `returns := false`). An internal halt's
exit code must be provably nonzero.

- The two things to inspect are the bytecode (`stepSp1` on the image)
  and the high-level spec.
- **Full** means the top theorem covers every reachable path to an
  *accepting* halt, a noreturn path is proved never to accept, and
  every hypothesis is met by the real run. Traps, rejects, and
  divergence are already safe; they are not extra outcomes to relate.
- A precondition the image never meets is a vacuous theorem. That is
  the failure mode in `docs/ELF.md` §1. It is not progress, and it is
  the highest-yield hunt on this host.
- The bar in `docs/PLAN.md`: no hypothesis the real run does not
  satisfy, and no contract quantified over states the run never reaches.

## Four layers (keep distinct)

| layer | what it is | who audits it |
| --- | --- | --- |
| 1 | what the bytecode does, and what the spec says | read the definitions |
| 2 | the bridge: `AState.Holds`, `Pre`, `Post`, `Env` | this skill |
| 3 | the stated observation, up to the top theorem | the theorem statement |
| 4 | the proof | `gates` |

A green layer-4 proof does not certify layers 1–3. Audit those
explicitly. Prefer, in order:

1. a real disagreement with the thing that runs
2. a vacuous or false guarantee
3. a model / relation / observation blind spot
4. a meaningful claim with an explicit trust base
5. an honest unknown

## What the spec may say

The observables are the ones in `Pre` / `Post` / `Accepted`: return to
`ra` with the low bit cleared, callee-saved registers, memory outside
the footprint and the protected regions, the owned invariant, and
whether an accepting halt (exit code 0) is reachable. The high-level
spec is a property of those, not of implementation scratch.

Decompose with the relations the host already has (`AState.Holds`,
region disjointness, `Env`). Prefer a footprint over requiring the
whole memory to be unchanged.

A failed attempt to prove the spec is often the most useful output.
Treat it as a disagreement with the run, and write it in `docs/PLAN.md`
before changing the statement.

## Working principles

1. State the high-level spec, and the observation it is allowed to
   mention, before proving the functions underneath it.
2. Separate representation proofs from semantic proofs.
3. Make every assumption explicit. A new domain hypothesis is named in
   `docs/PLAN.md`.
4. Treat accepting halts and noreturn paths as part of the spec.
5. Use finite datatypes and exhaustive matching where the image is finite.
6. Do not silently restrict `Pre` until the image happens to agree.
7. Record every discovered disagreement, including a deliberate
   difference, in `docs/PLAN.md` before adjusting the proof.
8. Prefer small compositional lemmas feeding the top theorem from the
   loaded state to the spec.
9. Keep `docs/PLAN.md` current ([coverage.md](coverage.md)).
10. When adding an assumption, ask whether it is an invariant of the
    run or only avoids a hard case.
11. Treat proof attempts as bug-finding.
12. Keep the four layers distinct.

## Proof structure

Keep the tree the host already has. Framework proofs live in
`MachineChecked/RiscV/` (`Frame`, `Check`, `Exec`). A case lives in
`Cases/<image>/` (`Image`, `Contract`, `Frame`, `Runtime`). Do not
create `Left/`, `Right/`, `Simulation/`, or `Assumptions.lean`.

| layer | what the pass proves there |
| --- | --- |
| 1 Representation | the image, the layout, the decoding |
| 2 Semantic components | reusable memory, frame, and fact lemmas |
| 3 Function specifications | `Iface.HoldsN` for each function on the path: return postcondition, or never-accepts |
| 4 Composition | the contract table, by induction on the budget |
| 5 Whole program | from the loaded state, through the runtime, to the high-level spec |

Critically examine every added precondition. A theorem that only
describes the return path, while a reachable path accepts, is not the
claim. A theorem whose `Pre` the image never meets is not the claim.

**Partial / opaque dispatch blocks what it *names*, not what it
encloses.** An arm whose body names nothing in a `partial` / opaque
block can still be total. Check the arm, not the keyword on the
match.

## Assumptions

Every assumption used by a theorem the pass claims. Categorize:
validity of the model, configuration, representation invariant,
environment / host, crypto primitive, external theorem, unproved
implementation, deliberate scope restriction.

For each: why required, who guarantees it, can a reachable state
violate it, is it part of the intended statement, eliminable by
proving?

**A negative claim needs a search whose root can contain the
answer.** "`X` does not exist" is much stronger than "I did not find
`X`." Root the search where a top-level module would sit. A guard
that shares your search is one observation, not two.

**A citation resolving in a different model still needs checking.**
Confirm the name is in this image or in `riscv-zkvm`, not a sibling
package that happens to share a symbol.

**Check drift both ways.** An account that overstates is dangerous;
one that understates makes the pass look weaker than it is and
misdirects the next reading of `docs/PLAN.md`.

## Disagreements

When the bytecode and the spec disagree, do not change the proof
first. Write the note in `docs/PLAN.md`. Machine behavior is what
`stepSp1` does on the image; claimed behavior is what the spec says.
Record:

- area
- machine behavior
- claimed behavior
- triggering state
- expected behavior + source
- configuration
- reachability
- severity
- likely cause
- disposition (machine / spec / image import / relation / config /
  intentional abstraction / unreachable / ambiguity / needs
  investigation)

"I cannot prove this without assuming X" is better than silently
assuming X. Write X down.

## When the pass is finished

The pass is finished when the top theorem says the loaded bytecode
meets the spec, the gates are green, and `docs/PLAN.md` matches the
theorems. Prefer a story that can be checked:

- **Image** — layout and decode are theorems about this image.
- **State** — every observable the spec mentions is in `Pre` / `Post`
  / `Accepted`, or explicitly left out.
- **Outcomes** — every reachable accepting path, and every noreturn
  path on the way to the spec.
- **Configuration** — the theorem names the image and the machine.
  Do not mix SP1 with another backend by accident.
- **Trust** — `riscv-zkvm` at its pin, the Lean kernel, `bv_decide`
  where it is used, and the import of the image. State that.

Do not assume the invariant you claim to establish
(`(hInv : Invariant s) → Safe s` with no reachability story from the
loaded state).

## Stuck

- **The statement is unsupported** (unsound goal, missing bridge,
  relation bug, upstream `partial` / opaque): stop that lemma. Write
  the evidence in `docs/PLAN.md`. Restate or fix the relation. Do not
  weaken the top theorem to avoid the evidence, and do not send the
  bad statement to a prover.
- **The statement still looks sound** after real attempts: check
  whether a reachable state of this image falsifies it, whether the
  observation boundary is wrong, and whether the disagreement is
  material. If it is, record it. If it is not, decompose the lemma
  and keep going. There is no external prover. The host does not
  accept `sorry`.

## Review checklist

Before treating the top theorem as the claim:

- [ ] The theorem starts from the loaded image and ends at the spec
- [ ] Every reachable accepting path is covered; noreturn paths never accept
- [ ] Return address, callee-saved registers, footprint, and halt kind are covered where the spec can see them
- [ ] Configuration-dependent semantics are accounted for
- [ ] Implementation-only effects stay out of the spec
- [ ] Assumptions are visible; `Pre` is not vacuously restrictive
- [ ] Reachable states of this image can meet the stated preconditions
- [ ] The relation does not identify observably different states
- [ ] Every function on the path has a theorem, or an explicit gap in `docs/PLAN.md`
- [ ] Proof difficulty was checked for semantic signal (bug, disagreement, bad statement) before more tactics

## Hunt list

For the top theorem, and for each function specification it depends on:

```text
Name:
Statement:     (unfolded)
Runs as:       (the code the theorem actually talks about)
Observation:   (what a caller will read the claim as)
Vacuous?:      uninhabited precondition, unused assumption, side condition
Reads differently?:
```

Highest yield: an unsatisfiable precondition; a postcondition that
drops an accepting path; a claim satisfied by the wrong event; a
`Pre` that excludes states the real load reaches; a note in
`docs/PLAN.md` that calls a return-only theorem the spec.

## Anti-patterns

| temptation | do this instead |
| --- | --- |
| A return-only theorem offered as the spec | Cover every reachable accepting path; prove noreturn paths never accept |
| Restrict `Pre` until the proof closes | Ask whether the restriction is an invariant of the run; otherwise record the disagreement |
| Add `axiom` or `sorry` for a stuck lemma | Decompose or restate. The host allows neither |
| Leave unused hypotheses | Tighten the statement. An unused assumption means the theorem is not tight |
| Change the spec to match a stuck proof | Record the disagreement in `docs/PLAN.md`, then restate |
| Prove the spec against a `partial` / opaque dispatcher | Prove it against the code the image actually runs |
| Hand-edit a generated image module | The image is an input. Change the proof or the spec |
| Report progress in chat | `docs/PLAN.md` and the top theorem are the claim |

## Interaction style

- Be concise. Prefer theorem sketches, tables, invariants, concrete
  decompositions.
- Inspect definitions before proposing replacements.
- Label clearly: discovered facts / the spec / assumptions / open questions.
- Awkward proofs: question the relation before adding tactics or
  assumptions.

## Off-limits

- Honour the **forbidden** list. Do not edit `riscv-zkvm` to make a
  theorem hold.
- Do not weaken a statement to make it shippable without saying so
  in the file header and in `docs/PLAN.md`.
- Do not add a `Co-authored-by` trailer. Commits are the user's.
- Do not describe the pass as finished unless the top theorem exists
  and `docs/PLAN.md` names it.
