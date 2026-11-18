# Ascent

Runs, the safety judgement, refinement and correspondence for any machine, given only its
step. Shared by every layer of the [roadmap](../../../ROADMAP.md); nothing here mentions an
instruction set. Package [`lprog`](../../README.md), namespace `Lprog.Ascent`.

| file | contents |
| --- | --- |
| `Run.lean` | `steps f n s` (exactly `n` steps of a partial step function `f`) and `Reaches f Q s` (some run from `s` ends in a state satisfying `Q`), with the rules `step`, `steps`, `trans`, `mono` and `loop`. |
| `Safe.lean` | `SafeN step accept G n Q s`, over a step relation whose outcomes are a state, `trap` (safe) or `wrong` (unsafe): within `n` steps, along runs satisfying the guard `G`, nothing goes `wrong` and every accepting state satisfies `Q`. `erase` forgets the events of a step relation that has them; `silent` gives an event-free relation an empty event list. Structural and step rules, plus `loop`, `loop_measure`, `budget_induction`, and `of_reaches` (on a deterministic machine, a run reaching a state gives `SafeN` from its start). `detStep` turns a partial step function into a relation. |
| `Refine.lean` | When two programs look the same to an observer. A `System` is a step relation with events plus its accepting states. `Behaves` is the events a run produces and how it ends (running, accepted, trapped, `wrong`). `Refines A a B b`: everything `A` shows, `B` shows, unless `B` can go `wrong` (undefined behaviour in the refined program). `Equivalent` is refinement both ways; `Refines.of_sim` builds a refinement from a simulation. |
| `Corres.lean` | `Corres step accept SR P fa`, a correspondence stated as a contract: from a state related by `SR` to an abstract state satisfying `P`, every continuation that is safe from the states related to its image under `fa` is safe from the start. Rules `refl`, `weaken`, `seq`, `of_reaches`. |

## How the layers use it

These are the only notion of a run and the only judgement in the repository:

- `MachineChecked.RiscV.SafeN` is `Ascent.SafeN` at `detStep stepSp1`, with `Accepted` as the accepting
  states (`MachineChecked/RiscV/Safe.lean`).
- Lprog's `Isa.SafeN` is `Ascent.SafeN` at its step relation and its context's accepting
  states (`Lprog/Sem.lean`).
- A lift's transfer theorem carries the judgement from one level to the other
  (`MachineChecked/RiscV/Lift/Transfer.lean`, `transfer`), so contracts proved at Lprog hold
  of the machine.
- A lift's equivalence theorem (`MachineChecked/RiscV/Lift/Equiv.lean`) says the two levels
  look the same to an observer, which is the standard a decompiler and a compiler are judged
  by ([`docs/design/Decompiler.md`](../../../docs/design/Decompiler.md)).

## Provenance

`Run.lean` and `Corres.lean` are ported from catcrypt-compiler's Ascent, which follows
Sebastian Graf's [ascent](https://github.com/sgraf812/ascent); `Safe.lean` is not.
[`PROVENANCE.md`](PROVENANCE.md) gives the origin of each file, and
[`LICENSE-catcrypt`](LICENSE-catcrypt) the licence.
