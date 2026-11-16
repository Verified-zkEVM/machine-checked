# Ascent

**Shared by every layer of the [roadmap](../../ROADMAP.md).** Runs, correspondence and the
safety judgement for any machine, given only its step. Nothing here mentions an instruction set.

| file | contents |
| --- | --- |
| `Run.lean` | `steps f n s` (exactly `n` steps of a partial step function `f`) and `Reaches f Q s` (some run from `s` ends in a state satisfying `Q`), with the rules `step`, `steps`, `trans`, `mono` and `loop`. |
| `Safe.lean` | `SafeN step accept G n Q s` over a step relation whose outcomes are a state, a `trap` (safe) or `wrong` (unsafe): within `n` steps, along runs satisfying the guard `G`, nothing goes `wrong` and every accepting state satisfies `Q`. `erase` forgets the events of a step relation that has them, and `silent` gives one that has none an empty list. With the structural and step rules, `loop`, `loop_measure`, `budget_induction`, and `of_reaches` (a run that reaches a state gives `SafeN` from where it started, on a deterministic machine). A partial step function is a relation by `detStep`. |
| `Refine.lean` | When two programs are the same to an observer. A `System` is a step relation with events and its accepting states; `Behaves` is the events a run makes and how it is seen to end (running, accepted, trapped, `wrong`). `Refines A a B b`: everything `A` shows, `B` shows, unless `B` can go `wrong` (undefined behaviour of the one refined). `Equivalent` is refinement both ways, and `Refines.of_sim` gives a refinement from a simulation. |
| `Corres.lean` | `Corres step accept SR P fa`, a correspondence as a contract: from a state related by `SR` to an abstract state satisfying `P`, every continuation that is safe from the states related to `fa` of it is safe from the start. With `refl`, `weaken`, `seq` and `of_reaches`. |

These are the one notion of a run, and the one judgement, in the repository. `RiscV.SafeN` is
`Ascent.SafeN` at `detStep stepSp1` with `Accepted` as the accepting states
(`RiscV/Safe.lean`), and the low logical program's is `Ascent.SafeN` at its step relation and
its context's accepting states (`Lprog/Sem.lean`: `Isa.SafeN`). A lift's transfer theorem
carries the judgement at one level to the other (`RiscV/Lprog/Transfer.lean`, `transfer`), so
contracts proved high up hold of the machine. Its equivalence theorem
(`RiscV/Lprog/Equiv.lean`) says the two levels show an observer the same, which is what a
decompiler and a compiler are judged by (`docs/design/Decompiler.md`).

Ported from catcrypt-compiler's ascent, which follows Sebastian Graf's
[ascent](https://github.com/sgraf812/ascent). [`PROVENANCE.md`](PROVENANCE.md) has the origin of
each file, and [`LICENSE-catcrypt`](LICENSE-catcrypt) the licence it came under.
