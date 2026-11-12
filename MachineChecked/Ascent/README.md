# Ascent

**Shared by every layer of the [roadmap](../../ROADMAP.md).** Runs, correspondence and the
safety judgement for any machine, given only its step. Nothing here mentions an instruction set.

| file | contents |
| --- | --- |
| `Run.lean` | `steps f n s` (exactly `n` steps of a partial step function `f`) and `Reaches f Q s` (some run from `s` ends in a state satisfying `Q`), with the rules `step`, `steps`, `trans`, `mono` and `loop`. |
| `Safe.lean` | `SafeN step accept G n Q s` over a step relation whose outcomes are a state, a `trap` (safe) or `wrong` (unsafe): within `n` steps, along runs satisfying the guard `G`, nothing goes `wrong` and every accepting state satisfies `Q`. With the structural and step rules, `loop`, `loop_measure`, `budget_induction`, and `of_reaches` (a run that reaches a state gives `SafeN` from where it started, on a deterministic machine). A partial step function is a relation by `detStep`. |
| `Corres.lean` | `Corres step accept SR P fa`, a correspondence as a contract: from a state related by `SR` to an abstract state satisfying `P`, every continuation that is safe from the states related to `fa` of it is safe from the start. With `refl`, `weaken`, `seq` and `of_reaches`. |

These are the one notion of a run, and the one judgement, in the repository. `RiscV.SafeN` is
`Ascent.SafeN` at `detStep stepSp1` with `Accepted` as the accepting states
(`RiscV/Safe.lean`), and the low logical program's is `Ascent.SafeN` at its step relation and
its context's accepting states (`Lprog/Sem.lean`: `Isa.SafeN`). A lift's transfer theorem
carries the judgement at one level to the other (`RiscV/Lprog/Transfer.lean`, `transfer`), so
contracts proved high up hold of the machine.

Ported from catcrypt-compiler's ascent, which follows Sebastian Graf's
[ascent](https://github.com/sgraf812/ascent). [`PROVENANCE.md`](PROVENANCE.md) has the origin of
each file, and [`LICENSE-catcrypt`](LICENSE-catcrypt) the licence it came under.
