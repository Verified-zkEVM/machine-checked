# Ascent

**Shared by every layer of the [roadmap](../../ROADMAP.md).** Runs, correspondence and the
safety judgement for any machine, given only its step. Nothing here mentions an instruction set.

| file | contents |
| --- | --- |
| `Run.lean` | `steps f n s` (exactly `n` steps of a partial step function `f`) and `Reaches f Q s` (some run from `s` ends in a state satisfying `Q`), with the rules `step`, `steps`, `trans`, `mono` and `loop`. |
| `Corres.lean` | `Corres f SR P fa`: from a state related by `SR` to an abstract state satisfying `P`, the machine reaches a state related to `fa` of it. With `refl`, `weaken` and `seq`. |
| `Safe.lean` | `SafeN step accept G n P s` over a step relation whose outcomes are a state, a `trap` (safe) or `wrong` (unsafe): within `n` steps, along runs satisfying the guard `G`, nothing goes `wrong` and every accepting state gives `P`. With the structural and step rules, `loop`, `loop_measure` and `budget_induction`. A partial step function is a relation by `detStep`. |

These are the one notion of a run, and the one judgement, in the repository. `RiscV.SafeN` is
`Ascent.SafeN` at `detStep stepSp1` with `Accepted` as the accepting states. riscv-zkvm's machine is an instance
(`RiscV/Safe.lean`: `stepsSp1 := steps stepSp1`), and so is the low logical program
(`Lprog/Sem.lean`: `Isa.Reaches := Reaches (I.step body)`). A lift's transfer theorem carries
a `Reaches` at one level to a `Reaches` at the other (`RiscV/Lprog/Lift.lean`,
`reach_of_reaches`), so correspondences and runs proved high up hold of the machine.

Ported from catcrypt-compiler's ascent, which follows Sebastian Graf's
[ascent](https://github.com/sgraf812/ascent). [`PROVENANCE.md`](PROVENANCE.md) has the origin of
each file, and [`LICENSE-catcrypt`](LICENSE-catcrypt) the licence it came under.
