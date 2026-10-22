# Ascent

**Shared by every layer of the [roadmap](../../ROADMAP.md).** Runs and correspondence for any
machine, given only its step function. Nothing here mentions an instruction set.

| file | contents |
| --- | --- |
| `Run.lean` | `steps f n s` (exactly `n` steps of a partial step function `f`) and `Reaches f Q s` (some run from `s` ends in a state satisfying `Q`), with the rules `step`, `steps`, `trans`, `mono` and `loop`. |
| `Corres.lean` | `Corres f SR P fa`: from a state related by `SR` to an abstract state satisfying `P`, the machine reaches a state related to `fa` of it. With `refl`, `weaken` and `seq`. |

These are the one notion of a run in the repository. riscv-zkvm's machine is an instance
(`RiscV/Safe.lean`: `stepsSp1 := steps stepSp1`), and so is the low logical program
(`Lprog/Sem.lean`: `Isa.Reaches := Reaches (I.step body)`). A lift's transfer theorem carries
a `Reaches` at one level to a `Reaches` at the other (`RiscV/Lprog/Lift.lean`,
`reach_of_reaches`), so correspondences and runs proved high up hold of the machine.

Ported from catcrypt-compiler's ascent, which follows Sebastian Graf's
[ascent](https://github.com/sgraf812/ascent). [`PROVENANCE.md`](PROVENANCE.md) has the origin of
each file, and [`LICENSE-catcrypt`](LICENSE-catcrypt) the licence it came under.
