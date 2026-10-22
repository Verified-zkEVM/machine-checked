# Agent doctrine

Standing proof rules are in `CONTRIBUTING.md` (the Ground rules section). The
trust ladder is `docs/ELF.md` §4. The layers, and where the code stands, are in
`ROADMAP.md`. New proofs go through the lift (`MachineChecked/RiscV/Lprog`).

## Skills

| skill | owns | must not |
| --- | --- | --- |
| `/formal-verification` | the verification pass from the bytecode to the high-level spec (`SafeN` / `Iface.HoldsN` over `stepSp1`), with the account kept in the case plan (`Cases/<case>/PLAN.md`) | open a PR, merge, invent a second machine semantics |

`/work` and `/review-pr` are not imported. There is no attack skill.
A pass of an attack skill is not owed, and must not be claimed.
