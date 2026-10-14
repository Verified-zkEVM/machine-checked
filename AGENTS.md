# Agent doctrine

Standing proof rules are in `docs/PLAN.md` (the Rules section). The
trust ladder is `docs/ELF.md` §4.

## Skills

| skill | owns | must not |
| --- | --- | --- |
| `/formal-verification` | the verification pass from the bytecode to the high-level spec (`SafeN` / `Iface.HoldsN` over `stepSp1`), with the account kept in `docs/PLAN.md` | open a PR, merge, invent a second machine semantics |

`/work` and `/review-pr` are not imported. There is no attack skill.
A pass of an attack skill is not owed, and must not be claimed.
