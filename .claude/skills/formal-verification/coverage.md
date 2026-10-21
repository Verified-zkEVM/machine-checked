# Coverage hygiene

The case plan (`Cases/<case>/PLAN.md`) is the account of what the verification pass has proved.
Chat is not that account.

Bindings live in [SKILL.md](SKILL.md). Update the case plan in place.
Do not create a second matrix, and do not invent a regenerator.

## Artifacts

| role | where |
| --- | --- |
| What the pass has proved | the case plan |
| Disagreements between the bytecode and the spec | the case plan (history: `docs/ELF.md` §1) |
| Domain hypotheses | the theorem, noted in the case plan |
| Standing trust | `CONTRIBUTING.md` § Ground rules and `docs/ELF.md` §4 |

## After the theorems change

1. Update the case plan in place. A new disagreement or a new domain
   hypothesis goes in that file too.
2. There is no derived coverage artifact. Do not generate one, and
   do not hand-edit modules under `Cases/*/Image/`.
3. Do not invent progress in chat that is not in the case plan.

## What a note may claim

| status | means |
| --- | --- |
| `unstated` | no theorem yet |
| `stated` | the theorem exists; it may cite lemmas still open |
| `return-only` | the return path only — not the finished claim |
| `proved` | the loaded bytecode meets the spec: every reachable accepting path, noreturn paths never accept, hypotheses met by the real run |
| `n/a` | out of scope, with a reason |

A note may name a theorem that does not exist yet only while the
status is `unstated`. Once it says `proved`, the named theorem has
to be the one that does the work.

## Theorem links

When the case plan names a theorem, the name has to be the `theorem`
or `def` that exists after the build. Take it from a search after
`lake build`, not from memory.

Do not call the pass proved in chat or in the case plan unless that
theorem exists. The top theorem is the one that starts from the loaded
image and ends at the spec.

## Ledger audit

Two directions, before calling the pass proved:

- *Backward — invalidation*: each disagreement in `docs/ELF.md` §1 or
  the case plan that the claim covers needs a named discharging
  theorem. A covered disagreement with no theorem is an overclaim.
- *Forward — maintenance*: if the pass changes what a note covers
  (a new function under an existing gap, a hypothesis narrowed), update
  the note. A new hypothesis that restricts the theorem's domain
  belongs in the case plan.

Check drift both ways. An understated note misdirects the next reading
as surely as an overstated one hides risk.

## Negative claims

"`X` does not exist" needs a search whose root can contain `X`.
Confirm the name is in this image or in `riscv-zkvm`, not a sibling
package. A guard that shares the search is not independent evidence.
See [SKILL.md](SKILL.md) (Assumptions).

## Before stopping

- [ ] the case plan matches the theorems
- [ ] Disagreements and new domain hypotheses are written there
- [ ] Nothing is claimed beyond that file and the top theorem
- [ ] Generated image modules were not edited
