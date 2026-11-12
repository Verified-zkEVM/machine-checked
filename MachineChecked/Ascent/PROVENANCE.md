# Provenance

Code in this directory, except `Safe.lean`, is ported from
[catcrypt-compiler](https://github.com/spitters/catcrypt-compiler) at `master` `69ffea9f`,
with the permission of its maintainer, and has since been changed to fit MachineChecked.
catcrypt-compiler is MIT-licensed; its licence is reproduced in `LICENSE-catcrypt`.

| file | from | changes |
| --- | --- | --- |
| `Run.lean` | after `Ascent/CorresIsa.lean` (`CorresIsaRun`) | runs of any step function, with the number of steps chosen per state; written here |
| `Corres.lean` | `HaxAscent/Calculus/CorresMCore.lean`, `Ascent/CorresIsa.lean` | stated over `Reaches` instead of a fixed fuel; `CatCryptCore`'s relational refinement and `RefinesP`/`RefinesO` (`HaxAscent/Ascent/Refines.lean`) are not taken; `weaken` and `seq` added |
| `Safe.lean` | not ported | generalised from this repository's `RiscV/Safe.lean` |

catcrypt-compiler's Ascent follows Sebastian Graf's
[sgraf812/ascent](https://github.com/sgraf812/ascent).
