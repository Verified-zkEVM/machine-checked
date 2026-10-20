# Provenance

Code in this directory is ported from
[catcrypt-compiler](https://github.com/spitters/catcrypt-compiler) at `master` `69ffea9f`,
with the permission of its maintainer, and has since been changed to fit MachineChecked.
catcrypt-compiler is MIT-licensed; its licence is reproduced in `LICENSE-catcrypt`.

| file | from | changes |
| --- | --- | --- |
| `Refines.lean` | `HaxAscent/Ascent/Refines.lean` | namespace `MachineChecked.Ascent`; not a Lean `module` |
| `Corres.lean` | `HaxAscent/Calculus/CorresMCore.lean`, `HaxAscent/Calculus/CorresGenericSpec.lean` | the `CatCryptCore` relational-refinement link is dropped; `CorresM.weaken`, `CorresM.congr`, `CorresM.seq` added |

catcrypt-compiler's Ascent follows Sebastian Graf's
[sgraf812/ascent](https://github.com/sgraf812/ascent).
