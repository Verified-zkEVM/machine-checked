# Provenance

Code in this directory is ported from
[catcrypt-compiler](https://github.com/spitters/catcrypt-compiler) at `master` `69ffea9f`,
with the permission of its maintainer. catcrypt-compiler is MIT-licensed; its licence is
reproduced in `../Ascent/LICENSE-catcrypt`.

| file | from | changes |
| --- | --- | --- |
| `Model.lean` | `SecureCompilation/ARMBackend/ArmModel.lean` | namespace `MachineChecked.ARM`; not a Lean `module`; its three nested machines (`AState`, `BState`, `BMState`) are one `State` with one instruction type `Inst`, the `W` forms acting on the low halves of the `X` registers; the loop and branch-label alphabets are not taken; its concrete `example`s are checked by `decide`, not `native_decide` |
| `Mem64.lean` | `SecureCompilation/MachineMem64.lean` | namespace `MachineChecked.ARM`; not a Lean `module` |

The model is **trusted** (`docs/ELF.md` §4): it is not yet proved against a canonical AArch64
specification.
