# Provenance

Code in this directory is ported from
[catcrypt-compiler](https://github.com/spitters/catcrypt-compiler) at `master` `69ffea9f`,
with the permission of its maintainer. catcrypt-compiler is MIT-licensed; its licence is
reproduced in `../Ascent/LICENSE-catcrypt`.

| file | from | changes |
| --- | --- | --- |
| `BinOp.lean` | `shiftMask` from `SecureCompilation/VIR/Core.lean`, `JasminBinOp` from `SecureCompilation/VIR/JasminDialect.lean` | only these two, so the VIR layer (and its Mathlib import) is not taken |
| `Model.lean` | `SecureCompilation/X86Backend/Model.lean` | namespace `MachineChecked.X86`; not a Lean `module` |
| `JasminModel.lean` | `SecureCompilation/X86Backend/JasminModel.lean` | namespace `MachineChecked.X86.Jasmin`; not a Lean `module` |

The model is **trusted** (`docs/ELF.md` §4): it is not yet proved against a canonical x86-64
specification.
