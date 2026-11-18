# pancake

A Lake package of this repository containing **Pancake as the decompiler writes it**, over
Flapjack's syntax (`Flapjack.Pancake.PanLang`). See
[`docs/design/Packages.md`](../docs/design/Packages.md).

| module | namespace | contents |
| --- | --- | --- |
| `Pancake.Basic` | `Pancake` | The word type (`W`) and a program (`Program`, a list of Flapjack declarations). |
| `Pancake.Env` | `Pancake` | What a decompiled program assumes of its environment: it starts at `main`, ends by raising `halt`, gives up via the foreign call `trap`, makes system calls via `syscall` (bare) or `ecall` (SP1), and finds a call's results at `scratch`. Lift 2 writes its programs with these. |
| `Pancake.Print` | `Pancake` | A program as the source text Flapjack reads (`print`). Flapjack has a parser but no printer. |

`import Pancake` imports everything. A program written by `decompile --to lean --pancake` has
type `Pancake.Program`, and its theorem relates it to lift 2 in the root package
([`MachineChecked/Logical`](../MachineChecked/Logical/README.md)).

## No semantics yet

Running a program means Flapjack's interpreter (`Flapjack.evalPanValueProgram`). Flapjack's
semantics does not build on this repository's Lean version (v4.36) at the pinned commit, which
is on Flapjack's branch `lean-v4.36-frontend` and ports only the syntax. Once it builds, this
package will get `run` (the interpreter from `main`, with the environment's foreign calls) and
lemmas for reasoning about decompiled programs.

## Requiring it

It requires Flapjack at the commit this repository pins, and therefore Flapjack's own
requirements (Mathlib, ZirenDet). From another Lake project on the same Lean version as this
repository:

```toml
[[require]]
name = "pancake"
git = "https://github.com/Verified-zkEVM/machine-checked"
rev = "<commit>"
subDir = "pancake"
```
