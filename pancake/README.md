# pancake

A Lake package of this repository: **Pancake as the decompiler writes it**, over Flapjack's
syntax (`Flapjack.Pancake.PanLang`). See [`docs/design/Packages.md`](../docs/design/Packages.md).

| module | namespace | what |
| --- | --- | --- |
| `Pancake.Basic` | `Pancake` | the word (`W`) and a program (`Program`, a list of Flapjack's declarations) |
| `Pancake.Env` | `Pancake` | what a decompiled program assumes of its environment: it starts at `main`, ends by raising `halt`, gives up by the foreign call `trap`, makes a system call by `syscall` (bare) or `ecall` (SP1), and finds a call's results at `scratch`. Lift 2 writes its programs with these. |
| `Pancake.Print` | `Pancake` | a program as the source text Flapjack reads (`print`): Flapjack has a parser and no printer |

`import Pancake` imports all of it.

**No semantics yet.** Running a program is Flapjack's interpreter
(`Flapjack.evalPanValueProgram`), but Flapjack's semantics does not build on this repository's
Lean version (v4.36) at the commit it pins (on Flapjack's branch `lean-v4.36-frontend`, which
ports its syntax only). When it does, this package gets `run` (the interpreter from `main`,
with the environment's foreign calls) and lemmas for reasoning about decompiled programs.

## Requiring it

It requires Flapjack, at the commit this repository pins, and so Flapjack's own requirements
(Mathlib, ZirenDet). From another Lake project, on the same Lean version as this repository:

```toml
[[require]]
name = "pancake"
git = "https://github.com/Verified-zkEVM/machine-checked"
rev = "<commit>"
subDir = "pancake"
```

A program `decompile --to lean --pancake` writes is of type `Pancake.Program`, and its theorem
relates it to lift 2 in the root package.
