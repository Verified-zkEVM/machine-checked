# Building what `decompile --to lean` writes

`compile.sh` builds the modules that `decompile --to lean` writes
([`Tools/README.md`](../../Tools/README.md), "As Lean") one by one, several in parallel, and
times each. The build times in `Tools/README.md` were measured with it.

```sh
lake build decompile
.lake/build/bin/decompile --to lean --proved path/to/guest.elf /tmp/emit Guest
scripts/lean-emit/compile.sh /tmp/emit Guest 8     # OUT NS [JOBS], default 8 jobs
```

It builds the data module first (`Words` for `--proved`, `Code` otherwise), then the `F<i>` and
`Pancake` modules in parallel, and prints the five slowest, how many of those failed, and the
sum of their times (not wall time; the data module is not counted). Logs go to `OUT/log/`.
`NS` must be a single component, and the root module `OUT/NS.lean` is not built.

- It runs `lean` from the repository root, so the ELF path in `Words.lean` or `Code.lean` is
  resolved from there.
- `OUT` must be outside the repository's module tree; `compile.sh` passes it to `lean` as the
  root.
- A project that requires this repository should build the modules with `lake build` instead.
