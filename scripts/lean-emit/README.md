# Building what `decompile --to lean` writes

`compile.sh` builds the modules `decompile --to lean` writes (`Tools/README.md`, "As Lean")
one by one, several at a time, and times each: how the numbers there were measured.

```sh
lake build decompile
.lake/build/bin/decompile --to lean --proved path/to/guest.elf /tmp/emit Guest
scripts/lean-emit/compile.sh /tmp/emit Guest 8     # builds each module, timing it
```

It runs `lean` from the repository's root, so the ELF's path in `Guest/Words.lean` is read from
there. `OUT` must be outside the repository's module tree; `compile.sh` passes it to `lean` as
the root. A project that requires this repository builds the modules with `lake build` instead.

The modules were first written by a prototype here (`Gen.lean`), for the experiment of
`docs/design/Packages.md` §2; the tool replaced it.
