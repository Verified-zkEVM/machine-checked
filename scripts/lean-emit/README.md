# Emitting the lift as Lean (experiment, 2026-11-16)

The experiment of [`docs/design/Packages.md`](../../docs/design/Packages.md) §2: the
`--proved` lift of an ELF written as Lean modules, with a theorem per function that its term
is `liftFn` of the ELF's words, checked by the kernel (`decide +kernel`). A prototype of
`decompile --to lean`, not the tool.

```sh
lake build Tools.Decompile
ELF=path/to/guest.elf OUT=/tmp/emit NS=Guest lake env lean scripts/lean-emit/Gen.lean
scripts/lean-emit/compile.sh /tmp/emit Guest 8     # builds each module, timing it
```

`OUT` must be outside the repository's module tree; `compile.sh` passes it to `lean` as the
root. The results, and what the emitter has to do for large programs, are in the design note.
