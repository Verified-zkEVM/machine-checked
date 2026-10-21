# Exec

Hand proofs of interfaces. Some functions are out of the checker's reach: loops over memory,
the allocator, the panic runtime. Their interfaces are proved here, against the same
`Iface.HoldsN` as the checker's, so they enter the same contract table and compose with the
checked functions through `table_sound`.

| file | contents |
| --- | --- |
| `Basic.lean` | Stepping lemmas for proving an interface by hand. |
| `Tactic.lean` | `xstep`: execute the instruction at the current state of a `SafeN` goal. |
| `Hint.lean` | SP1's input path exactly: what `HINT_LEN` and `HINT_READ` do. |
| `Arith.lean` | Word facts hand proofs keep needing: store footprints, and the bit tests compilers use on lengths. |
