# Exec

Hand proofs of interfaces, a layer-0 proof tool (see [`../README.md`](../README.md)).

Some functions are beyond the contract checker ([`../Check`](../Check/README.md)): loops over
memory, the allocator, the panic runtime. Their interfaces are proved by hand against the same
`Iface.HoldsN`, so they enter the same contract table and compose with checked functions
through `table_sound`.

| file | contents |
| --- | --- |
| `Basic.lean` | Stepping lemmas for proving an interface by hand. |
| `Tactic.lean` | `xstep`: execute the instruction at the current state of a `SafeN` goal. |
| `Hint.lean` | SP1's input path: exactly what `HINT_LEN` and `HINT_READ` do. |
| `Arith.lean` | Word facts hand proofs often need: store footprints, and the bit tests compilers use on lengths. |
