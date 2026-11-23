# Design note: the lift of one function

How a function's lift is stated apart from the program it sits in, and what that is for. This
covers three pull requests; the first states the lift and the theorems below.

## Goal

A client of `decompile --to lean --proved` proves `(liftProg fns)[i]? = some f` for each
function. The statement names the whole program, so every such module imports every
function's words and is rebuilt when any word changes. The lift of a function reads the rest
of the program in two places only: the function at each address it calls, and the list of all
functions for a computed jump it cannot resolve. Stating the lift over those two inputs lets a
module check one function from its own words and a few entry facts, and is the base for terms
that do not mention addresses and for caching by content.

## Definitions and theorems

- `liftFn entry all f` (`MachineChecked/RiscV/Lift/Lift.lean`): the lift of `f` given
  `entry : Word → Option Nat` and `all : List Nat`, the names `Lprog.Linked.Cx` uses in the
  lift of linked programs. `liftProg fs` is `fs.map (liftFn (entryOf fs) (List.range
  fs.length))`: there is one lift.
- `Fn.targets f`: the addresses at which the lift of `f` applies `entry`.
- `liftFn_congr`: resolvers that agree on `f.targets` give the same lift.
- `getElem?_liftProg_of_targets`: function `i` of `liftProg fs` is `liftFn entry (List.range
  fs.length) fs[i]` for any `entry` that agrees with `entryOf fs` on its targets.

A client then checks a function in two parts. A module that knows only the function's words,
its base and a table of its callees proves `liftFn (lookup tbl) (List.range n) fn = f` by
`kernel_eq`. A module that knows the program proves `fns[i]? = some fn` and that `entryOf fns`
agrees with the table on `fn.targets`, and `getElem?_liftProg_of_targets` joins the two.

Next: `decompile --to lean --proved` writing one words module per function and checking each
function against a local table (`Tools/ToLean.lean`); then terms over a base and a resolver,
checked by `fun entry base => Eq.refl _`, which name callees by symbol.

## Trusted

Nothing new. Tables and target lists are written by tools and checked by the kernel through
the theorem above.

## Open choices

- Take `Lprog.Linked.Cx` itself in place of the two arguments, toward one notion of context
  for the proved lift and the lift of linked programs. Its `label`, `cands` and `abort` have
  no use in `liftProg` today.
- Free `all` for a function with no unresolved computed jump, so that a function's check does
  not mention the number of functions.
- Whether `entryOf` should stay a linear search. Lookups cost the kernel a comparison per
  function; a client's local table avoids it.
- How many functions a written module holds. The cost of a written module is mostly its
  imports, so one module per function is the dearest layout.
