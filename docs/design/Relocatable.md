# Design note: the lift of one function

How a function's lift is stated apart from the program it sits in.

## Goal

A client of `decompile --to lean --proved` proves `(liftProg fns)[i]? = some f` for each
function. The statement names the whole program, so every such module imports every
function's words and is rebuilt when any word changes. The lift of a function reads the rest
of the program in two places only: the function at each address it calls, and the list of all
functions for a computed jump it cannot resolve. Stating the lift over those two inputs lets a
module check one function from its own words and a few entry facts.

## Definitions and theorems

- `liftFn entry all f` (`MachineChecked/RiscV/Lift/Lift.lean`): the lift of `f` given
  `entry : Word → Option Nat` and `all : List Nat`, the names `Lprog.Linked.Cx` uses in the
  lift of linked programs. `liftProg fs` is `fs.map (liftFn (entryOf fs) (List.range
  fs.length))`: there is one lift.
- `Fn.callTargets f`: the addresses at which the lift of `f` applies `entry`, one per call
  site.
- `liftFn_congr`: resolvers that agree on `f.callTargets` give the same lift.
- `getElem?_liftProg_of_callTargets`: function `i` of `liftProg fs` is `liftFn entry
  (List.range fs.length) fs[i]` for any `entry` that agrees with `entryOf fs` on its call
  targets.

A client checks a function in two parts. A module that knows only the function's words, its
base and a table `tbl` of its callees proves `liftFn tbl (List.range n) fn = f` by `kernel_eq`.
A module that knows the program proves `fns[i]? = some fn` and
`fn.callTargets.map (entryOf fns) = fn.callTargets.map tbl` (by `kernel_eq`; deciding the
`∀ a ∈` form is much slower in the kernel), and `getElem?_liftProg_of_callTargets` with
`List.map_inj_left.mp` joins the two.

## Trusted

Nothing new. Tables and call-target lists are written by tools and checked by the kernel
through the theorem above.

## Open choices

- Take `Lprog.Linked.Cx` itself in place of the two arguments, toward one notion of context
  for the proved lift and the lift of linked programs. Its `label`, `cands` and `abort` have
  no use in `liftProg` today.
- Free `all` for a function with no unresolved computed jump, so that a function's check does
  not mention the number of functions.

## Possible follow-ups

Not agreed; separate pull requests, only if wanted. The emitter writes one words module per
function, optionally several functions per module; then terms that take the base and the
resolver as variables, so a function's term survives relinking.
