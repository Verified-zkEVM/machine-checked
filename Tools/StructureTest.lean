/-
  Tools.StructureTest

  Checks of `Logical.Structure` on small graphs, run when the module is built. A node that ends
  in a switch is never a two-way choice or a way out, whatever its number of successors: with
  two it was once taken for an `if`, with one its check was dropped, and with none it was
  taken for the end of the function.
-/

import MachineChecked.Logical.Structure

namespace Tools.StructureTest

open MachineChecked.Logical.Structure

/-- Does some part of `s` satisfy `p`? -/
def has (p : S → Bool) (s : S) : Bool :=
  p s || match s with
    | .seq a b | .ite _ a b | .arm _ _ a b => has p a || has p b
    | .block _ b | .loop _ b => has p b
    | _ => false

def isIte : S → Bool | .ite .. => true | _ => false
def isArm : S → Bool | .arm .. => true | _ => false
def isFail : S → Bool | .fail => true | _ => false
def isStop : S → Bool | .stop => true | _ => false

/-- The structure of `succs`, with the nodes `sw` ending in a switch. -/
def run (succs : Array (List Nat)) (sw : List Nat) : Option S :=
  «structure» succs (Array.ofFn fun (i : Fin succs.size) => sw.contains i.val)
    (Array.replicate succs.size 1) 24

-- a switch with two candidates is no `if`
#guard (run #[[1, 2], [], []] [0]).any fun s => has isArm s && !has isIte s
-- a branch with two successors is
#guard (run #[[1, 2], [], []] []).any fun s => has isIte s && !has isArm s
-- a switch with one candidate keeps its check, and goes nowhere if it fails
#guard (run #[[1], []] [0]).any fun s => has isArm s && has isFail s
-- a switch with none goes nowhere; it does not end the function
#guard (run #[[]] [0]).any fun s => has isFail s && !has isStop s
-- a switch with no candidates is no way out to copy where it is taken
#guard !(copied #[[1, 2], [3], [3], []] #[false, false, false, true] #[1, 1, 1, 1] 24)[3]!
#guard (copied #[[1, 2], [3], [3], []] #[false, false, false, false] #[1, 1, 1, 1] 24)[3]!

end Tools.StructureTest
