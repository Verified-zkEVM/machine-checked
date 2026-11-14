/-
  MachineChecked.Logical.Structure

  From a control-flow graph to structured control flow: sequences, two-way choices, blocks one
  leaves and loops one repeats.

  The method is Ramsey's ("Beyond Relooper", ICFP 2022), which follows the dominator tree. A
  node is placed inside the node that dominates it immediately. A node that only one forward
  edge reaches goes where that edge is; a node that several reach (a merge node) goes after a
  `block` that holds the code that jumps to it, so that a jump to it is leaving the block. A
  node that a backward edge reaches is the head of a `loop`, and that edge is starting the
  loop again. It works exactly on the reducible graphs (every backward edge goes to a node
  that dominates its source); for any other, `structure` gives `none`.

  Nothing here knows what a node does. A node is a number, the graph gives each node's
  successors in order, and the result says where each node goes (`S`). Nothing is proved of
  it yet.

  ## Main definitions

  * `S`, `structure`
  * `S.fallsThrough`, `S.simp`
-/

namespace MachineChecked.Logical.Structure

/-- Structured control flow over the nodes of a graph. -/
inductive S where
  | nil
  | seq (a b : S)
  /-- The code of node `n`, without the jump that ends it. -/
  | node (n : Nat)
  /-- Nothing follows: the node before it ends the function. -/
  | stop
  /-- The end of node `n`, which has two successors: what follows the first, and the second. -/
  | ite (n : Nat) (t e : S)
  /-- The end of node `n`, which has several: `t` follows its successor `k`, `e` the later
      ones. -/
  | arm (n k : Nat) (t e : S)
  /-- No successor is left: the node goes nowhere it may. -/
  | fail
  /-- `exit l` inside leaves it. -/
  | block (l : Nat) (body : S)
  /-- `again l` inside starts it again; running off its end leaves it, and so does
      `leave` directly inside it. -/
  | loop (l : Nat) (body : S)
  | exit (l : Nat)
  | again (l : Nat)
  | leave
  deriving Repr, Inhabited

namespace S

/-- May control run off the end? -/
def fallsThrough : S → Bool
  | nil | node _ => true
  | seq a b => a.fallsThrough && b.fallsThrough
  | stop | fail | exit _ | again _ | leave => false
  | ite _ t e | arm _ _ t e => t.fallsThrough || e.fallsThrough
  | block l b => b.fallsThrough || hasExit l b
  | loop _ b => b.fallsThrough || hasLeave b
where
  /-- Does it leave block `l`? -/
  hasExit (l : Nat) : S → Bool
    | seq a b => hasExit l a || hasExit l b
    | ite _ t e | arm _ _ t e => hasExit l t || hasExit l e
    | block _ b | loop _ b => hasExit l b
    | exit l' => l' == l
    | _ => false
  /-- Does it leave the loop it is directly inside? -/
  hasLeave : S → Bool
    | seq a b => hasLeave a || hasLeave b
    | ite _ t e | arm _ _ t e => hasLeave t || hasLeave e
    | leave => true
    | _ => false

/-- `exit l` as `exit l'`, everywhere. -/
def rename (l l' : Nat) : S → S
  | seq a b => seq (rename l l' a) (rename l l' b)
  | ite n t e => ite n (rename l l' t) (rename l l' e)
  | arm n k t e => arm n k (rename l l' t) (rename l l' e)
  | block m b => block m (rename l l' b)
  | loop m b => loop m (rename l l' b)
  | exit m => exit (if m = l then l' else m)
  | s => s

/-- Where block `l` ends in another block, leaving `l` is leaving that one. -/
def intoLast (l : Nat) : S → S
  | seq a b => seq a (intoLast l b)
  | ite n t e => ite n (intoLast l t) (intoLast l e)
  | arm n k t e => arm n k (intoLast l t) (intoLast l e)
  | block m b => block m (rename l m b)
  | s => s

/-- `exit l` as `leave`, in a loop's body but not inside what is nested in it. -/
def toLeave (l : Nat) : S → S
  | seq a b => seq (toLeave l a) (toLeave l b)
  | ite n t e => ite n (toLeave l t) (toLeave l e)
  | arm n k t e => arm n k (toLeave l t) (toLeave l e)
  | exit m => if m = l then leave else exit m
  | s => s

/-- Without the `exit l` that control would do anyway by running off the end of block `l`;
    where the block ends in a loop, leaving the block from it is leaving the loop. -/
def dropExit (l : Nat) : S → S
  | seq a b => seq a (dropExit l b)
  | ite n t e => ite n (dropExit l t) (dropExit l e)
  | arm n k t e => arm n k (dropExit l t) (dropExit l e)
  | loop m b => loop m (toLeave l b)
  | exit l' => if l' = l then nil else exit l'
  | s => s

/-- The body of loop `l`, where running off the end repeats: an `again l` at the end is
    dropped, and where control ran off the end it now leaves. -/
def loopBody (l : Nat) : S → S
  | seq a b => seq a (loopBody l b)
  | ite n t e => ite n (loopBody l t) (loopBody l e)
  | arm n k t e => arm n k (loopBody l t) (loopBody l e)
  | again l' => if l' = l then nil else again l'
  | s => if s.fallsThrough then seq s leave else s

/-- How many constructors. -/
def size : S → Nat
  | seq a b | ite _ a b | arm _ _ a b => a.size + b.size + 1
  | block _ b | loop _ b => b.size + 1
  | _ => 1

/-- Blocks nothing leaves but by running off the end are no blocks, and a loop's body is
    one where running off the end repeats (`loopBody`). -/
def simpN : Nat → S → S
  | 0, s => s
  | fuel + 1, seq a b => seq (simpN fuel a) (simpN fuel b)
  | fuel + 1, ite n t e => ite n (simpN fuel t) (simpN fuel e)
  | fuel + 1, arm n k t e => arm n k (simpN fuel t) (simpN fuel e)
  | fuel + 1, block l b =>
    let b' := dropExit l (simpN fuel (intoLast l b))
    if fallsThrough.hasExit l b' then block l b' else b'
  | fuel + 1, loop l b => loop l (loopBody l (simpN fuel b))
  | _, s => s

def simp (s : S) : S := simpN s.size s

end S

/-! ## The graph -/

/-- What the method needs of a graph: for each node its number in reverse postorder (0 for
    the entry; `none` if nothing reaches it), its immediate dominator, the merge nodes it
    dominates immediately (latest first), and whether it is a merge node or the head of a
    loop. -/
structure Info where
  succs : Array (List Nat)
  rpo : Array (Option Nat)
  kids : Array (List Nat)
  isMerge : Array Bool
  isLoop : Array Bool

/-- The nodes in postorder, from node 0. -/
def postorder (succs : Array (List Nat)) : Array Nat := Id.run do
  let n := succs.size
  if n = 0 then return #[]
  let mut seen := Array.replicate n false
  let mut out : Array Nat := #[]
  -- a node, and its successors yet to visit
  let mut stack : Array (Nat × List Nat) := #[(0, succs[0]!)]
  seen := seen.set! 0 true
  let edges := succs.foldl (fun k l => k + l.length) 0
  for _ in [0 : 2 * (n + edges) + 2] do
    match stack.back? with
    | none => break
    | some (x, []) =>
      out := out.push x
      stack := stack.pop
    | some (x, y :: ys) =>
      stack := stack.pop.push (x, ys)
      if y < n && !seen[y]! then
        seen := seen.set! y true
        stack := stack.push (y, succs[y]!)
  return out

/-- The analysis of a graph, or `none` if it is not reducible. -/
def analyse (succs : Array (List Nat)) : Option Info := Id.run do
  let n := succs.size
  let post := postorder succs
  let m := post.size
  let mut rpo : Array (Option Nat) := Array.replicate n none
  for i in [0 : m] do
    rpo := rpo.set! post[i]! (some (m - 1 - i))
  let num (x : Nat) : Nat := (rpo[x]!).getD n
  let order := post.reverse
  let mut preds : Array (List Nat) := Array.replicate n []
  for x in order do
    for y in succs[x]! do
      if y < n then preds := preds.set! y (x :: preds[y]!)
  -- immediate dominators, by Cooper, Harvey and Kennedy's iteration
  let mut idom : Array (Option Nat) := Array.replicate n none
  idom := idom.set! 0 (some 0)
  for _ in [0 : n + 2] do
    let mut changed := false
    for x in order do
      if x = 0 then continue
      let mut new : Option Nat := none
      for p in preds[x]! do
        if idom[p]!.isNone then continue
        match new with
        | none => new := some p
        | some q =>
          -- the nearest common dominator of `p` and `q`
          let mut a := p
          let mut b := q
          for _ in [0 : 2 * n + 2] do
            if a = b then break
            if num a > num b then a := (idom[a]!).getD 0
            else b := (idom[b]!).getD 0
          new := some a
      if new != idom[x]! then
        idom := idom.set! x new
        changed := true
    if !changed then break
  let dominates (d x : Nat) : Bool := Id.run do
    let mut a := x
    for _ in [0 : n + 1] do
      if a = d then return true
      if a = 0 then return false
      a := (idom[a]!).getD 0
    return false
  let mut isMerge := Array.replicate n false
  let mut isLoop := Array.replicate n false
  let mut forwardIn := Array.replicate n 0
  for x in order do
    for y in succs[x]! do
      if y ≥ n then return none
      if num y ≤ num x then
        if !dominates y x then return none
        isLoop := isLoop.set! y true
      else forwardIn := forwardIn.set! y (forwardIn[y]! + 1)
  for x in order do
    if forwardIn[x]! ≥ 2 then isMerge := isMerge.set! x true
  let mut kids : Array (List Nat) := Array.replicate n []
  -- in reverse postorder, so that each list ends up latest first
  for x in order do
    if x ≠ 0 && isMerge[x]! then
      let d := (idom[x]!).getD 0
      kids := kids.set! d (x :: kids[d]!)
  return some { succs, rpo, kids, isMerge, isLoop }

namespace Info

variable (g : Info)

mutual

/-- Node `x` and all it dominates. -/
def tree : Nat → Nat → Option S
  | 0, _ => none
  | fuel + 1, x => do
    let body ← within fuel x g.kids[x]!
    some (if g.isLoop[x]! then .loop x body else body)

/-- Node `x` inside the blocks of the merge nodes `ys`, each followed by its node. -/
def within : Nat → Nat → List Nat → Option S
  | 0, _, _ => none
  | fuel + 1, x, y :: ys => do
    some (.seq (.block y (← within fuel x ys)) (← tree fuel y))
  | fuel + 1, x, [] => do
    match g.succs[x]! with
    | [] => some (.seq (.node x) .stop)
    | [a] => some (.seq (.node x) (← branch fuel x a))
    | [a, b] => some (.seq (.node x) (.ite x (← branch fuel x a) (← branch fuel x b)))
    | ss => some (.seq (.node x) (← arms fuel x 0 ss))

/-- The successors of `x` from the `k`th on. -/
def arms : Nat → Nat → Nat → List Nat → Option S
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => some .fail
  | fuel + 1, x, k, a :: rest => do
    some (.arm x k (← branch fuel x a) (← arms fuel x (k + 1) rest))

/-- The edge from `x` to `y`. -/
def branch : Nat → Nat → Nat → Option S
  | 0, _, _ => none
  | fuel + 1, x, y =>
    if (g.rpo[y]!).getD 0 ≤ (g.rpo[x]!).getD 0 then some (.again y)
    else if g.isMerge[y]! then some (.exit y)
    else tree fuel y

end

end Info

/-- **The structure of a graph**: node 0 is the entry, and `succs` gives each node's
    successors in order. `none` if the graph is not reducible. -/
def «structure» (succs : Array (List Nat)) : Option S := do
  let g ← analyse succs
  let edges := succs.foldl (fun k l => k + l.length) 0
  (← g.tree (4 * (succs.size + edges) + 8) 0).simp

end MachineChecked.Logical.Structure
