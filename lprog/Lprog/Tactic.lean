/-
  Lprog.Tactic

  `lsym`: symbolic execution of an Lprog function body, for any instruction set. A first form
  (`docs/design/Automation.md`, item 1).

  The goal is `I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩`; `lsym hf` takes
  `hf : p[fn]? = some fd` and steps the body of `fd` from `pc`:

  * a label is stepped over;
  * an operation is stepped with its result computed by `simp` (the simp set `lsym_simp` and
    the lemmas given) and substituted. A load's or a store's check, behind the instruction
    set's memory, is closed by `simp` if it can; if not, it stays as the hypothesis `hm` of
    what follows, and the result is computed all the same. It is no goal: an operation whose
    check fails traps, and the run stops safely;
  * a `goto` goes to its label;
  * an `Lcond` splits: one goal for each outcome, with the condition's value as the hypothesis
    `hc`, simplified;
  * a return leaves the goals that the link register and the stack pointer are as the call
    left them, and the goal after it;
  * a call or a tail call, with `using [specs]`, applies the first specification that fits and
    steps on after the return, with the postcondition as `hret`.

  It stops where it can do nothing: at a call without a specification, an external call, or a
  loop's head, which a proof meets with the function's specification or an invariant. A loop
  is found without `stop`: a path that comes back to a program counter it has stepped from is
  left there. A step that runs out of recursion depth or heartbeats leaves its goal too.
  `set_option trace.lsym true` says, for each goal left, why. The
  instruction at `pc` is found by `rfl`, so the body should be a literal (`decompile --to
  lean` writes one, `f<i>`); a body to be computed is computed again at each step. `lsym`
  keeps program counters literals, and allows the depth a lookup in a body of a few hundred
  entries needs.

  ## Main results

  * `SafeN.opn'`, `SafeN.cond'`, `SafeN.tail'`: the rules in the form a tactic applies
  * `lstep`, `lsym`
-/

import Lean
import Lprog.Block
import Lprog.Contract
import Lprog.LsymAttr
import Lprog.Op

namespace Lprog

namespace SafeN

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {G : State I → Prop} {n : Nat}
  {Q : State I → Prop} {rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M}
  {fd : Lfundef I.Op I.Reg} {fn pc : Nat} {rv top : BitVec 64}

/-- An operation, for every result it may give: every state after it is safe. Nothing need
    be shown of an operation that gives none (a load or a store whose check fails): it traps,
    and the run stops, safely (`fault`). -/
theorem opn' {op : I.Op} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn op))
    (h : ∀ r' m', I.opn op regs m = some (r', m') →
      I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  cases he : I.opn op regs m with
  | none => exact fault hf hi he
  | some rm => exact opn hf hi he (h rm.1 rm.2 he)

/-- A branch, for each value its condition may have. Unlike an operation's, a condition that
    gives no value is `wrong`, so that it gives one is a goal. -/
theorem cond' {cnd : LOperand I.Reg} {l : LLabel} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcond cnd l)) {j : Nat} (hl : labelIdx fd.body l = some j)
    (hs : (I.cond cnd regs m).isSome)
    (ht : I.cond cnd regs m = some true → I.SafeN p c G n Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩)
    (hn : I.cond cnd regs m = some false → I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  cases hc : I.cond cnd regs m with
  | none => simp [hc] at hs
  | some b =>
    cases b
    · exact cond hf hi hc hl (fun h => nomatch h) (fun _ => hn hc)
    · exact cond hf hi hc hl (fun _ => ht hc) (fun h => nomatch h)

/-- A tail call, its continuation first and the stack pointer's condition after, the order a
    tactic that applies a specification to the continuation wants. -/
theorem tail' {tgt : Target I.Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Ltail tgt))
    {f : Nat} (hc : I.callee p regs tgt = some f)
    (h : I.SafeN p c G n Q ⟨⟨f, 0, rv, top⟩ :: rest, regs, m⟩) (hsp : regs I.sp = top) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  tail hf hi hsp hc h

/-- A call through a contract of the callee (`Isa.Contract`): the target reaches it, its
    precondition holds, and every state it returns to by its postcondition is safe after the
    call. -/
theorem call_contract {ret : BitVec 64} {tgt : Target I.Reg} {f : Nat}
    {Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
    {Post : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}
    (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lcall ret tgt)) (hcon : I.Contract p c f Pre Post)
    (hc : I.callee p regs tgt = some f) (hpre : Pre ret (regs I.sp) (updReg regs I.link ret) m)
    (hk : ∀ r' m', Post ret (regs I.sp) (updReg regs I.link ret) m r' m' →
      I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  call hf hi hc (hcon.run hpre hk)

/-- A tail call through a contract of the callee: the stack pointer is back, and the callee
    returns where the caller would. -/
theorem tail_contract {tgt : Target I.Reg} {f : Nat}
    {Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
    {Post : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}
    (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Ltail tgt)) (hcon : I.Contract p c f Pre Post)
    (hc : I.callee p regs tgt = some f) (hsp : regs I.sp = top) (hpre : Pre rv top regs m)
    (hk : ∀ r' m', Post rv top regs m r' m' → I.SafeN p c G n Q ⟨rest, r', m'⟩) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  tail hf hi hsp hc (hcon.run hpre hk)

end SafeN

attribute [lsym_simp] Isa.ofOps Op.eval Expr.eval BinOp.eval UnOp.eval condEval operandVal cmpEval Width.bytes Width.bits
  updReg_apply

-- addresses as a base plus one constant: a subtraction as the addition of its negation, sums
-- to the right, constants folded (by `simp`'s own `BitVec` simprocs); a frame opened and closed,
-- `sp - n + n`, is then `sp + 0`, which is `sp`
attribute [lsym_simp, lsym_addr] BitVec.sub_eq_add_neg BitVec.add_assoc BitVec.add_zero
  BitVec.add_left_neg BitVec.add_right_neg

/-- A size subtracted and added back, `-n + (n + c)`, as the normal form leaves `sp - n + n + c`:
    for a frame whose size is not a numeral. -/
@[lsym_simp, lsym_addr] theorem addr_neg_add_cancel {w : Nat} (a b : BitVec w) : -a + (a + b) = b := by
  rw [← BitVec.add_assoc, BitVec.add_left_neg, BitVec.zero_add]

/-- The same, the other way: `n + (-n + c)`. -/
@[lsym_simp, lsym_addr] theorem addr_add_neg_cancel {w : Nat} (a b : BitVec w) : a + (-a + b) = b := by
  rw [← BitVec.add_assoc, BitVec.add_right_neg, BitVec.zero_add]
attribute [lsym_addr] BitVec.reduceAdd BitVec.reduceNeg BitVec.reduceOfNat Nat.reduceMul Nat.reduceAdd

/-- A product of numerals and an index, its numerals together: `8 * (2 * j)` is `16 * j`. -/
theorem addr_mul_assoc (a b c : Nat) : a * (b * c) = a * b * c := (Nat.mul_assoc a b c).symm

-- an index into a region, `base + BitVec.ofNat 64 (8 * (2 * j + 1))`, as `lsym` computes it,
-- `base + (BitVec.ofNat 64 (16 * j) + 8#64)`: for facts about cells, by `simp only [lsym_addr]`
attribute [lsym_addr] BitVec.ofNat_add Nat.mul_add Nat.mul_one addr_mul_assoc

/-- One step of `lsym`, side conditions tried with `simp_all` and the given lemmas. -/
syntax (name := lstep) "lstep " term (" with " "[" Lean.Parser.Tactic.simpLemma,* "]")?
  (" using " "[" term,* "]")? : tactic

open Lean in
macro_rules
  | `(tactic| lstep $hf $[with [$lems,*]]? $[using [$specs,*]]?) => do
    -- the simp set by its name as it is, not as the quotation's hygiene would make it
    let set := mkIdent `lsym_simp
    -- the branch's hypothesis, by a name a proof can use
    let hc := mkIdent `hc
    let simpHc ← match lems with
      | some ls => `(tactic| all_goals try simp [$set:ident, $ls,*] at $hc:ident)
      | none => `(tactic| all_goals try simp [$set:ident] at $hc:ident)
    let close ← match lems with
      | some ls => `(tactic| try (first | rfl | (focus (simp_all [$set:ident, $ls,*]; done))))
      | none => `(tactic| try (first | rfl | (focus (simp_all [$set:ident]; done))))
    -- an operation's result, computed and substituted, so that what follows sees its value
    -- (`subst`, not the pattern `rfl`, which the quotation's hygiene would make a name). A
    -- load's or a store's check that `simp` cannot decide stays, as the hypothesis `hm` of what
    -- follows, and the result is substituted all the same; nothing need be shown of it, since
    -- an operation whose check fails traps (`SafeN.opn'`).
    let hm := mkIdent `hm
    -- (the memory's equation first: `subst` of a check, not an equation, can evaluate it)
    let eqs ← `(tactic| first
      | (obtain ⟨h1, h2⟩ := he; subst h2; subst h1)
      | (obtain ⟨$hm:ident, h1, h2⟩ := he; subst h2; subst h1)
      | (split at he
         · (rename_i $hm:ident; simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨h1, h2⟩ := he; subst h2; subst h1)
         · simp at he))
    let subst ← match lems with
      | some ls =>
        `(tactic| try (simp [$set:ident, $ls,*, Option.some.injEq, Prod.mk.injEq] at he; $eqs:tactic))
      | none =>
        `(tactic| try (simp [$set:ident, Option.some.injEq, Prod.mk.injEq] at he; $eqs:tactic))
    -- a call or a tail call, through the first specification that applies. A contract
    -- (`Isa.Contract`) names the callee: the call's target must be shown to reach it
    -- (`callee`, by `rfl`, or by `simp` and `decide`), or the contract is not this call's; the
    -- stack pointer and the precondition are closed by `simp` if they can be (not `rfl`, which
    -- on the continuation can unfold `SafeN` past the depth allowed), and the
    -- continuation is left for `lsym` to take up. Any other specification is applied as it
    -- is, and what it leaves tried with `simp_all`.
    let callee ← match lems with
      | some ls => `(tactic| first | rfl | (focus (simp [Lprog.Isa.callee, $set:ident, $ls,*]; done)) |
          (focus (simp [Lprog.Isa.callee, $set:ident, $ls,*]; decide)))
      | none => `(tactic| first | rfl | (focus (simp [Lprog.Isa.callee, $set:ident]; done)) |
          (focus (simp [Lprog.Isa.callee, $set:ident]; decide)))
    let side ← match lems with
      | some ls => `(tactic| all_goals (try (first | (focus (simp [Lprog.Isa.callee, $set:ident, $ls,*]; done)) |
          (focus (simp [Lprog.Isa.callee, $set:ident, $ls,*]; decide)))))
      | none => `(tactic| all_goals (try (first | (focus (simp [Lprog.Isa.callee, $set:ident]; done)) |
          (focus (simp [Lprog.Isa.callee, $set:ident]; decide)))))
    let specs : Array (TSyntax `term) := match specs with | some ss => ss.getElems | none => #[]
    let mut calls : Array (TSyntax `tactic) := #[]
    for sp in specs do
      -- through a contract: the callee, the stack pointer and the precondition closed if they
      -- can be, the continuation left
      calls := calls.push (← `(tactic| focus (refine Lprog.SafeN.call_contract $hf rfl $sp ?_ ?_ ?_; ($callee:tactic); ($side:tactic))))
      calls := calls.push (← `(tactic| focus (refine Lprog.SafeN.tail_contract $hf rfl $sp ?_ ?_ ?_ ?_; ($callee:tactic); ($side:tactic))))
      calls := calls.push (← `(tactic| (refine Lprog.SafeN.call $hf rfl rfl ?_; apply $sp; all_goals ($close:tactic))))
      calls := calls.push (← `(tactic| (refine Lprog.SafeN.tail' $hf rfl rfl ?_ ?_; apply $sp; all_goals ($close:tactic))))
    let base ← `(tactic| first
      | refine Lprog.SafeN.label $hf rfl ?_
      | (refine Lprog.SafeN.opn' $hf rfl (fun r' m' he => ?_); $subst)
      | refine Lprog.SafeN.goto $hf rfl rfl ?_
      | (refine Lprog.SafeN.cond' $hf rfl rfl ?_ (fun $hc:ident => ?_) (fun $hc:ident => ?_); $close; $simpHc)
      | (refine Lprog.SafeN.ret $hf rfl ?_ ?_ ?_
         $close
         $close))
    let all ← calls.foldlM (β := TSyntax `tactic)
      (fun acc c => `(tactic| first | ($acc:tactic) | ($c:tactic))) base
    return all

/-- **`lframe`**: a goal `∀ r, r ∉ S → r ≠ x0 → r' r = regs r`, where `r'` is `regs` with
    registers written by `updReg` (as `lsym` leaves it): each register written is in `S`. The
    lemmas given unfold `S` where it is a name. -/
syntax (name := lframe) "lframe" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean in
macro_rules
  | `(tactic| lframe $[[$lems,*]]?) => do
    let set := mkIdent `lsym_simp
    match lems with
    | some ls => `(tactic| (intro r hr _h0; simp only [$ls,*, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [$set:ident, hr]))
    | none => `(tactic| (intro r hr _h0; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [$set:ident, hr]))

open Lean Elab Tactic Meta in
/-- The function and the program counter of a goal `… ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩`,
    the program counter if it is a numeral (or a sum of numerals, as the steps leave it), the
    function if it is one too. -/
def goalAt? (g : MVarId) : MetaM (Option (Option Nat × Nat)) := do
  -- the type may be under metadata (`have` and other steps leave it)
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some s := t.getAppArgs.back? | return none
  let s ← whnfR s
  unless s.isAppOfArity ``State.mk 4 do return none
  let stack ← whnfR s.getAppArgs[1]!
  unless stack.isAppOfArity ``List.cons 3 do return none
  let fr ← whnfR stack.getAppArgs[1]!
  unless fr.isAppOfArity ``Frame.mk 4 do return none
  let some pc ← evalNat fr.getAppArgs[1]! | return none
  return some (← evalNat fr.getAppArgs[0]!, pc)

open Lean Meta in
/-- A goal `∀ r' m', Post … → SafeN … s`, a specification's continuation, with its binders
    introduced as `r'`, `m'` and `hret` (and `h₁`, … for any more); any other goal as it is. -/
def introCont (g : MVarId) : MetaM MVarId := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isForall do return g
  let n ← forallTelescope t fun xs body => do
    let body := body.consumeMData
    let some s := body.getAppArgs.back? | return 0
    let s ← whnfR s
    return if s.isAppOfArity ``State.mk 4 then xs.size else 0
  if n == 0 then return g
  -- a contract's postcondition is a function applied: `hret` is stated as what it says
  let g ← g.replaceTargetDefEq (← Core.betaReduce t)
  let names := [`r', `m', `hret] ++ (List.range n).map fun k => Name.mkSimple s!"h{k}"
  let (_, g') ← g.introN n (names.take n)
  return g'

open Lean Meta in
/-- The goal with each frame's program counter a literal: a step leaves `pc + 1`, and a jump the
    index `rfl` finds, which can be a long sum; the next step's lookup recurses through it. -/
def normPc (g : MVarId) : MetaM MVarId := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun e => do
    if e.isAppOfArity ``Frame.mk 4 then
      let args := e.getAppArgs
      if args[1]!.nat?.isSome then return .done e
      match ← evalNat args[1]! with
      | some n => return .done (mkAppN e.getAppFn (args.set! 1 (mkNatLit n)))
      | none => return .done e
    else return .continue)
  if t' == t then return g
  g.replaceTargetDefEq t'

initialize Lean.registerTraceClass `lsym

/-- **`lsym hf`**: step the body of the function `hf` names, on every branch, as far as
    `lstep` goes. `lsym hf stop [p, …]` leaves a goal where it comes to one of the program
    counters `p`, a loop's head, for its invariant (the goal it starts from is stepped even at
    one); `lsym hf … with [lemmas]` gives `simp_all` lemmas and hypotheses for the side
    conditions; `lsym hf … using [specs]` steps calls and tail calls through the first
    specification that applies (a callee's contract, stated from its entry, with a continuation
    `∀ r' m', Post … → SafeN …`), and goes on after the call with the postcondition as `hret`. -/
syntax (name := lsym) "lsym " term (" stop " "[" num,* "]")?
  (" with " "[" Lean.Parser.Tactic.simpLemma,* "]")? (" using " "[" term,* "]")? : tactic

open Lean Elab Tactic Meta in
@[tactic lsym] def evalLsym : Tactic := fun stx => do
  let hf : TSyntax `term := ⟨stx[1]⟩
  let stops : List Nat := if stx[2].isNone then [] else
    (stx[2][2].getSepArgs.toList.filterMap fun n => n.isNatLit?)
  let lems : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := if stx[3].isNone then #[] else
    stx[3][2].getSepArgs.map fun t => ⟨t⟩
  let ls : Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma "," := lems
  let specs : Array (TSyntax `term) := if stx[4].isNone then #[] else
    stx[4][2].getSepArgs.map fun t => ⟨t⟩
  let ss : Syntax.TSepArray `term "," := specs
  let step ← match lems.isEmpty, specs.isEmpty with
    | true, true => `(tactic| lstep $hf)
    | false, true => `(tactic| lstep $hf with [$ls,*])
    | true, false => `(tactic| lstep $hf using [$ss,*])
    | false, false => `(tactic| lstep $hf with [$ls,*] using [$ss,*])
  -- each goal with the program counters its path has stepped from, to find a loop
  let mut todo : List (MVarId × List (Nat × Nat)) ←
    (← getGoals).mapM fun g => return (← liftMetaM (normPc g), [])
  -- the goals it starts from are stepped even at a stop: a stop is for coming back to
  let start := todo.map (·.1)
  let mut left : Array MVarId := #[]
  let mut fuel := 100000
  while !todo.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let (g, seen) := todo.head!
    todo := todo.tail!
    if ← g.isAssigned then continue
    -- a goal that is no `SafeN` at a program counter (a side condition) is left as it is
    let at? ← g.withContext (goalAt? g)
    match at? with
    | none => left := left.push g
    | some (fn?, pc) =>
      if stops.contains pc && !start.contains g then left := left.push g
      else if fn?.any (fun fn => seen.contains (fn, pc)) then
        trace[lsym] "left at {pc}: the path has stepped from it before, so it is a loop's head; \
          give `stop [{pc}]` and an invariant"
        left := left.push g
      else
        setGoals [g]
        let saved ← saveState
        -- a lookup in the body by `rfl` recurses once per entry: a body of a few hundred
        -- entries needs more than the default depth. A step that still runs out of depth or
        -- heartbeats leaves its goal (`tryCatchRuntimeEx`: `try … catch` does not catch them)
        let err? ← tryCatchRuntimeEx
          (do
            withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 16384 })
              (evalTactic step)
            pure none)
          (fun e => pure (some e))
        match err? with
        | none =>
          -- a specification's continuation, `∀ r' m', Post … → SafeN …`, taken up after the call
          let seen' := match fn? with | some fn => (fn, pc) :: seen | none => seen
          let mut next : List (MVarId × List (Nat × Nat)) := []
          for g' in (← getGoals) do
            next := next ++ [(← normPc (← introCont g'), seen')]
          todo := next ++ todo
        | some e =>
          saved.restore (restoreInfo := true)
          trace[lsym] "left at {pc}: no step applies (a call without a specification, an external \
            call, or a body that is not a literal): {e.toMessageData}"
          left := left.push g
  setGoals (left.toList ++ todo.map (·.1))

