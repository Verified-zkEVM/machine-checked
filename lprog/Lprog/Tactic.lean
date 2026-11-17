/-
  Lprog.Tactic

  `lsym`: symbolic execution of an Lprog function body, for any instruction set. A first form
  (`docs/design/Automation.md`, item 1).

  The goal is `I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩`; `lsym hf` takes
  `hf : p[fn]? = some fd` and steps the body of `fd` from `pc`:

  * a label, and an operation whose result is computed by `rfl` (one that cannot fault), are
    stepped over;
  * an operation that may fault (a load or a store, behind the instruction set's memory
    check) is stepped with its result named (`r'`, `m'` and the equation `he`), and leaves the
    side goal that it does not fault, which `lsym` tries to close with `simp_all`;
  * a `goto` goes to its label;
  * an `Lcond` splits: one goal for each outcome, with the condition's value as the hypothesis
    `hc`, simplified;
  * a return leaves the goals that the link register and the stack pointer are as the call
    left them, and the goal after it.

  It stops where it can do nothing: at a call, an external call, or a loop's head, which a
  proof meets with the function's specification or an invariant. The instruction at `pc` is
  found by `rfl`, so the body should be a literal (`decompile --to lean` writes one, `f<i>`);
  a body to be computed is computed again at each step.

  ## Main results

  * `SafeN.opn'`, `SafeN.cond'`: the rules in the form a tactic applies
  * `lstep`, `lsym`
-/

import Lean
import Lprog.Block
import Lprog.LsymAttr
import Lprog.Op

namespace Lprog

namespace SafeN

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {G : State I → Prop} {n : Nat}
  {Q : State I → Prop} {rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M}
  {fd : Lfundef I.Op I.Reg} {fn pc : Nat} {rv top : BitVec 64}

/-- An operation, for every result it may give: safe if it gives one, and every state after it
    is safe. -/
theorem opn' {op : I.Op} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn op))
    (h : ∀ r' m', I.opn op regs m = some (r', m') →
      I.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩)
    (hs : (I.opn op regs m).isSome) :
    I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  cases he : I.opn op regs m with
  | none => simp [he] at hs
  | some rm => exact opn hf hi he (h rm.1 rm.2 he)

/-- A branch, for each value its condition may have. -/
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

end SafeN

attribute [lsym_simp] Isa.ofOps Op.eval Expr.eval BinOp.eval UnOp.eval condEval operandVal cmpEval Width.bytes
  updReg_apply

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
    -- (`subst`, not the pattern `rfl`, which the quotation's hygiene would make a name)
    let subst ← match lems with
      | some ls =>
        `(tactic| try (simp [$set:ident, $ls,*, Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨h1, h2⟩ := he; subst h1; subst h2))
      | none =>
        `(tactic| try (simp [$set:ident, Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨h1, h2⟩ := he; subst h1; subst h2))
    -- a call or a tail call, through the first specification that applies: the callee is
    -- computed (`rfl`), the specification applied to the state at its entry, and what it leaves
    -- (its preconditions, and its continuation, which `lsym` takes up) tried with `simp_all`
    let specs : Array (TSyntax `term) := match specs with | some ss => ss.getElems | none => #[]
    let mut calls : Array (TSyntax `tactic) := #[]
    for sp in specs do
      calls := calls.push (← `(tactic| (refine Lprog.SafeN.call $hf rfl rfl ?_; apply $sp; all_goals ($close:tactic))))
      calls := calls.push (← `(tactic| (refine Lprog.SafeN.tail' $hf rfl rfl ?_ ?_; apply $sp; all_goals ($close:tactic))))
    let base ← `(tactic| first
      | refine Lprog.SafeN.label $hf rfl ?_
      | refine Lprog.SafeN.opn $hf rfl rfl ?_
      | (refine Lprog.SafeN.opn' $hf rfl (fun r' m' he => ?_) ?_; $subst; rotate_left 1; $close)
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
/-- The program counter of a goal `… ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩`, if it is a
    numeral (or a sum of numerals, as the steps leave it). -/
def goalPc? (g : MVarId) : MetaM (Option Nat) := do
  -- the type may be under metadata (`have` and other steps leave it)
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some s := t.getAppArgs.back? | return none
  let s ← whnfR s
  unless s.isAppOfArity ``State.mk 4 do return none
  let stack ← whnfR s.getAppArgs[1]!
  unless stack.isAppOfArity ``List.cons 3 do return none
  let fr ← whnfR stack.getAppArgs[1]!
  unless fr.isAppOfArity ``Frame.mk 4 do return none
  evalNat fr.getAppArgs[1]!

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
  let names := [`r', `m', `hret] ++ (List.range n).map fun k => Name.mkSimple s!"h{k}"
  let (_, g') ← g.introN n (names.take n)
  return g'

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
  let mut todo := (← getGoals)
  -- the goals it starts from are stepped even at a stop: a stop is for coming back to
  let start := todo
  let mut left : Array MVarId := #[]
  let mut fuel := 100000
  while !todo.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let g := todo.head!
    todo := todo.tail!
    if ← g.isAssigned then continue
    -- a goal that is no `SafeN` at a program counter (a side condition) is left as it is
    let pc? ← g.withContext (goalPc? g)
    match pc? with
    | none => left := left.push g
    | some pc =>
      if stops.contains pc && !start.contains g then left := left.push g
      else
        setGoals [g]
        let ok ← try evalTactic step; pure true catch _ => pure false
        if ok then
          -- a specification's continuation, `∀ r' m', Post … → SafeN …`, taken up after the call
          let mut next : List MVarId := []
          for g' in (← getGoals) do
            next := next ++ [← introCont g']
          todo := next ++ todo
        else left := left.push g
  setGoals (left.toList ++ todo)

