/-
  AsmVerif.RiscV.Sym.Close

  `sym_close hk`: finish a specification proof at a return.

  After `sym_exec` stops at the return, the goal is `SafeN G n P t` and the context
  holds the executor's facts about `t`. `sym_close hk` applies the
  specification's continuation `hk` and discharges each of its hypotheses:

  * `t.pc = e`, `t.getReg r = e`   -- from `hpc` and the register file `Regs t l`
  * `CalleeSaved s t`             -- register by register, `Regs s l₀` against `Regs t l`
  * `t.code = s.code`, `Unchanged W s t` -- the executor's chained facts
  * `Region b vs t`               -- a tracked region, after rewriting `vs` with the
                                     atom definitions (`*_def`) the executor introduced;
                                     failing that, the region fact at `b`, leaving the
                                     equation of the contents as a goal
  * anything else                 -- assumption, `simp` with the facts, `omega`.

  Whatever it cannot discharge is left as a goal.
-/

import AsmVerif.RiscV.Sym.Tactic

open Lean Meta Elab Tactic

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64.Accel in
/-- The four cells the executor leaves for `natToLeLimbs 4 a`. -/
theorem cells4 (a : Nat) :
    [BitVec.ofNat 64 (a >>> 0), BitVec.ofNat 64 (a >>> 64), BitVec.ofNat 64 (a >>> 128),
      BitVec.ofNat 64 (a >>> 192)] = natToLeLimbs 4 a := rfl

open RiscvZkvm.Rv64.Accel in
theorem cells4' (a : Nat) :
    [BitVec.ofNat 64 (a >>> (64 * 0)), BitVec.ofNat 64 (a >>> (64 * 1)),
      BitVec.ofNat 64 (a >>> (64 * 2)), BitVec.ofNat 64 (a >>> (64 * 3))] = natToLeLimbs 4 a := rfl

end AsmVerif.RiscV.Sym

namespace AsmVerif.RiscV.Sym.Close

open RiscvZkvm.Rv64 AsmVerif.RiscV.Sym.Meta

def findHyp (p : Expr → MetaM Bool) : MetaM (Option LocalDecl) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← p (← instantiateMVars d.type) then return some d
  return none

/-- The register-file fact about `s`. -/
def regsOf? (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let some d ← findHyp fun ty => pure (ty.isAppOfArity ``AsmVerif.RiscV.Sym.Regs 2 && ty.appFn!.appArg! == s)
    | return none
  return some (d.toExpr, (← instantiateMVars d.type).appArg!)

/-- For each list variable `l` with a length fact `l.length = n`, the equation
    `[l[0]!, …, l[n-1]!] = l`: the executor expands such a list into its cells. -/
def foldRules : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    unless lhs.isAppOfArity ``List.length 2 && lhs.appArg!.isFVar do continue
    let some n ← getNatValue? rhs | continue
    let l := lhs.appArg!
    let heq ← mkAppM ``AsmVerif.RiscV.Sym.List.eq_map_range #[l, d.toExpr]    -- l = map
    let mapE := (← inferType heq).appArg!
    let elemTy ← inferType (← mkAppOptM ``GetElem?.getElem! #[none, none, none, none, none, none, l, mkNatLit 0])
    let cells ← (List.range n).toArray.mapM fun i => mkAppM ``GetElem?.getElem! #[l, mkNatLit i]
    let lit := mkListLit elemTy cells
    let hr ← mkExpectedTypeHint (← mkEqRefl lit) (← mkEq lit mapE)
    out := out.push (← mkAppM ``Eq.trans #[hr, ← mkAppM ``Eq.symm #[heq]])
  return out

/-- The atom definitions `e = x`, with expanded list variables folded back in `e`. -/
def atomDefs : MetaM (Array Expr) := do
  let folds ← foldRules
  let mut out := #[]
  for d in ← getLCtx do
    if d.userName.toString.endsWith "_def" then
      if folds.isEmpty then out := out.push d.toExpr; continue
      let ty ← instantiateMVars d.type
      let some (_, e, _) := ty.eq? | out := out.push d.toExpr; continue
      let (_, pf) ← rewriteTo e folds #[]
      out := out.push (← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[pf], d.toExpr])
  return out

/-- `s.getReg (regOf i) = l[i]!`, stated as `s.getReg .xᵢ = v`. -/
def regEq (s h l : Expr) (i : Nat) : MetaM (Expr × Expr) := do
  let cells ← listElems l
  let v := cells[i]!
  let pf := mkAppN (mkConst ``AsmVerif.RiscV.Sym.Regs.get) #[s, l, h, mkNatLit i, ← natLt i 32]
  return (← mkExpectedTypeHint pf (mkEqW (mkGetReg s i) v), v)

partial def closeCalleeSaved (s t : Expr) : MetaM Expr := do
  -- through a state with a register file: `CalleeSaved s t₀`, then `t₀` to `t`
  if (← regsOf? s).isNone then
    let some d ← findHyp fun ty => pure (ty.isAppOfArity ``AsmVerif.RiscV.Sym.CalleeSaved 2 && ty.appFn!.appArg! == s
        && ty.appArg! != t)
      | throwError "sym_close: no register file for {s}"
    let t₀ := (← instantiateMVars d.type).appArg!
    return ← mkAppM ``AsmVerif.RiscV.Sym.CalleeSaved.trans #[d.toExpr, ← closeCalleeSaved t₀ t]
  let some (hs, ls) ← regsOf? s | throwError "sym_close: no register file for {s}"
  let some (ht, lt) ← regsOf? t | throwError "sym_close: no register file for {t}"
  let mut args := #[]
  for i in [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] do
    let (pt, vt) ← regEq t ht lt i
    let (ps, vs) ← regEq s hs ls i
    unless ← isDefEq vt vs do
      throwError "sym_close: callee-saved register x{i} holds {vt}, was {vs}"
    args := args.push (← mkAppM ``Eq.trans #[pt, ← mkAppM ``Eq.symm #[ps]])
  mkAppM ``AsmVerif.RiscV.Sym.CalleeSaved.intro args

/-- `[v[0]!, …, v[n-1]!] = v` for a list atom `v`, its length from its definition. -/
def cellsOfAtom (vsH v : Expr) (defs : Array Expr) : TacticM (Option Expr) := do
  unless v.isFVar do return none
  let cells? : Option (Array Expr) ← try some <$> listElems vsH catch _ => pure none
  let some cells := cells? | return none
  let n := cells.size
  for i in [0:n] do
    let c := cells[i]!
    unless c.isAppOfArity ``GetElem?.getElem! 8 && c.appFn!.appArg! == v do return none
    unless (← getNatValue? c.appArg!) == some i do return none
  let lenTy ← mkEq (← mkAppM ``List.length #[v]) (mkNatLit n)
  let back ← defs.mapM fun d => mkAppM ``Eq.symm #[d]
  let mut lens := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (_, lhs, _) := (← instantiateMVars d.type).eq? then
      if lhs.isAppOfArity ``List.length 2 then lens := lens.push d.toExpr
  let some hlen ← proveBySimp lenTy (back ++ lens) #[``AsmVerif.RiscV.Sym.length_curveAddL, ``AsmVerif.RiscV.Sym.length_curveDblL,
      ``List.length_cons, ``List.length_nil]
    | return none
  let heq ← mkAppM ``AsmVerif.RiscV.Sym.List.eq_map_range #[v, hlen]      -- v = map
  let mapE := (← inferType heq).appArg!
  let hr ← mkExpectedTypeHint (← mkEqRefl vsH) (← mkEq vsH mapE)
  return some (← mkAppM ``Eq.trans #[hr, ← mkAppM ``Eq.symm #[heq]])

/-- `∀ r ∈ W', ∃ r' ∈ W, Covers r'.1 r'.2 r.1 r.2`, entry by entry by `omega`. -/
def coverProof (W W' : Expr) : TacticM (Option Expr) := do
  let ws ← listElems W
  let ws' ← listElems W'
  let prodTy ← mkAppM ``Prod #[wordTy, natTy]
  let mut pf ← mkAppOptM ``AsmVerif.RiscV.Sym.cover_nil #[some W]
  for j in (List.range ws'.size).reverse do
    let e := ws'[j]!
    let mut found : Option Expr := none
    for wi in [0:ws.size] do
      if found.isSome then break
      let w := ws[wi]!
      let prop := mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Covers) (← mkAppM ``Prod.fst #[w]) (← mkAppM ``Prod.snd #[w])
        (← mkAppM ``Prod.fst #[e]) (← mkAppM ``Prod.snd #[e])
      let some hc ← proveByOmega prop | continue
      let mut memPf ← mkAppOptM ``List.mem_cons_self #[some prodTy, some w,
        some (mkListLit prodTy (ws.extract (wi+1) ws.size))]
      for jj in (List.range wi).reverse do
        memPf ← mkAppM ``List.mem_cons_of_mem #[ws[jj]!, memPf]
      found := some (← mkAppM ``AsmVerif.RiscV.Sym.cover_cons #[memPf, hc, pf])
    match found with
    | some p => pf := p
    | none => return none
  return some pf

/-- Two region bases equal: reducibly, else by unification only when they share their atom
    (`T.b3` against `sp + 0x18` unfolds the bit-vector arithmetic past the recursion limit). -/
def sameBase (b' b : Expr) : MetaM Bool := do
  if ← withReducible (isDefEq b' b) then return true
  let l' ← normLin b'
  let l ← normLin b
  if !l'.sameAtom l then return false
  isDefEq b' b

/-- Close a goal, or return the goals it reduces to. -/
def closeOne (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  -- an assumption
  if let some d ← findHyp (fun t => withReducible (isDefEq t ty)) then
    g.assign d.toExpr; return []
  match_expr ty with
  | AsmVerif.RiscV.Sym.CalleeSaved s t => g.assign (← closeCalleeSaved s t); return []
  | AsmVerif.RiscV.Sym.Unchanged W s u =>
    -- `Unchanged W s t₀` then `Unchanged W' t₀ u`, `W` covering `W'`
    for d₁ in ← getLCtx do
      let ty₁ ← instantiateMVars d₁.type
      unless ty₁.isAppOfArity ``AsmVerif.RiscV.Sym.Unchanged 3 && ty₁.appFn!.appArg! == s do continue
      unless ← isDefEq ty₁.appFn!.appFn!.appArg! W do continue
      let t₀ := ty₁.appArg!
      for d₂ in ← getLCtx do
        let ty₂ ← instantiateMVars d₂.type
        unless ty₂.isAppOfArity ``AsmVerif.RiscV.Sym.Unchanged 3 && ty₂.appFn!.appArg! == t₀ && ty₂.appArg! == u do continue
        let W' := ty₂.appFn!.appFn!.appArg!
        if let some hc ← coverProof W W' then
          g.assign (← mkAppM ``AsmVerif.RiscV.Sym.Unchanged.trans_cover #[d₁.toExpr, d₂.toExpr, hc])
          return []
    return [g]
  | AsmVerif.RiscV.Sym.Region b vs t =>
    let defs ← atomDefs
    let (vs', pf) ← rewriteTo vs defs #[]
    let pf' := pf   -- : vs = vs'
    for d in ← getLCtx do
      let dty ← instantiateMVars d.type
      if dty.isAppOfArity ``AsmVerif.RiscV.Sym.Region 3 && dty.appArg! == t then
        let b' := dty.appFn!.appFn!.appArg!
        let vsH := dty.appFn!.appArg!
        if ← sameBase b' b then
          if ← withReducible (isDefEq vsH vs') then
            -- `Region b vs' t` → `Region b vs t`
            let pf' ← mkAppM ``Eq.symm #[pf]
            g.assign (← mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[d.toExpr, pf'])
            return []
    -- a region fact at the same base: its contents equal the goal's, left to the proof
    for d in ← getLCtx do
      let dty ← instantiateMVars d.type
      if dty.isAppOfArity ``AsmVerif.RiscV.Sym.Region 3 && dty.appArg! == t then
        if ← sameBase dty.appFn!.appFn!.appArg! b then
          let vsH := dty.appFn!.appArg!
          -- the same number, as four cells
          let eqTy ← mkEq vsH vs'
          if let some pf ← proveBySimp eqTy #[] #[``AsmVerif.RiscV.Sym.cells4, ``AsmVerif.RiscV.Sym.cells4', ``eq_self] then
            g.assign (← mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[d.toExpr, ← mkAppM ``Eq.trans #[pf, ← mkAppM ``Eq.symm #[pf']]])
            return []
          -- a list atom `v`, as its cells `[v[0]!, …]`
          if let some pf ← cellsOfAtom vsH vs' defs then
            g.assign (← mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[d.toExpr, ← mkAppM ``Eq.trans #[pf, ← mkAppM ``Eq.symm #[pf']]])
            return []
          let eqG ← mkFreshExprSyntheticOpaqueMVar (← mkEq vsH vs) `contents
          g.assign (← mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[d.toExpr, eqG])
          return [eqG.mvarId!]
    return [g]
  | _ => pure ()
  -- `∃ ws, ws.length = n ∧ Region b ws t`: a region fact at `b` of `n` cells
  if ty.isAppOfArity ``Exists 2 then
    let p := ty.appArg!
    let ws ← mkFreshExprMVar ty.appFn!.appArg!
    let body ← whnfR (p.beta #[ws])
    if let some (lenTy, regTy) := body.and? then
      if regTy.isAppOfArity ``AsmVerif.RiscV.Sym.Region 3 then
        let b := regTy.appFn!.appFn!.appArg!
        let t := regTy.appArg!
        for d in ← getLCtx do
          let dty ← instantiateMVars d.type
          unless dty.isAppOfArity ``AsmVerif.RiscV.Sym.Region 3 && dty.appArg! == t do continue
          unless ← sameBase dty.appFn!.appFn!.appArg! b do continue
          let vsH := dty.appFn!.appArg!
          let s ← saveState
          unless ← isDefEq ws vsH do s.restore; continue
          let lenTy ← instantiateMVars lenTy
          let some hl ← proveBySimp lenTy #[] #[``List.length_cons, ``List.length_nil, ``AsmVerif.RiscV.Sym.length_contents]
            | s.restore; continue
          g.assign (← mkAppOptM ``Exists.intro #[none, some p, some vsH,
            some (← mkAppM ``And.intro #[hl, d.toExpr])])
          return []
  -- a large statement (a model of a whole buffer) is the proof's: `simp` over it with every fact
  -- in context can run for an hour
  if dagSize ty > 4000 then return [g]
  -- equations and the rest: `simp` with the facts, then `omega`
  let facts ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let t ← instantiateMVars d.type
    if t.isEq || t.isAppOfArity ``Not 1 then return acc.push d.toExpr
    return acc
  -- register facts from the register file
  let mut regFacts := #[]
  if let some (_, lhs, _) := ty.eq? then
    if lhs.isAppOfArity ``MachineState.getReg 2 then
      let s := lhs.appFn!.appArg!
      if let some (h, l) ← regsOf? s then
        let i ← regIdx lhs.appArg!
        regFacts := regFacts.push (← regEq s h l i).1
  if let some pf ← proveBySimp ty (regFacts ++ facts) (normLemmas ++ #[``BitVec.ofNat_add]) then
    g.assign pf; return []
  if let some pf ← proveByOmega ty then
    g.assign pf; return []
  -- left to the proof
  return [g]

/-- `closeOne`, reporting any goal that takes over a second (`trace.Asm.sym.time`). -/
def timedClose (g : MVarId) : TacticM (List MVarId) := do
  let t0 ← IO.monoMsNow
  let r ← closeOne g
  let t1 ← IO.monoMsNow
  if t1 - t0 > 1000 then
    let ty ← instantiateMVars (← g.getType)
    trace[AsmVerif.sym.time] "sym_close: {t1 - t0} ms on a goal of size {dagSize ty}, head {ty.getAppFn}"
  return r

end AsmVerif.RiscV.Sym.Close

namespace AsmVerif.RiscV.Sym

open Lean Elab Tactic in
/-- Close `SafeN G n P t` at a return by the specification's continuation. -/
elab "sym_close " h:term : tactic => do
  let g ← getMainGoal
  let hk ← g.withContext do
    let e ← Term.elabTerm h none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let gs ← g.apply hk
  replaceMainGoal []
  let mut rest : List MVarId := []
  -- a goal about an argument still to be determined (`?acc.length = 9`) waits
  -- for the region that determines it, rather than matching any assumption
  let mut later : List MVarId := []
  for gi in gs do
    if ← gi.isAssigned then continue
    let ty ← instantiateMVars (← gi.getType)
    if ty.hasExprMVar && !ty.isAppOf ``AsmVerif.RiscV.Sym.Region then later := later ++ [gi]; continue
    rest := rest ++ (← Close.timedClose gi)
  for gi in later do
    if ← gi.isAssigned then continue
    rest := rest ++ (← Close.timedClose gi)
  setGoals rest

end AsmVerif.RiscV.Sym

namespace AsmVerif.RiscV.Sym

open Lean Elab Tactic Meta in
/-- Substitute every atom the executor named (`x_def : e = x`), newest first. -/
elab "sym_subst" : tactic => do
  let defs ← withMainContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.userName.toString.endsWith "_def" then out := out.push d.fvarId
    return out
  for h in defs.reverse do
    let g ← getMainGoal
    let ty ← g.withContext do instantiateMVars (← h.getType)
    if let some (_, _, rhs) := ty.eq? then
      if rhs.isFVar then
        let g' ← substCore g h (symm := true)
        replaceMainGoal [g'.2]

end AsmVerif.RiscV.Sym

namespace AsmVerif.RiscV.Sym

open Lean Elab Tactic Meta in
/-- Unfold, one level, the atoms the executor named (`x_def : e = x`, read `x = e`) that occur
    in the goal: a small leftover goal (a tag byte of a cell named by an atom) to plain terms
    for `simp`. One level only: an atom naming a whole buffer unfolds to a term over hundreds of
    further atoms, and unfolding those too blows up. -/
elab "sym_unfold" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let inGoal := (collectFVars {} ty).fvarSet
  let mut rules := #[]
  for d in ← getLCtx do
    if d.userName.toString.endsWith "_def" then
      let dty ← instantiateMVars d.type
      let some (_, _, x) := dty.eq? | continue
      unless x.isFVar && inGoal.contains x.fvarId! do continue
      rules := rules.push (← mkAppM ``Eq.symm #[d.toExpr])
  let (ty', pf) ← AsmVerif.RiscV.Sym.Meta.rewriteTo ty rules #[]
  let g' ← mkFreshExprSyntheticOpaqueMVar ty'
  g.assign (← mkAppM ``Eq.mpr #[pf, g'])
  replaceMainGoal [g'.mvarId!]

end AsmVerif.RiscV.Sym
