import MachineChecked.RiscV.Sym.Tactic

/-!
# Resuming `sym_exec`

`sym_exec` transports its region facts from its start state along a frame fact
`Unchanged W s₀ s`, so a second run from a stopped state `sₖ` needs one that starts at `sₖ`.
`sym_reframe` composes the frame of the run so far into `hframe : Unchanged W s sₖ` (where `s` is
the first run's start: an older `hframe` and the stopped run's `hunch`, by `Unchanged.trans`) and
adds `hu : Unchanged W sₖ sₖ` for the next run. At the return, `sym_close` joins `hframe` to
the last run's frame.
-/

namespace MachineChecked.RiscV.Sym

open Lean Elab Tactic Meta

elab "sym_reframe" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``MachineChecked.RiscV.SafeN 4 do throwError "sym_reframe: goal is not `SafeN G n P s`"
  let s := ty.appArg!
  let lctx ← getLCtx
  let some h := lctx.findDeclRev? (fun d => if d.userName == `hunch then some d else none)
    | throwError "sym_reframe: no `hunch`"
  let hty ← instantiateMVars h.type
  unless hty.isAppOfArity ``MachineChecked.RiscV.Sym.Unchanged 3 do throwError "sym_reframe: `hunch` is not a frame fact"
  let W := hty.appFn!.appFn!.appArg!
  let old := lctx.findDeclRev? (fun d => if d.userName == `hframe then some d else none)
  let frame ← match old with
    | some f => mkAppM ``MachineChecked.RiscV.Sym.Unchanged.trans #[f.toExpr, h.toExpr]
    | none => pure h.toExpr
  let refl := mkApp2 (mkConst ``MachineChecked.RiscV.Sym.Unchanged.refl) W s
  -- the code map: `hcode : s.code = sⱼ.code` from the run so far, composed with an older
  -- `hcode0 : sⱼ.code = s₀.code` into `hcode0 : s.code = s₀.code`
  let isCodeEq (d : LocalDecl) : MetaM Bool := do
    let ty ← instantiateMVars d.type
    match ty.eq? with
    | some (_, l, r) =>
      let c := ``RiscvZkvm.Rv64.MachineState.code
      return l.isAppOfArity c 1 && r.isAppOfArity c 1
    | none => return false
  let mut codeNow : Option LocalDecl := none
  for d in lctx do
    if d.userName == `hcode && (← isCodeEq d) then codeNow := some d
  let codeOld := lctx.findDeclRev? (fun d => if d.userName == `hcode0 then some d else none)
  let codePf? ← match codeNow with
    | some c => match codeOld with
      | some c0 => some <$> mkAppM ``Eq.trans #[c.toExpr, c0.toExpr]
      | none => pure (some c.toExpr)
    | none => pure none
  let mut hyps := #[
    ({ userName := `hframe, type := ← inferType frame, value := frame } : Hypothesis),
    { userName := `hu, type := ← inferType refl, value := refl }]
  if let some pf := codePf? then
    hyps := hyps.push { userName := `hcode0, type := ← inferType pf, value := pf }
  let (_, g) ← g.assertHypotheses hyps
  let g ← g.tryClearMany (#[h.fvarId] ++ (old.map (·.fvarId)).toArray ++ (codeOld.map (·.fvarId)).toArray)
  -- the intermediate states and every fact about them: only the first run's start `s₀` (in
  -- `hframe`) and the current state matter from here
  let s₀ := (← instantiateMVars (← inferType frame)).appFn!.appArg!
  let g ← g.withContext do
    let msTy := mkConst ``RiscvZkvm.Rv64.MachineState
    let mut stale : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if d.toExpr == s || d.toExpr == s₀ then continue
      if ← isDefEq d.type msTy then stale := stale.push d.fvarId
    let mut ids : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if (ty.find? fun e => e.isFVar && stale.contains e.fvarId!).isSome then ids := ids.push d.fvarId
    g.tryClearMany (ids.reverse ++ stale.reverse)
  replaceMainGoal [g]

/-- Clear the executor's atom definitions (`…_def`) that nothing else mentions: once the
arithmetic they carry has been summarised, they only slow the next run down. -/
elab "sym_forget" : tactic => withMainContext do
  let g ← getMainGoal
  let mut ids : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if d.userName.toString.endsWith "_def" then ids := ids.push d.fvarId
  replaceMainGoal [← g.tryClearMany ids]

end MachineChecked.RiscV.Sym
