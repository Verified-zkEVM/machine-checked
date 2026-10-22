import Lean
import MachineChecked.RiscV.Sym.Frame

/-!
# Naming the cells of a tracked region between two executor runs

A contract that mentions a callee's argument words (`commit_ivk`'s `hfrom`: the `ak` and `nk`
words) is instantiated at the stop before the call. The words are whatever the executor holds in
the region at that address — large terms. `generalize_cells a₀ a₁ … : base` abstracts the first
cells of the `Region base [...] _` hypothesis found in the context into fresh variables, so the
contract is stated over names and matches the callee's precondition by unification.
-/

open Lean Elab Tactic Meta

namespace MachineChecked.RiscV.Sym

/-- `e` occurs in `ty` (syntactically). -/
def _root_.Lean.Expr.containsExpr (ty e : Expr) : Bool :=
  Option.isSome <| ty.find? (· == e)

open RiscvZkvm.Rv64

/-- `x + N#64` as `(x, N)`; anything else as `(e, 0)`. -/
def splitOff (e : Expr) : Expr × Nat :=
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let args := e.getAppArgs
    let lit := args[5]!
    if lit.isAppOfArity ``BitVec.ofNat 2 then
      match lit.appArg!.rawNatLit? with
      | some n => (args[4]!, n)
      | none => match lit.appArg!.nat? with
        | some n => (args[4]!, n)
        | none => (e, 0)
    else (e, 0)
  else (e, 0)

syntax (name := generalizeCells) "generalize_cells " (colGt ident)+ " : " term : tactic

@[tactic generalizeCells] def evalGeneralizeCells : Tactic := fun stx => do
  match stx with
  | `(tactic| generalize_cells $ids:ident* : $b:term) => withMainContext do
    let bE ← elabTerm b none
    let (bAtom, bOff) := splitOff bE
    let mut cells? : Option (Array Expr) := none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.isAppOfArity ``MachineChecked.RiscV.Sym.Region 3 do continue
      let args := ty.getAppArgs
      let some (_, elems) := (args[1]!).listLit? | continue
      -- the region at that base, or one at a literal offset below it on the same atom
      if ← isDefEq args[0]! bE then
        cells? := some elems.toArray
        break
      let (rAtom, rOff) := splitOff args[0]!
      unless ← isDefEq rAtom bAtom do continue
      let off := (bOff + 2 ^ 64 - rOff) % 2 ^ 64
      unless off % 8 == 0 && off / 8 < elems.length do continue
      cells? := some (elems.toArray.extract (off / 8) elems.length)
      break
    let some cells := cells? | throwError "generalize_cells: no region with a literal list at {bE}"
    unless ids.size ≤ cells.size do
      throwError "generalize_cells: {ids.size} names for {cells.size} cells"
    let mut g ← getMainGoal
    for i in [0:ids.size] do
      -- the hypotheses over the cell go back into the goal, so they are abstracted too
      let deps ← g.withContext do
        let mut fvs : Array FVarId := #[]
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          if (← instantiateMVars d.type).containsExpr cells[i]! then fvs := fvs.push d.fvarId
        pure fvs
      let (fvs', g₁) ← g.revert deps
      let (_, g₂) ← g₁.generalize #[{ expr := cells[i]!, xName? := some ids[i]!.getId }]
      let (_, g₃) ← g₂.introNP fvs'.size
      g := g₃
    replaceMainGoal [g]
  | _ => throwUnsupportedSyntax

syntax (name := generalizeReg) "generalize_reg " ident " : " term : tactic

/-- `generalize_reg v : Reg.x8` abstracts the value a register fact `_.getReg Reg.x8 = e` (the
most recent one) gives into a fresh variable `v`. -/
@[tactic generalizeReg] def evalGeneralizeReg : Tactic := fun stx => do
  match stx with
  | `(tactic| generalize_reg $id:ident : $r:term) => withMainContext do
    let rE ← elabTerm r none
    let mut val? : Option Expr := none
    for d in (← getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOfArity ``MachineState.getReg 2 do continue
      unless ← isDefEq lhs.appArg! rE do continue
      val? := some rhs
      break
    let some v := val? | throwError "generalize_reg: no register fact for {rE}"
    let g ← getMainGoal
    let deps ← g.withContext do
      let mut fvs : Array FVarId := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if (← instantiateMVars d.type).containsExpr v then fvs := fvs.push d.fvarId
      pure fvs
    let (fvs', g₁) ← g.revert deps
    let (_, g₂) ← g₁.generalize #[{ expr := v, xName? := some id.getId }]
    let (_, g₃) ← g₂.introNP fvs'.size
    replaceMainGoal [g₃]
  | _ => throwUnsupportedSyntax

example (s : MachineState) (x : Word) (h : s.getReg Reg.x8 = x + 1#64)
    (h2 : Region (x + 1#64) [x] s) : ∃ v : Word, s.getReg Reg.x8 = v ∧ Region v [x] s := by
  generalize_reg v : Reg.x8
  exact ⟨v, h, h2⟩

example (sp : Word) (x y z : Word) (s : MachineState) (h : Region (sp + 8#64) [x + 1#64, y, z] s) :
    ∃ a b : Word, Region (sp + 8#64) [x + 1#64, a, b] s := by
  generalize_cells a b : (sp + 16#64)
  exact ⟨a, b, h⟩

syntax (name := clearJunkRegions) "clear_junk_regions" : tactic

/-- Clears the `Region b (contents t b n) t` facts a previous run left (a block some callee's
frame covered, now of unknown contents), so a fresh statement of the block can take their place. -/
@[tactic clearJunkRegions] def evalClearJunkRegions : Tactic := fun _ => withMainContext do
  let mut fvs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOfArity ``MachineChecked.RiscV.Sym.Region 3 do continue
    if (ty.getAppArgs[1]!).isAppOfArity ``MachineChecked.RiscV.Sym.contents 3 then fvs := fvs.push d.fvarId
  let g ← getMainGoal
  replaceMainGoal [← g.tryClearMany fvs]

example (b : Word) (s : MachineState) (_h : Region b (contents s b 3) s) (h2 : Region b [b] s) :
    Region b [b] s := by
  clear_junk_regions
  exact h2

/-- A check of the tactic: two cells named, the region restated over them. -/
example (base : Word) (x y z : Word) (s : MachineState) (h : Region base [x + 1#64, y, z] s) :
    ∃ a b : Word, Region base [a, b, z] s := by
  generalize_cells a b : base
  exact ⟨a, b, h⟩


/-- `region_at b in s as h`: rename the `Region b _ s` hypothesis to `h`, found by its base and
state syntactically (no unification of the contents, which for model-valued regions is expensive).
`s` may be `_`: the most recent `Region b _ _` then. -/
syntax (name := regionAt) "region_at " term " in " term " as " ident : tactic

@[tactic regionAt] def evalRegionAt : Tactic := fun stx => withMainContext do
  let b ← instantiateMVars (← elabTerm stx[1] none)
  let st ← instantiateMVars (← elabTerm stx[3] none)
  let mut found : Option FVarId := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``MachineChecked.RiscV.Sym.Region 3 && ty.getAppArgs[0]! == b &&
        (st.isMVar || ty.getAppArgs[2]! == st) then
      found := some d.fvarId
  match found with
  | none =>
    let mut bases : Array MessageData := #[]
    for d in ← getLCtx do
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``MachineChecked.RiscV.Sym.Region 3 then bases := bases.push m!"{d.userName}: {ty.getAppArgs[0]!} @ {ty.getAppArgs[2]!}"
    throwError "region_at: no `Region {b} _ {st}` hypothesis; regions:{indentD (MessageData.joinSep bases.toList "\n")}"
  | some f => replaceMainGoal [← (← getMainGoal).rename f stx[5].getId]

end MachineChecked.RiscV.Sym
