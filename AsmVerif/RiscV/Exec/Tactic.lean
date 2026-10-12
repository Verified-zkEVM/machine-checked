/-
  AsmVerif.RiscV.Exec.Tactic

  `xstep code` executes the instruction at the current state of a `SafeN` goal.

  The goal must be `SafeN k P x` where `x`'s program counter reduces to a literal (a state
  built by `setPC`, or `s.setPC p` from `setPC_self` at a cut point), and `code : CodeAt f C`
  for the function `f` being executed. The tactic reads the instruction at that pc from
  `f.prog` syntactically, so the kernel checks the fetch by evaluating one list index, and
  the instruction's immediates stay literals that `simp` can fold.

  `xstep1 code` is the same step, spending one unit of budget (`SafeN (k + 1)`).

  After the step the continuation's goal is `SafeN k P (execInstrBr x i)`, unfolded and
  simplified: register reads through the new writes are resolved, immediates folded. A
  branch leaves an `if` for the proof to split.
-/

import Lean
import AsmVerif.RiscV.Exec.Basic

namespace AsmVerif.RiscV.Exec

open Lean Meta Elab Tactic
open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame AsmVerif.RiscV.Check

/-- The natural number a closed `BitVec` literal denotes. -/
def bvLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfD e
  match ← getBitVecValue? e with
  | some ⟨_, v⟩ => return some v.toNat
  | none =>
    -- `BitVec.ofNat w n` / `{ toFin := ⟨n, _⟩ }` after unfolding
    match e.getAppFnArgs with
    | (``BitVec.ofNat, #[_, n]) => return (← evalNat (← whnfD n)).map id
    | (``BitVec.ofFin, #[_, f]) =>
      let f ← whnfD f
      match f.getAppFnArgs with
      | (``Fin.mk, #[_, n, _]) => evalNat (← whnfD n)
      | _ => return none
    | _ => return none

/-- The `j`-th element of a list given as a literal (after unfolding definitions). -/
partial def listNth? (l : Expr) (j : Nat) : MetaM (Option Expr) := do
  let l ← whnfD l
  match l.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => if j = 0 then return some h else listNth? t (j - 1)
  | _ => return none

/-- The instruction at the goal state's pc, as the literal term in the function's program. -/
def instrAtGoal (code : Expr) : TacticM Expr := do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ty ← whnfR ty
  let x ← match ty.getAppFnArgs with
    | (``SafeN, #[_, _, x]) => pure x
    | _ => throwError "xstep: goal is not `SafeN k P x`"
  let codeTy ← whnfR (← inferType code)
  let f ← match codeTy.getAppFnArgs with
    | (``CodeAt, #[f, _]) => pure f
    | _ => throwError "xstep: expected `CodeAt f C`, got {codeTy}"
  let some pc ← bvLit? (← mkAppM ``MachineState.pc #[x])
    | throwError "xstep: the state's pc is not a literal"
  let some base ← bvLit? (← mkAppM ``Fn.base #[f])
    | throwError "xstep: the function's base is not a literal"
  let d := (pc + 2 ^ 64 - base) % 2 ^ 64
  unless d % 4 = 0 do throwError "xstep: pc {pc} is not an instruction of the function"
  let some oi ← listNth? (← mkAppM ``Fn.prog #[f]) (d / 4)
    | throwError "xstep: pc {pc} is outside the function"
  let oi ← whnfR oi
  match oi.getAppFnArgs with
  | (``Option.some, #[_, i]) => pure i
  | _ => throwError "xstep: no instruction decodes at pc {pc}"

syntax (name := xstepTac) "xstep " term:max : tactic
syntax (name := xstep1Tac) "xstep1 " term:max : tactic

def runStep (code : Term) (one : Bool) : TacticM Unit := do
  let codeE ← elabTerm code none
  let i ← instrAtGoal codeE
  let iS ← Term.exprToSyntax i
  let lem := if one then mkIdent ``safe_step1 else mkIdent ``safe_step
  evalTactic (← `(tactic|
    refine $lem (i := $iS) (fetchLit $code (by
        simp only [MachineState.code_setReg, MachineState.code_setPC,
          MachineState.code_setByte, MachineState.code_setMem, MachineState.code_setHalfword,
          MachineState.code_setWord32]
        assumption) (pc_setPC _ _) rfl (by decide))
      (by decide) (by decide) (by intro _ _ h; cases h) ?_))
  evalTactic (← `(tactic| intro _))
  let isBranch := match i.getAppFn.constName? with
    | some n => n == ``Instr.BEQ || n == ``Instr.BNE || n == ``Instr.BLT || n == ``Instr.BGE ||
        n == ``Instr.BLTU || n == ``Instr.BGEU
    | none => false
  -- In stages: `simp` folding `pc + imm` while it rewrites the `pc` builds a proof the
  -- kernel cannot check.
  let simpStep ← `(tactic| (
    simp only [pc_setPC, getReg_setReg, MachineState.getReg_setPC, getReg_setByte, AsmVerif.RiscV.Frame.getReg_setMem, getReg_x0,
      reduceCtorEq, ne_eq, not_false_eq_true, and_true, and_false, if_true, if_false]
    try simp only [signExtend12, signExtend13, BitVec.reduceSignExtend]
    try simp only [BitVec.reduceAdd, BitVec.add_zero]))
  let simpHb ← `(tactic|
    simp only [pc_setPC, getReg_setReg, MachineState.getReg_setPC, getReg_setByte, AsmVerif.RiscV.Frame.getReg_setMem, getReg_x0,
      reduceCtorEq, ne_eq, not_false_eq_true, and_true, and_false, if_true, if_false]
      at $(mkIdent `hb):ident)
  evalTactic (← `(tactic| dsimp only [execInstrBr]))
  if isBranch then
    -- Split before simplifying: `simp` under the branch's `if` builds a proof the kernel
    -- cannot check. The taken branch comes first; its condition is `hb`.
    focus do
      evalTactic (← `(tactic| split))
      let gs ← getGoals
      let mut out := []
      for g in gs do
        setGoals [g]
        evalTactic (← `(tactic| rename_i $(mkIdent `hb):ident))
        try evalTactic simpHb catch _ => pure ()
        try evalTactic simpStep catch _ => pure ()
        out := out ++ (← getGoals)
      setGoals out
  else
    try evalTactic simpStep catch _ => pure ()

@[tactic xstepTac] def evalXstep : Tactic := fun stx => runStep ⟨stx[1]⟩ false
@[tactic xstep1Tac] def evalXstep1 : Tactic := fun stx => runStep ⟨stx[1]⟩ true

end AsmVerif.RiscV.Exec
