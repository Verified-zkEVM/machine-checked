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
import AsmVerif.RiscV.Exec.Arith

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

def isLoadName (n : Name) : Bool :=
  n == ``Instr.LB || n == ``Instr.LBU || n == ``Instr.LH || n == ``Instr.LHU ||
  n == ``Instr.LW || n == ``Instr.LWU || n == ``Instr.LD

def isBranchName (n : Name) : Bool :=
  n == ``Instr.BEQ || n == ``Instr.BNE || n == ``Instr.BLT || n == ``Instr.BGE ||
  n == ``Instr.BLTU || n == ``Instr.BGEU

/-- The fetch proof for the instruction `iS` at the goal's state. -/
def fetchStx (code : Term) : TacticM Term :=
  `(fetchLit $code (by
        simp only [MachineState.code_setReg, MachineState.code_setPC,
          MachineState.code_setByte, MachineState.code_setMem, MachineState.code_setHalfword,
          MachineState.code_setWord32]
        assumption) (pc_setPC _ _) rfl (by decide))

/-- A load whose value is not needed: the destination takes a fresh value. -/
def runHavoc (code : Term) (one : Bool) (iS : Term) : TacticM Unit := do
  let lem := if one then mkIdent ``safe_load1 else mkIdent ``safe_load
  let f ← fetchStx code
  evalTactic (← `(tactic| refine $lem (i := $iS) $f rfl ?_))
  evalTactic (← `(tactic| intro _))
  evalTactic (← `(tactic| simp only [pc_setPC, setPC_setPC, setReg_setPC, setMem_setPC,
    setByte_setPC, setHalfword_setPC, setWord32_setPC, setReg_setReg_same]))
  try evalTactic (← `(tactic| simp only [BitVec.reduceAdd])) catch _ => pure ()

def runStep (code : Term) (one : Bool) (havoc : Bool := false) : TacticM Unit := do
  let codeE ← elabTerm code none
  let i ← instrAtGoal codeE
  let iS ← Term.exprToSyntax i
  if havoc && (i.getAppFn.constName?.map isLoadName).getD false then
    return ← runHavoc code one iS
  let lem := if one then mkIdent ``safe_step1 else mkIdent ``safe_step
  evalTactic (← `(tactic|
    refine $lem (i := $iS) (fetchLit $code (by
        simp only [MachineState.code_setReg, MachineState.code_setPC,
          MachineState.code_setByte, MachineState.code_setMem, MachineState.code_setHalfword,
          MachineState.code_setWord32]
        assumption) (pc_setPC _ _) rfl (by decide))
      (by decide) (by decide) (by intro _ _ h; cases h) ?_))
  -- The memory check is not kept: its state term is large and proofs here do not use it.
  evalTactic (← `(tactic| intro hm; clear hm))
  let isBranch := (i.getAppFn.constName?.map isBranchName).getD false
  -- In stages: `simp` folding `pc + imm` while it rewrites the `pc` builds a proof the
  -- kernel cannot check.
  let simpStep ← `(tactic| (
    simp only [pc_setPC, setPC_setPC, setReg_setPC, setMem_setPC, setByte_setPC,
      setHalfword_setPC, setWord32_setPC, setReg_setReg_same,
      AsmVerif.RiscV.Frame.setReg_x0, getReg_setReg,
      MachineState.getReg_setPC, getReg_setByte, getReg_setWord32, getReg_setHalfword,
      AsmVerif.RiscV.Frame.getReg_setMem, getReg_x0,
      reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false, and_true, and_false,
      false_and, true_and, if_true, if_false]
    try simp only [signExtend12, signExtend13, BitVec.reduceSignExtend]
    try simp only [BitVec.reduceAdd, BitVec.add_zero, BitVec.reduceAnd, BitVec.reduceNot]))
  let simpHb ← `(tactic|
    simp only [pc_setPC, setPC_setPC, setReg_setPC, setMem_setPC, setByte_setPC,
      setHalfword_setPC, setWord32_setPC, setReg_setReg_same,
      AsmVerif.RiscV.Frame.setReg_x0, getReg_setReg,
      MachineState.getReg_setPC, getReg_setByte, getReg_setWord32, getReg_setHalfword,
      AsmVerif.RiscV.Frame.getReg_setMem, getReg_x0,
      reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false, and_true, and_false,
      false_and, true_and, if_true, if_false]
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

/-- `xrun code`: step straight-line instructions, loads with fresh values, up to (not
    including) the next branch, jump or `ecall`, or the pc given by `to p`. Stops at a
    branch so the proof can split it with `xstep`. `xrun1` spends one unit of budget on its
    first step. -/
syntax (name := xrunTac) "xrun " term:max (" to " term:max)? : tactic
syntax (name := xrun1Tac) "xrun1 " term:max (" to " term:max)? : tactic

/-- The goal state's pc, if it is a literal. -/
def goalPC? : TacticM (Option Nat) := do
  let ty ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  match ty.getAppFnArgs with
  | (``SafeN, #[_, _, x]) => bvLit? (← mkAppM ``MachineState.pc #[x])
  | _ => return none

partial def runStraight (code : Term) (stop : Option Nat) (one : Bool) : TacticM Unit := do
  let codeE ← elabTerm code none
  let some i ← (try some <$> instrAtGoal codeE catch _ => pure none) | return
  let some n := i.getAppFn.constName? | return
  if let some p := stop then
    if (← goalPC?) == some p then return
  if isBranchName n || n == ``Instr.JAL || n == ``Instr.JALR || n == ``Instr.ECALL ||
     n == ``Instr.EBREAK then return
  runStep code one (havoc := true)
  runStraight code stop false

def stopOf (stx : Syntax) : TacticM (Option Nat) := do
  if stx[2].isNone then return none
  let e ← elabTerm stx[2][1] (some (mkApp (mkConst ``BitVec) (mkNatLit 64)))
  bvLit? e

@[tactic xrunTac] def evalXrun : Tactic := fun stx => do
  runStraight ⟨stx[1]⟩ (← stopOf stx) false

@[tactic xrun1Tac] def evalXrun1 : Tactic := fun stx => do
  runStraight ⟨stx[1]⟩ (← stopOf stx) true

/-- `xload code`: one load with a fresh value. -/
syntax (name := xloadTac) "xload " term:max : tactic
@[tactic xloadTac] def evalXload : Tactic := fun stx => runStep ⟨stx[1]⟩ false (havoc := true)

/-- Discharge a `Frame` goal through register writes and `pc` updates, down to a hypothesis;
    each store leaves its footprint obligation as a goal, in program order. -/
macro "xframe" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine Frame.setPC ?_ _ |
    with_reducible refine Frame.setReg ?_ (by decide) (by decide) _ |
    with_reducible refine Frame.setByte ?_ ?_ _ | with_reducible refine Frame.setMem ?_ ?_ _ |
    with_reducible refine Frame.setWord32 ?_ ?_ _ |
    with_reducible refine Frame.setHalfword ?_ ?_ _))

/-- Resolve register reads through a state's writes. -/
macro "xregs" : tactic => `(tactic|
  simp only [getReg_setReg, MachineState.getReg_setPC, getReg_setByte, getReg_setWord32,
    getReg_setHalfword, AsmVerif.RiscV.Frame.getReg_setMem, AsmVerif.RiscV.Frame.setReg_x0,
    reduceCtorEq, ne_eq, not_false_eq_true, not_true_eq_false, and_true, and_false, false_and,
    true_and, if_true, if_false])

/-- `xret code hk`: a `ret` at the goal's state, to the continuation `hk`; leaves the frame
    as a goal. -/
syntax (name := xretTac) "xret " term:max term:max : tactic
@[tactic xretTac] def evalXret : Tactic := fun stx => do
  let code : Term := ⟨stx[1]⟩
  let hk : Term := ⟨stx[2]⟩
  let codeTy ← whnfR (← inferType (← elabTerm code none))
  let cE ← match codeTy.getAppFnArgs with
    | (``CodeAt, #[_, c]) => pure c
    | _ => throwError "xret: expected `CodeAt f C`"
  let cS ← Term.exprToSyntax cE
  let f ← fetchStx code
  evalTactic (← `(tactic| refine safe_ret (C := $cS) (by rfl) ?_ $f $hk))

end AsmVerif.RiscV.Exec
