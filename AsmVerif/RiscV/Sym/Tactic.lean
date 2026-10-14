/-
  AsmVerif.RiscV.Sym.Sym

  The symbolic executor: `sym_exec`.

  The goal is `Safe P s` (`AsmVerif.RiscV.Sym.Safe`). The executor steps the machine from `s`,
  one instruction at a time, replacing the goal by `Safe P s'` for the
  successor state `s'` and deriving facts about `s'` from the facts about `s`:
  its pc, the registers it knows, the memory regions it tracks, the code map,
  the store invariant, the frame (`Unchanged`), the private input. The previous
  state's facts are cleared, so the context stays a fixed size.

  Beyond straight-line code it

  * splits on a branch it cannot decide (`Safe.cases`), exploring both arms;
  * applies a function specification at a call (`sym_exec [f_spec, …]`),
    discharging its preconditions from the facts and reading its
    postcondition back as facts about the returned state;
  * executes the accelerator `ECALL`s (`Safe.uint256Mul` & co.), `COMMIT`,
    `COMMIT_DEFERRED_PROOFS`, and closes a `HALT` with a literal nonzero exit
    code (`Safe.reject`).

  It stops, leaving the goal for the user, at a symbolic jump target (a
  return), a `HALT` it cannot decide, an address no `CodeAt` fact covers, a
  memory access outside every region, or the step budget.

  Values are kept in the normal form `atom + c#64` (or a literal); a computed
  value that is not of that form and is large is named by a fresh atom (with its
  defining equation `vₖ_def` kept in the context), so terms never grow.

  ## Facts it reads about the initial state `s`

  * `s.pc = <literal>`, `s.getReg .xᵢ = e`
  * `Region b vs s` with `RegionOk lo hi b n`; `vs` a literal or a list
    variable with a `vs.length = n` fact
  * `Disjoint b₁ n₁ b₂ n₂`
  * `CodeAt base prog s`, `CodeWithin lo hi s`
  * `Unchanged W s₀ s` (else `Unchanged [] s s`); stores must land in `W`
  * `s.privateInput = e`
  * `StackOk L room sp`, unpacked into `Nat` facts for `omega`; `L : Layout` (also
    through `RoImage L s` or a `RegionOk L.roBase …` fact) gives the executor the guest's
    text window, read-only segment and stack top
  * any other hypothesis is available to the branch and side-condition
    provers (`simp` with equations, `omega` with `Nat` facts).
-/

import Lean
import AsmVerif.RiscV.Image
import AsmVerif.RiscV.Sym.Regs
import AsmVerif.RiscV.Sym.Ro
import AsmVerif.RiscV.Sym.ByteFold

namespace AsmVerif.RiscV.Sym

/-- `getReg .x0 = 0`, for the executor's register table. -/
theorem getReg_x0 (s : RiscvZkvm.Rv64.MachineState) : s.getReg .x0 = 0 := rfl

end AsmVerif.RiscV.Sym

open Lean Meta Elab Tactic

namespace AsmVerif.RiscV.Sym.Meta

open RiscvZkvm.Rv64

initialize registerTraceClass `AsmVerif.sym
initialize registerTraceClass `AsmVerif.sym.size
initialize registerTraceClass `AsmVerif.sym.time

/-! ## Normal forms -/

/-- `atom + c` with `c < 2^64`; `atom = none` is a literal. -/
structure Lin where
  atom : Option Expr
  c : Nat
  deriving Inhabited

def two64 : Nat := 2 ^ 64

def Lin.lit (c : Nat) : Lin := ⟨none, c % two64⟩

def Lin.addC (l : Lin) (k : Nat) : Lin := ⟨l.atom, (l.c + k) % two64⟩

def Lin.sameAtom (a b : Lin) : Bool :=
  match a.atom, b.atom with
  | none, none => true
  | some x, some y => x == y
  | _, _ => false

/-- Sign extension of a `bits`-bit value to 64 bits, as a `Nat` mod 2^64. -/
def sext (bits : Nat) (v : Nat) : Nat :=
  if v < 2 ^ (bits - 1) then v else two64 - (2 ^ bits - v)

/-- `getBitVecValue?`, looking through definitions (`fBase := 0x…#64`) one
    unfolding at a time, without reducing the literal itself. -/
partial def bvValue? (e : Expr) : MetaM (Option ((n : Nat) × BitVec n)) := do
  let e ← instantiateMVars e
  match ← getBitVecValue? e with
  | some v => return some v
  | none =>
    match ← unfoldDefinition? e with
    | some e' => bvValue? e'
    | none => return none

/-- Read a `Word` literal. -/
def litValue? (e : Expr) : MetaM (Option Nat) := do
  match ← bvValue? e with
  | some ⟨64, v⟩ => return some v.toNat
  | _ => return none

def wordTy : Expr := mkApp (mkConst ``BitVec) (mkNatLit 64)
def msTy : Expr := mkConst ``MachineState
def natTy : Expr := mkConst ``Nat

def mkWordLit (n : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit (n % two64))

def mkAdd (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a, b]
def mkMulN (a b : Expr) : MetaM Expr := mkAppM ``HMul.hMul #[a, b]
def mkAddN (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a, b]
def mkModN (a b : Expr) : MetaM Expr := mkAppM ``HMod.hMod #[a, b]

/-- The normal form of a `Word` expression. -/
partial def normLin (e : Expr) : MetaM Lin := do
  let e ← instantiateMVars e
  if let some v ← litValue? e then return Lin.lit v
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    let la ← normLin a
    let lb ← normLin b
    match la.atom, lb.atom with
    | _, none => return la.addC lb.c
    | none, _ => return lb.addC la.c
    | _, _ => return ⟨some e, 0⟩
  | HSub.hSub _ _ _ _ a b =>
    let la ← normLin a
    let lb ← normLin b
    match la.atom, lb.atom with
    | none, none => return Lin.lit (la.c + two64 - lb.c)
    | _, none => return la.addC (two64 - lb.c)
    | _, _ => return ⟨some e, 0⟩
  | signExtend12 imm =>
    match ← getBitVecValue? imm with
    | some ⟨12, v⟩ => return Lin.lit (sext 12 v.toNat)
    | _ => return ⟨some e, 0⟩
  | signExtend13 imm =>
    match ← getBitVecValue? imm with
    | some ⟨13, v⟩ => return Lin.lit (sext 13 v.toNat)
    | _ => return ⟨some e, 0⟩
  | signExtend21 imm =>
    match ← getBitVecValue? imm with
    | some ⟨21, v⟩ => return Lin.lit (sext 21 v.toNat)
    | _ => return ⟨some e, 0⟩
  | _ => return ⟨some e, 0⟩

def Lin.toExpr (l : Lin) : MetaM Expr :=
  match l.atom with
  | none => pure (mkWordLit l.c)
  | some a => if l.c == 0 then pure a else mkAdd a (mkWordLit l.c)

/-- Distinct-subterm count, for diagnostics. -/
def dagSize (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet UInt64 := {}
  let mut stack := #[e]
  let mut n : Nat := 0
  while h : stack.size > 0 do
    let e := stack.back
    stack := stack.pop
    if seen.contains e.hash then continue
    seen := seen.insert e.hash
    n := n + 1
    match e with
    | .app f a => stack := (stack.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => stack := (stack.push t).push b
    | .letE _ t v b _ => stack := ((stack.push t).push v).push b
    | .mdata _ b | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return n

/-- Node count, capped. -/
partial def exprSize (e : Expr) (cap : Nat := 200) : Nat :=
  go e 0
where
  go (e : Expr) (acc : Nat) : Nat :=
    if acc ≥ cap then acc else
    match e with
    | .app f a => go a (go f (acc + 1))
    | .lam _ t b _ | .forallE _ t b _ => go b (go t (acc + 1))
    | .letE _ t v b _ => go b (go v (go t (acc + 1)))
    | .mdata _ b | .proj _ _ b => go b (acc + 1)
    | _ => acc + 1

/-! ## Instruction decoding at the meta level -/

inductive Op where
  | alu (rd : Nat)
  | load (rd rs1 : Nat) (off : Nat) (width : Nat) (signed : Bool)
  | store (rs1 rs2 : Nat) (off : Nat) (width : Nat)
  | branch (rs1 rs2 : Nat) (off : Nat) (kind : String)
  | jal (rd : Nat) (off : Nat)
  | jalr (rd rs1 : Nat) (off : Nat)
  | ecall | ebreak | fence | other
  deriving Repr, Inhabited

def regIdx (e : Expr) : MetaM Nat := do
  let e ← whnfD e
  match e.constName? with
  | some n =>
    let s := n.getString!
    if s.startsWith "x" then
      match (s.drop 1).toString.toNat? with
      | some i => return i
      | none => throwError "regIdx: {e}"
    else throwError "regIdx: {e}"
  | none => throwError "regIdx: not a register {e}"

def bvLit (e : Expr) : MetaM Nat := do
  match ← bvValue? e with
  | some ⟨_, v⟩ => return v.toNat
  | none => throwError "bvLit: not a literal {e}"

def classify (ins : Expr) : MetaM Op := do
  let ins ← whnfD ins
  let f := ins.getAppFn.constName!.getString!
  let args := ins.getAppArgs
  let r (i : Nat) := regIdx args[i]!
  let l (i : Nat) := bvLit args[i]!
  match f with
  | "LD"  => return .load (← r 0) (← r 1) (← l 2) 8 false
  | "LW"  => return .load (← r 0) (← r 1) (← l 2) 4 true
  | "LWU" => return .load (← r 0) (← r 1) (← l 2) 4 false
  | "LH"  => return .load (← r 0) (← r 1) (← l 2) 2 true
  | "LHU" => return .load (← r 0) (← r 1) (← l 2) 2 false
  | "LB"  => return .load (← r 0) (← r 1) (← l 2) 1 true
  | "LBU" => return .load (← r 0) (← r 1) (← l 2) 1 false
  | "SD"  => return .store (← r 0) (← r 1) (← l 2) 8
  | "SW"  => return .store (← r 0) (← r 1) (← l 2) 4
  | "SH"  => return .store (← r 0) (← r 1) (← l 2) 2
  | "SB"  => return .store (← r 0) (← r 1) (← l 2) 1
  | "BEQ" | "BNE" | "BLT" | "BGE" | "BLTU" | "BGEU" =>
    return .branch (← r 0) (← r 1) (← l 2) f
  | "JAL" => return .jal (← r 0) (← l 1)
  | "JALR" => return .jalr (← r 0) (← r 1) (← l 2)
  | "ECALL" => return .ecall
  | "EBREAK" => return .ebreak
  | "FENCE" | "NOP" => return .fence
  | "CSRS" => return .other
  | _ => return .alu (← r 0)   -- every remaining constructor writes `rd` first

/-! ## Executor state -/

structure RegFact where
  val : Expr      -- normal form
  lin : Lin
  proof : Expr    -- : s.getReg .xᵢ = val
  deriving Inhabited

structure RegionInfo where
  base : Expr
  baseLin : Lin
  n : Nat
  cells : Array Expr
  listExpr : Expr
  hyp : Expr      -- : Region base listExpr s   (a term, derived from `hypM`)
  hypM : Expr     -- : Region base listExpr sM  (a hypothesis)
  ok : Expr       -- : RegionOk lo hi base n, or `noRegionOk` when there is none
  w : Option (Nat × Nat)  -- (index in W, cell offset within that entry), if writable
  /-- A read-only region disjoint from all of `W`: `hypM` is a fact about `s₀`
      that is never transported; a use goes through `Unchanged` and `outW`. -/
  outW : Option Expr := none   -- : ∀ r ∈ W, Disjoint base n r.1 r.2
  /-- `base.toNat + 8 n ≤ roBase ∨ roBase + roBytes ≤ base.toNat`, once proved. -/
  roOut : Option Expr := none
  /-- An *opaque* region: `listExpr` is a list variable, kept unexpanded (`cells` is empty),
      with `lenPf : listExpr.length = n`. Read only, by indexed loads (`symbolicLoad`);
      never stored to, and never located by a concrete offset. For large tables. -/
  lenPf : Option Expr := none
  deriving Inhabited

structure WEntry where
  base : Expr
  baseLin : Lin
  n : Nat
  nw : Expr       -- : base.toNat + 8 * n ≤ 2 ^ 64
  deriving Inhabited

structure CodeInfo where
  base : Nat
  baseExpr : Expr
  progExpr : Expr
  prog : Array (Option Expr)   -- decoded instruction terms
  hlen : Expr                  -- : prog.length = n
  hyp : Expr                   -- : CodeAt base prog s   (a term)
  hyp0 : Expr                  -- : CodeAt base prog s₀  (a hypothesis)
  deriving Inhabited

/-- Marks a region given without a `RegionOk` fact: it may be read by an
    accelerator or passed to a callee, but not loaded or stored through. -/
def noRegionOk : Expr := mkConst `AsmVerif.RiscV.Sym.Meta.noRegionOk

def RegionInfo.okE (R : RegionInfo) : MetaM Expr := do
  if R.ok == noRegionOk then
    throwError "sym_exec: region at {R.base} has no `RegionOk` fact"
  return R.ok

/-- A function specification the executor can apply at a call. -/
structure SpecInfo where
  name : Name
  entry : Nat
  /-- A local hypothesis used as a specification (an induction hypothesis, or
      a fact assumed about code not yet proved), rather than a constant. -/
  term? : Option Expr := none
  deriving Inhabited

/-- The layout the hypotheses name, with its constants evaluated. -/
structure LayoutInfo where
  L : Expr
  roBase : Nat
  roBytes : Nat
  roChunks : Nat
  stackTop : Nat
  textLo : Nat
  textHi : Nat
  deriving Inhabited

def LayoutInfo.roBaseE (li : LayoutInfo) : Expr := mkApp (mkConst ``AsmVerif.RiscV.Sym.Layout.roBase) li.L
def LayoutInfo.roBytesE (li : LayoutInfo) : Expr := mkApp (mkConst ``AsmVerif.RiscV.Sym.Layout.roBytes) li.L

/-- The executor's state. Only a handful of facts are hypotheses, and they
    are chained so that a step adds a constant number of them:

    * `hregs : Regs s regList` -- the whole register file;
    * `hmem : s.mem = sM.mem`  -- memory since the last write, at `sM`;
      region facts and the frame are hypotheses about `sM`;
    * `hcode : s.code = s₀.code` -- code facts are hypotheses about `s₀`;
    * `hpc`, and `hpriv` when the private input is known.

    The per-register, per-region and per-code facts the steps use (`regs`,
    `regions[·].hyp`, `codes[·].hyp`, `hcw`, `hunch`) are *terms* built from
    these by `St.refresh`; only the ones a step uses end up in the proof. -/
structure St where
  s0 : Expr
  s : Expr
  pc : Option Nat                  -- `none`: symbolic
  pcE : Expr
  hpc : Expr                       -- : s.pc = pcE
  regs : Array (Option RegFact)    -- 32; `proof` is a term from `hregs`
  regList : Expr
  hregs : Expr                     -- : Regs s regList
  sM : Expr
  hmem : Expr                      -- : s.mem = sM.mem
  regions : Array RegionInfo
  codes : Array CodeInfo
  hcode : Expr                     -- : s.code = s₀.code
  hcw0 : Expr                      -- : CodeWithin lo hi s₀
  hcw : Expr                       -- : CodeWithin lo hi s
  k : Nat
  W : Expr                         -- : List (Word × Nat)
  wEntries : Array WEntry
  hunchM : Expr                    -- : Unchanged W s₀ sM
  hunch : Expr                     -- : Unchanged W s₀ s
  hroM : Option Expr := none       -- : RoImage sM
  okFacts : Bool := false          -- the `RegionOk` facts' bounds have been added for `omega`
  hro : Option Expr := none        -- : RoImage L s
  layout : Option LayoutInfo := none
  priv : Option (Expr × Expr)      -- (value, proof : s.privateInput = value)
  disj : Array (Expr × Expr × Expr × Expr × Expr)  -- (b₁, n₁, b₂, n₂, proof)
  /-- Pairs `omega` could not show disjoint (a buffer inside the heap entry): not retried. -/
  disjFail : Array (Expr × Nat × Expr × Nat) := #[]
  /-- Regions placed in a write-set entry by bounds (`coverEntry`): (base, cells, entry, proof). -/
  covers : Array (Expr × Nat × Nat × Expr) := #[]
  toClear : Array FVarId
  pureFacts : Array Expr           -- equations and negations usable by `simp`
  /-- A `Nat` comparison a specification's precondition needed and no fact decided: the
      executor splits on it when no specification at the pc applies. -/
  undecided : Option Expr := none
  /-- Several specifications compete at this pc: a `Nat` comparison precondition is tried
      cheaply (a hypothesis, `omega` over its cluster) and otherwise left undecided. -/
  multiSpec : Bool := false
  specs : Array SpecInfo
  stops : Array Nat
  deriving Inhabited

def mkReg (i : Nat) : Expr := mkConst (`RiscvZkvm.Rv64.Reg ++ Name.mkSimple s!"x{i}")
def mkGetReg (s : Expr) (i : Nat) : Expr := mkApp2 (mkConst ``MachineState.getReg) s (mkReg i)
def mkPc (s : Expr) : Expr := mkApp (mkConst ``MachineState.pc) s
def mkEqW (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) wordTy a b
def mkEqMS (a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) msTy a b
def mkSetPC (s p : Expr) : Expr := mkApp2 (mkConst ``MachineState.setPC) s p
def mkSetReg (s : Expr) (i : Nat) (v : Expr) : Expr := mkApp3 (mkConst ``MachineState.setReg) s (mkReg i) v
def mkSetMem (s a v : Expr) : Expr := mkApp3 (mkConst ``MachineState.setMem) s a v
def mkSafe (P s : Expr) : Expr := mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Safe) P s

def natLtE (a b : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) natTy (mkConst ``instLTNat) a b
def natLeE (a b : Expr) : Expr := mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat) a b

def St.layoutE (st : St) : MetaM LayoutInfo := do
  let some li := st.layout
    | throwError "sym_exec: no `Layout` among the hypotheses (`RoImage L s`, `StackOk L …`, `RegionOk L.roBase …`)"
  return li

/-- `ext ≤ L.roBase ∨ L.roBase + L.roBytes ≤ toN`: a block off the read-only segment. -/
def roOutProp (li : LayoutInfo) (ext toN : Expr) : MetaM Expr := do
  mkAppM ``Or #[natLeE ext li.roBaseE, natLeE (← mkAppM ``HAdd.hAdd #[li.roBaseE, li.roBytesE]) toN]

/-- The layout's constants as equations (`hL_roBase : L.roBase = 0x…`, added by `initState`),
    for `simp` and `omega`. -/
def layoutRules : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if d.userName.toString.startsWith "hL_" then out := out.push d.toExpr
  return out

def layoutRuleIdents : MetaM (Array Name) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if d.userName.toString.startsWith "hL_" then out := out.push d.userName
  return out

def natLt (i n : Nat) : MetaM Expr := mkDecideProof (natLtE (mkNatLit i) (mkNatLit n))
def natLe (i n : Nat) : MetaM Expr := mkDecideProof (natLeE (mkNatLit i) (mkNatLit n))
def natEq (a b : Expr) : MetaM Expr := mkDecideProof (mkApp3 (mkConst ``Eq [1]) natTy a b)

def listElems (e : Expr) : MetaM (Array Expr) := do
  let mut e ← whnfD e
  let mut out := #[]
  repeat
    match_expr e with
    | List.cons _ a t => out := out.push a.headBeta; e ← whnfD t
    | List.nil _ => break
    | _ => throwError "listElems: not a list literal {e}"
  return out

def mkListLit (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc) (mkApp (mkConst ``List.nil [0]) ty)

def listWordTy : Expr := mkApp (mkConst ``List [0]) wordTy

/-- A `rfl` proof carrying an explicit type. -/
def rflOf (ty : Expr) (rhs : Expr) : MetaM Expr := do
  let pf ← mkEqRefl rhs
  mkExpectedTypeHint pf ty

/-- Instantiate lemma `lem` so that its conclusion is `target`; remaining
    propositional arguments are discharged by `decide`. -/
def lemmaApp (lem : Name) (target : Expr) : MetaM Expr := do
  let c ← mkConstWithFreshMVarLevels lem
  let (mvs, _, concl) ← forallMetaTelescope (← inferType c)
  unless ← isDefEq concl target do
    throwError "lemmaApp {lem}: conclusion{indentExpr concl}\ndoes not match{indentExpr target}"
  for mv in mvs do
    if !(← mv.mvarId!.isAssigned) then
      let ty ← instantiateMVars (← inferType mv)
      if ← isProp ty then mv.mvarId!.assign (← mkDecideProof ty)
      else throwError "lemmaApp {lem}: unassigned argument of type {ty}"
  instantiateMVars (mkAppN c mvs)

/-- Rebuild the derived facts from the chained hypotheses. -/
def St.refresh (st : St) : MetaM St := do
  let s := st.s
  let mut regs := st.regs
  for i in [0:32] do
    if let some f := st.regs[i]! then
      let pf ← if i == 0 then pure (mkApp (mkConst ``AsmVerif.RiscV.Sym.getReg_x0) s) else do
        let hi ← natLt i 32
        let raw := mkAppN (mkConst ``AsmVerif.RiscV.Sym.Regs.get) #[s, st.regList, st.hregs, mkNatLit i, hi]
        mkExpectedTypeHint raw (mkEqW (mkGetReg s i) f.val)
      regs := regs.set! i (some { f with proof := pf })
  let sameM := st.sM == s
  let hunch ← if sameM then pure st.hunchM else mkAppM ``AsmVerif.RiscV.Sym.Unchanged.of_mem_eq' #[st.hunchM, st.hmem]
  let regions ← st.regions.mapM fun R => do
    if let some outW := R.outW then
      if st.s0 == s then return { R with hyp := R.hypM }
      let hn ← match R.lenPf with
        | some h => pure h
        | none => rflOf (← mkEq (← mkAppM ``List.length #[R.listExpr]) (mkNatLit R.n)) (mkNatLit R.n)
      return { R with hyp := ← mkAppM ``AsmVerif.RiscV.Sym.Region.of_unchanged' #[R.hypM, hunch, hn, outW] }
    if sameM then return { R with hyp := R.hypM }
    return { R with hyp := ← mkAppM ``AsmVerif.RiscV.Sym.Region.of_mem_eq' #[R.hypM, st.hmem] }
  let same0 := st.s0 == s
  let codes ← st.codes.mapM fun c => do
    if same0 then return { c with hyp := c.hyp0 }
    return { c with hyp := ← mkAppM ``AsmVerif.RiscV.Sym.codeAt_of_code_eq #[st.hcode, c.hyp0] }
  let hcw ← if same0 then pure st.hcw0 else mkAppM ``AsmVerif.RiscV.Sym.codeWithin_of_code_eq #[st.hcode, st.hcw0]
  let hro ← match st.hroM with
    | none => pure none
    | some h => if sameM then pure (some h) else some <$> mkAppM ``AsmVerif.RiscV.Sym.RoImage.of_mem_eq #[h, st.hmem]
  return { st with regs, regions, codes, hcw, hunch, hro }

/-- `Regs s l` with `l` a literal: the literal of `l.set i v`. -/
def regListSet (l : Expr) (i : Nat) (v : Expr) : MetaM Expr := do
  let cells ← listElems l
  return mkListLit wordTy (cells.set! i v)

/-! ## The goal -/

def goalParts (g : MVarId) : MetaM (Expr × Expr) := do
  let ty ← instantiateMVars (← g.getType)
  match_expr ty with
  | AsmVerif.RiscV.Sym.Safe P s => return (P, s)
  | _ => throwError "sym_exec: goal is not `Safe P s`:{indentExpr ty}"

/-- Replace the main goal `G` by `G` under new hypotheses `xᵢ : tᵢ`, closing the
    old goal with `(fun x₁ … xₙ => ?new) a₁ … aₙ`. The application is built
    with an explicit λ, not an assigned metavariable, so instantiation does not
    β-reduce it: each fact is checked once by the kernel and then referred to
    by name, instead of being copied into every use. -/
def introVia (names : Array Name) (types : Array Expr) (args : Array Expr) : TacticM (Array Expr) := do
  let g ← getMainGoal
  g.withContext do
    let target ← g.getType
    let rec go (i : Nat) (fvs : Array Expr) : MetaM (Expr × Array Expr × MVarId) := do
      if h : i < names.size then
        let ty := (types[i]!).instantiateRev fvs  -- types may mention earlier binders by fvar already
        withLocalDeclD names[i] ty fun x => go (i + 1) (fvs.push x)
      else
        let ng ← mkFreshExprSyntheticOpaqueMVar target
        let lam ← mkLambdaFVars fvs ng
        return (lam, fvs, ng.mvarId!)
    let (lam, fvs, ng) ← go 0 #[]
    g.assign (mkAppN lam args)
    replaceMainGoal [ng]
    return fvs

/-- Add a hypothesis to the main goal's context and return its fvar. -/
def addFact (name : Name) (type proof : Expr) : TacticM Expr := do
  let type ← instantiateMVars type
  let proof ← instantiateMVars proof
  let fvs ← introVia #[name] #[type] #[proof]
  return fvs[0]!

/-- The facts whose free variables are all still in the main goal's context
    (a cleared step hypothesis takes the facts built on it with it). -/
def liveFacts (fs : Array Expr) : TacticM (Array Expr) := withMainContext do
  let lctx ← getLCtx
  fs.filterM fun f => do
    let f ← instantiateMVars f
    return !f.hasAnyFVar (fun fv => !lctx.contains fv)

def clearFacts (fvs : Array FVarId) : TacticM Unit := do
  let mut g ← getMainGoal
  for fv in fvs.reverse do
    try g ← g.clear fv catch _ => pure ()
  replaceMainGoal [g]

/-- Replace the goal `Safe P s` by `Safe P s'` for a fresh `s'` with
    `hdef : shape = s'`. `close k` must prove `Safe P s` from
    `k : ∀ s', shape = s' → Safe P s'`. Returns `(s', hdef)`. -/
def advance (shape : Expr) (close : Expr → MetaM Expr) (k : Nat) : TacticM (Expr × Expr) := do
  let g ← getMainGoal
  g.withContext do
    let (P, _) ← goalParts g
    let kTy ← withLocalDeclD (Name.mkSimple s!"s_{k}") msTy fun s' => do
      withLocalDeclD (Name.mkSimple s!"hdef_{k}") (mkEqMS shape s') fun h => do
        mkForallFVars #[s', h] (mkSafe P s')
    let kMV ← mkFreshExprSyntheticOpaqueMVar kTy
    g.assign (← close kMV)
    let (fvs, g') ← kMV.mvarId!.introNP 2
    replaceMainGoal [g']
    return (mkFVar fvs[0]!, mkFVar fvs[1]!)

/-- Name `e : ty` by a fresh atom `a`, returning `(a, h : e = a)`. -/
def atomize (e ty : Expr) (nm : Name) : TacticM (Expr × Expr) := do
  let g ← getMainGoal
  let (heqTy, rflPf) ← g.withContext do
    let heqTy ← withLocalDeclD nm ty fun a => do mkLambdaFVars #[a] (← mkEq e a)
    pure (heqTy, ← mkEqRefl e)
  -- the equation's type mentions the atom: build it under the first binder
  let g ← getMainGoal
  g.withContext do
    let target ← g.getType
    withLocalDeclD nm ty fun a => do
      withLocalDeclD (nm.appendAfter "_def") (heqTy.beta #[a]) fun h => do
        let ng ← mkFreshExprSyntheticOpaqueMVar target
        let lam ← mkLambdaFVars #[a, h] ng
        g.assign (mkApp2 lam e rflPf)
        replaceMainGoal [ng.mvarId!]
        return (a, h)

/-! ## Simp-based rewriting -/

/-- The low three bits of a sum: an alignment test on a pointer plus an offset, folded through
    the pointer's own `&&& 7` fact (the right-hand side is a `Nat` the simprocs evaluate). -/
theorem and7_add (x c : BitVec 64) :
    (x + c) &&& 7#64 = BitVec.ofNat 64 (((x &&& 7#64).toNat + c.toNat) % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

def simpWith (e : Expr) (rules : Array Expr) (consts : Array Name) (dec : Bool := true) :
    MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for c in consts do
    let info ← getConstInfo c
    if info.isTheorem then thms ← thms.addConst c
    else thms ← thms.addDeclToUnfold c
  let mut i := 0
  for r in rules do
    thms ← thms.add (.other (Name.mkSimple s!"h{i}")) #[] r
    i := i + 1
  let ctx ← Simp.mkContext (config := { decide := dec, zeta := true })
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let simprocs ← Simp.getSimprocs
  let (r, _) ← simp e ctx #[simprocs]
  return r

/-- Lemmas that put `Word` arithmetic into `atom + lit` form. -/
def normLemmas : Array Name := #[
  ``BitVec.add_assoc, ``BitVec.sub_eq_add_neg, ``BitVec.add_zero, ``BitVec.zero_add,
  ``signExtend12, ``signExtend13, ``signExtend21, ``eq_self, ``ne_eq, ``not_true_eq_false,
  ``not_false_eq_true]

def proveBySimp (prop : Expr) (rules : Array Expr) (consts : Array Name) : MetaM (Option Expr) := do
  let r ← simpWith prop rules consts
  if r.expr.isConstOf ``True then
    let pf ← r.getProof
    return some (mkApp2 (mkConst ``of_eq_true) prop pf)
  else
    trace[AsmVerif.sym] "proveBySimp residual: {r.expr}"
    return none

def rewriteTo (e : Expr) (rules : Array Expr) (consts : Array Name) : MetaM (Expr × Expr) := do
  let r ← simpWith e rules consts
  let pf ← r.getProof
  return (r.expr, pf)

/-- The definitions `e = a` of the atoms in `x`, reversed (`a = e`), transitively:
    an address the executor has named by an atom, unfolded for matching. -/
partial def atomUnfoldRules (x : Expr) (limit : Nat := 8) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  let mut seen : Std.HashSet FVarId := {}
  let mut todo := (collectFVars {} x).fvarIds
  while !todo.isEmpty && out.size < limit do
    let fv := todo.back!
    todo := todo.pop
    if seen.contains fv then continue
    seen := seen.insert fv
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let some (_, e, a) := d.type.eq? | continue
      unless a.isFVar && a.fvarId! == fv do continue
      unless (d.userName.toString.endsWith "_def") do continue
      out := out.push (← mkEqSymm d.toExpr)
      todo := todo ++ (collectFVars {} e).fvarIds
  return out

/-- The `toNat` rewrites `omega`'s goals get; its auxiliary facts are put in the same form. -/
def omegaNormLemmas : Array Name := #[``AsmVerif.RiscV.Sym.add_ofNat_big, ``BitVec.toNat_add, ``BitVec.toNat_sub,
  ``BitVec.toNat_ofNat, ``BitVec.toNat_shiftLeft, ``BitVec.toNat_ushiftRight, ``BitVec.toNat_setWidth]

/-- A proof of `e.toNat < 2 ^ k` for a word `e`, with `k < 64`, built from its structure;
    atoms are read through their definitions (`fuel` of them). -/
partial def widthBound (e : Expr) (fuel : Nat := 16) : MetaM (Option (Nat × Expr)) := do
  let e := e.consumeMData
  let lit? : Option Nat ← match_expr e with
    | BitVec.ofNat w n => do
      if (← getNatValue? w) == some 64 then getNatValue? n else pure none
    | _ => pure none
  if let some n := lit? then
    let k := if n == 0 then 0 else Nat.log2 n + 1
    if k ≥ 64 then return none
    return some (k, ← mkAppM ``AsmVerif.RiscV.Sym.wb_lit #[mkNatLit n, mkNatLit k, ← mkDecideProof (natLtE (mkNatLit n) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit k]))])
  let widen (k m : Nat) (h : Expr) : MetaM Expr :=
    if k == m then pure h else do mkAppM ``AsmVerif.RiscV.Sym.wb_mono #[h, ← mkDecideProof (natLeE (mkNatLit k) (mkNatLit m))]
  match_expr e with
  | BitVec.setWidth m v x =>
    let some mv ← getNatValue? m | return none
    let some vv ← getNatValue? v | return none
    if vv != 64 || mv ≥ 64 then return none
    return some (mv, ← mkAppM ``AsmVerif.RiscV.Sym.wb_setWidth #[x, ← mkDecideProof (natLeE (mkNatLit mv) (mkNatLit 64))])
  | BitVec.zeroExtend m v x =>
    let some mv ← getNatValue? m | return none
    let some vv ← getNatValue? v | return none
    if vv != 64 || mv ≥ 64 then return none
    let pf ← mkAppM ``AsmVerif.RiscV.Sym.wb_setWidth #[x, ← mkDecideProof (natLeE (mkNatLit mv) (mkNatLit 64))]
    return some (mv, ← mkExpectedTypeHint pf (natLtE (← mkAppM ``BitVec.toNat #[e]) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit mv])))
  | HShiftLeft.hShiftLeft _ _ _ _ x c =>
    let some cv ← getNatValue? c | return none
    let some (k, h) ← widthBound x fuel | return none
    if k + cv ≥ 64 then return none
    return some (k + cv, ← mkAppM ``AsmVerif.RiscV.Sym.wb_shl #[c, h])
  | HShiftRight.hShiftRight _ _ _ _ x c =>
    let some cv ← getNatValue? c | return none
    let some (k, h) ← widthBound x fuel | return none
    return some (k - cv, ← mkAppM ``AsmVerif.RiscV.Sym.wb_ushr #[c, h])
  | HOr.hOr _ _ _ _ x y =>
    let some (kx, hx) ← widthBound x fuel | return none
    let some (ky, hy) ← widthBound y fuel | return none
    let k := max kx ky
    return some (k, ← mkAppM ``AsmVerif.RiscV.Sym.wb_or #[← widen kx k hx, ← widen ky k hy])
  | HAnd.hAnd _ _ _ _ x y =>
    let bx ← widthBound x fuel
    let by_ ← widthBound y fuel
    match bx, by_ with
    | some (kx, hx), some (ky, hy) =>
      if kx ≤ ky then return some (kx, ← mkAppM ``AsmVerif.RiscV.Sym.wb_and_l #[y, hx])
      else return some (ky, ← mkAppM ``AsmVerif.RiscV.Sym.wb_and_r #[x, hy])
    | some (kx, hx), none => return some (kx, ← mkAppM ``AsmVerif.RiscV.Sym.wb_and_l #[y, hx])
    | none, some (ky, hy) => return some (ky, ← mkAppM ``AsmVerif.RiscV.Sym.wb_and_r #[x, hy])
    | none, none => return none
  | HAdd.hAdd _ _ _ _ x y =>
    let some (kx, hx) ← widthBound x fuel | return none
    let some (ky, hy) ← widthBound y fuel | return none
    let k := max kx ky
    if k + 1 ≥ 64 then return none
    return some (k + 1, ← mkAppM ``AsmVerif.RiscV.Sym.wb_add #[← widen kx k hx, ← widen ky k hy])
  | _ =>
    if fuel == 0 then return none
    if e.isFVar then
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        unless d.userName.toString.endsWith "_def" do continue
        let some (_, rhs, a) := (← instantiateMVars d.type).eq? | continue
        unless a == e do continue
        let some (k, h) ← widthBound rhs (fuel - 1) | return none
        return some (k, ← mkAppM ``AsmVerif.RiscV.Sym.wb_eq #[← mkEqSymm d.toExpr, h])
      return none
    -- a defined function of words (a spec's `lebs2ipK w0 w1`): one unfolding, the bound of
    -- the body restated for the application (definitional)
    if e.isApp && e.getAppFn.isConst then
      let some e' ← unfoldDefinition? e | return none
      let e' := e'.headBeta
      let some (k, h) ← widthBound e' (fuel - 1) | return none
      return some (k, ← mkExpectedTypeHint h (natLtE (← mkAppM ``BitVec.toNat #[e]) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit k])))
    return none

/-- The words in `e` whose width `omega` should be told: `|||` terms and atoms. -/
partial def widthTargets (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let acc ← (do
    if acc.contains e then return acc
    let ty ← inferType e
    unless ty == mkApp (mkConst ``BitVec) (mkNatLit 64) || (← isDefEq ty (mkApp (mkConst ``BitVec) (mkNatLit 64))) do return acc
    if e.isFVar || e.isAppOf ``HOr.hOr then return acc.push e
    return acc) <|> pure acc
  match e with
  | .app f a => widthTargets a (← widthTargets f acc)
  | .mdata _ b => widthTargets b acc
  | _ => return acc

/-- The `t` of every `t % 2^64` in `e`, innermost first. -/
partial def modTargets (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let acc ← match e with
    | .app f a => modTargets a (← modTargets f acc)
    | .mdata _ b => modTargets b acc
    | _ => pure acc
  match_expr e with
  | HMod.hMod _ _ _ _ t c =>
    let two64 ← match ← getNatValue? c with
      | some v => pure (v == 2 ^ 64)
      | none => match_expr c with
        | HPow.hPow _ _ _ _ b k => pure ((← getNatValue? b) == some 2 && (← getNatValue? k) == some 64)
        | _ => pure false
    if two64 && !acc.contains t then return acc.push t else return acc
  | _ => return acc

/-- One `omega` attempt at `prop`, without the bignum atoms' definitions (`accN_k_def`,
    over `Nat`: address facts never need them) and without the unpacked disjointness facts
    (`hdjN`) that `keep` rejects: each of those is a disjunction, which `omega` splits. -/
partial def omegaWith (prop : Expr) (keep : LocalDecl → MetaM Bool) (extras : Bool)
    (filter : Option (LocalDecl → MetaM Bool) := none) (modPass : Bool := true) :
    TacticM (Option Expr) := do
  let mv ← mkFreshExprMVar prop
  let saved ← getGoals
  let t0 ← IO.monoMsNow
  try
    let mut drop : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let n := d.userName.toString
      if n.startsWith "acc" && n.endsWith "_def" then drop := drop.push d.fvarId
      else if n.startsWith "hdj" && !(← keep d) then drop := drop.push d.fvarId
      else if let some f := filter then
        -- the `t % 2^64 = t` facts of an outer pass are kept (they are not in its cluster)
        if n != "hmod64" && (← isProp (← instantiateMVars d.type)) && !(← f d) then
          drop := drop.push d.fvarId
    let g ← mv.mvarId!.tryClearMany drop
    setGoals [g]
    -- branch facts on unsigned comparisons, as `Nat` facts
    let g ← if !extras then pure g else g.withContext do
      let mut hs : Array Hypothesis := #[]
      for d in ← getLCtx do
        unless d.userName.toString.startsWith "hbr" do continue
        let ty ← instantiateMVars d.type
        unless (ty.find? (·.isConstOf ``BitVec.ult)).isSome do continue
        let brLemmas := #[``BitVec.ult, ``decide_eq_true_eq, ``not_not, ``Bool.not_eq_true,
          ``decide_eq_false_iff_not, ``Nat.not_lt, ``BitVec.toNat_add, ``BitVec.toNat_ofNat,
          ``BitVec.toNat_ushiftRight, ``BitVec.toNat_shiftLeft, ``BitVec.toNat_setWidth]
        let r ← simpWith ty #[] brLemmas (dec := false)
        if r.expr == ty then continue
        hs := hs.push { userName := d.userName.appendAfter "_nat", type := r.expr,
                        value := ← mkEqMP (← r.getProof) d.toExpr }
        -- and over the atoms' definitions, for goals stated that way
        let unf ← atomUnfoldRules ty
        if !unf.isEmpty then
          let r' ← simpWith ty unf brLemmas (dec := false)
          if r'.expr != r.expr then
            hs := hs.push { userName := d.userName.appendAfter "_unf", type := r'.expr,
                            value := ← mkEqMP (← r'.getProof) d.toExpr }
      -- each literal mask `x &&& c` in the goal bounds its value by `c`
      let mut masks : Array (Expr × Nat) := #[]
      let rec collect (e : Expr) (acc : Array (Expr × Nat)) : MetaM (Array (Expr × Nat)) := do
        let acc ← match_expr e with
          | HAnd.hAnd _ _ _ _ x c => do
            match_expr c with
            | BitVec.ofNat w n =>
              if (← getNatValue? w) == some 64 then
                if let some k ← getNatValue? n then pure (acc.push (x, k)) else pure acc
              else pure acc
            | _ => pure acc
          | _ => pure acc
        match e with
        | .app f a => collect a (← collect f acc)
        | .mdata _ b => collect b acc
        | _ => pure acc
      masks ← collect (← instantiateMVars prop) masks
      for (x, k) in masks do
        let pf ← mkAppM ``AsmVerif.RiscV.Sym.toNat_and_le_lit #[x, mkNatLit k]
        hs := hs.push { userName := `hmask, type := ← inferType pf, value := pf }
        let pf' ← mkAppM ``AsmVerif.RiscV.Sym.toNat_and_le_self #[x, ← mkAppM ``BitVec.ofNat #[mkNatLit 64, mkNatLit k]]
        hs := hs.push { userName := `hmask, type := ← inferType pf', value := pf' }
        if k % 8 == 0 then
          let pf ← mkAppM ``AsmVerif.RiscV.Sym.toNat_and_mod_lit #[x, mkNatLit k, mkNatLit 3,
            ← mkDecideProof (natLeE (mkNatLit 3) (mkNatLit 64)),
            ← mkDecideProof (← mkEq (← mkAppM ``HMod.hMod #[mkNatLit k, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 3]]) (mkNatLit 0))]
          hs := hs.push { userName := `hmask, type := ← inferType pf, value := pf }
      for x in ← widthTargets (← instantiateMVars prop) do
        if let some (_, pf) ← widthBound x then
          hs := hs.push { userName := `hwidth, type := ← inferType pf, value := pf }
      -- in the normal form the goal will have, so `omega` sees the same atoms
      let hsN ← hs.mapM fun h => do
        let r ← simpWith h.type #[] omegaNormLemmas (dec := false)
        if r.expr == h.type then return h
        return { h with type := r.expr, value := ← mkEqMP (← r.getProof) h.value }
      let mut g := g
      if !hsN.isEmpty then g := (← g.assertHypotheses hsN).2
      -- `t % 2^64 = t` for each `t % 2^64` of the goal and these facts whose `t < 2^64` the
      -- facts prove (innermost first, each with the ones before it): `omega` has no dark
      -- shadow, and a `2^64` quotient it cannot pin to `0` loses an otherwise trivial goal
      if modPass then
        -- innermost first, each on the goal with the previous ones already rewritten away, so
        -- the next remainder's argument is the term `omega` will see
        let mut modEqs : Array Expr := #[]
        let mut progress := true
        let mut fuel := 8
        while progress && fuel > 0 do
          fuel := fuel - 1
          progress := false
          let r ← g.withContext do simpWith prop modEqs omegaNormLemmas (dec := false)
          let targets ← modTargets r.expr
          for t in targets do
            if !(← modTargets t).isEmpty then continue
            let bound := natLtE t (mkNatLit (2 ^ 64))
            setGoals [g]
            -- without the disjointness disjunctions: a `2^64` bound never needs them, and a
            -- bound that is false (`sp.toNat + 2^64 - c`) would fail over all their splits
            let pf? ← g.withContext do omegaWith bound (fun _ => pure false) false filter false
            trace[AsmVerif.sym] "mod64 target {t}: {pf?.isSome}"
            if let some pf := pf? then
              let eq ← g.withContext do mkAppM ``Nat.mod_eq_of_lt #[pf]
              modEqs := modEqs.push eq
              g := (← g.assertHypotheses #[{ userName := `hmod64, type := ← g.withContext (inferType eq), value := eq }]).2
              progress := true
              break
        if !modEqs.isEmpty then
          -- the goal with those remainders rewritten away
          let (propN, pfN?) ← g.withContext do
            let r ← simpWith prop modEqs omegaNormLemmas (dec := false)
            pure (r.expr, r.proof?)
          if let some pfN := pfN? then
            let mv' ← g.withContext do mkFreshExprSyntheticOpaqueMVar propN
            g.assign (← g.withContext do mkAppM ``Eq.mpr #[pfN, mv'])
            g := mv'.mvarId!
      return g
    setGoals [g]
    -- the layout's constants, as rewrite rules
    let lrs ← g.withContext do
      (← layoutRuleIdents).mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    -- without recovery, so a failure surfaces as `omega`'s own message, not `abortTactic`
    Tactic.withoutRecover <| evalTactic (← `(tactic| (
      (try simp (config := {decide := true}) only [AsmVerif.RiscV.Sym.add_ofNat_big, AsmVerif.RiscV.Sym.Disjoint, AsmVerif.RiscV.Sym.Covers, AsmVerif.RiscV.Sym.InRegion, BitVec.toNat_add, BitVec.toNat_sub,
        BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, RiscvZkvm.Rv64.SP1_MAX_MEMORY, not_and, Nat.not_lt, AsmVerif.RiscV.Sym.OutsideRo,
        $lrs,*,
        -- a literal-only conjunct (a region at a fixed address) decides to `True`,
        -- which `omega` rejects as a goal
        and_true, true_and]) <;>
      omega)))
    setGoals saved
    let t1 ← IO.monoMsNow
    if t1 - t0 > 1000 then trace[AsmVerif.sym.time] "slow omega {t1 - t0} ms proving {prop}"
    return some (← instantiateMVars mv)
  catch ex =>
    setGoals saved
    let t1 ← IO.monoMsNow
    if t1 - t0 > 1000 then trace[AsmVerif.sym.time] "slow omega {t1 - t0} ms failing on {prop}"
    let what ← match ex with
      | .internal id _ => do pure m!"internal exception {← id.getName}"
      | _ => pure ex.toMessageData
    trace[AsmVerif.sym] "proveByOmega failed on {prop}: {what}"
    return none

/-- The facts connected to `prop`'s variables (and `seed`) by shared variables, among the
    arithmetic facts (no machine-state variable in the statement): the one cluster `omega`
    needs, without the frame's `sp` bounds whose `2^64` quotients make its elimination give
    up on an unrelated goal. -/
def clusterKeep (prop : Expr) (seed : Array FVarId) : MetaM (LocalDecl → MetaM Bool) := do
  let isState (fv : FVarId) : MetaM Bool := do
    return (← instantiateMVars (← fv.getDecl).type).isConstOf ``RiscvZkvm.Rv64.MachineState
  let mut facts : Array (FVarId × Array FVarId) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let fvs := (← ty.collectFVars.run {}).2.fvarIds
    if ← fvs.anyM isState then continue
    facts := facts.push (d.fvarId, fvs)
  let mut reach : Array FVarId := (← prop.collectFVars.run {}).2.fvarIds ++ seed
  let mut chosen : Array FVarId := #[]
  let mut changed := true
  while changed do
    changed := false
    for (f, fvs) in facts do
      if chosen.contains f then continue
      if fvs.any reach.contains then
        chosen := chosen.push f
        changed := true
        for v in fvs do
          unless reach.contains v do reach := reach.push v
  return fun d => pure (chosen.contains d.fvarId)

/-- `omega` on `prop`: first over the cluster of connected facts, then bare (no disjointness facts: most address goals need none, and
    each costs a case split), then with the auxiliary facts (branch conditions, masks, bit
    widths; only when `extras`, for symbolic-load bounds, since the executor also calls
    `omega` speculatively and a failure there must stay cheap), then with the disjointness
    facts over `prop`'s own variables, then with all. -/
def proveByOmega (prop : Expr) (extras : Bool := false) (seed : Array FVarId := #[])
    (clusterOnly : Bool := false) : TacticM (Option Expr) := do
  let prop ← instantiateMVars prop
  let fvs := (← prop.collectFVars.run {}).2.fvarIds
  -- first over the connected cluster of facts only, without the disjointness disjunctions
  -- (each is a case split; with all of a frame's they cost seconds and gigabytes per call)
  let cl? ← if !fvs.isEmpty || !seed.isEmpty then some <$> clusterKeep prop seed else pure none
  if let some cl := cl? then
    if let some pf ← omegaWith prop (fun _ => pure false) false (filter := some cl) then return some pf
    if extras then
      if let some pf ← omegaWith prop (fun _ => pure false) true (filter := some cl) then return some pf
  -- (a speculative call: the attempts over the whole context are not worth their cost)
  if clusterOnly then return none
  let relevant (d : LocalDecl) : MetaM Bool := do
    let ty ← instantiateMVars d.type
    let dfvs := (← ty.collectFVars.run {}).2.fvarIds
    return dfvs.all fun f => fvs.contains f
  -- the facts over exactly `prop`'s variables: for a frame/region disjointness, the one
  -- caller fact that decides it, without the other regions' `mod` atoms (under which
  -- `omega`'s incomplete elimination loses the goal)
  let exact (d : LocalDecl) : MetaM Bool := do
    let ty ← instantiateMVars d.type
    let dfvs := (← ty.collectFVars.run {}).2.fvarIds
    return dfvs.all (fun f => fvs.contains f) && fvs.all (fun f => dfvs.contains f)
  -- few disjointness facts: their splits are cheap, keep them from the start
  let nDj := (← getLCtx).foldl (fun n d => if d.userName.toString.startsWith "hdj" then n + 1 else n) 0
  if nDj ≤ 6 then
    if let some pf ← omegaWith prop (fun _ => pure true) false then return some pf
    if !extras then return none
    return ← omegaWith prop (fun _ => pure true) true
  if let some pf ← omegaWith prop (fun _ => pure false) false then return some pf
  if extras then
    if let some pf ← omegaWith prop (fun _ => pure false) true then return some pf
  if fvs.size ≥ 2 then
    if let some pf ← omegaWith prop exact extras then return some pf
  -- the cluster with its disjointness facts, before the wider contexts
  if let some cl := cl? then
    if let some pf ← omegaWith prop (fun _ => pure true) extras (filter := some cl) then return some pf
  if let some pf ← omegaWith prop relevant extras then return some pf
  omegaWith prop (fun _ => pure true) extras

/-! ## Reading the state -/

def St.regRules (st : St) : Array Expr :=
  st.regs.foldl (fun acc r => match r with | some f => acc.push f.proof | none => acc) #[]

/-- A fact with its statement in the executor's normal form (literals folded),
    so that it matches the terms the executor produces. -/
def normFact (h ty : Expr) : MetaM Expr := do
  let r ← simpWith ty #[] normLemmas
  if r.expr == ty then return h
  match r.proof? with
  | none => mkExpectedTypeHint h r.expr
  | some pf => mkAppM ``Eq.mp #[pf, h]

/-- Equations and negations among the pure facts in context, for `simp`. -/
def pureRules : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if d.userName.toString.endsWith "_def" then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Eq 3 then
      let lhs := ty.appFn!.appArg!
      if lhs.isAppOf ``MachineState.getReg || lhs.isAppOf ``MachineState.pc
        || lhs.isAppOf ``MachineState.privateInput || lhs.isAppOf ``MachineState.code
        || lhs.isAppOf ``MachineState.mem || lhs.isAppOf ``List.length then continue
      let ety := ty.appFn!.appFn!.appArg!
      if ety.isConstOf ``MachineState then continue
      out := out.push (← normFact d.toExpr ty)
    else if ty.isAppOfArity ``Not 1 || ty.isAppOfArity ``Ne 3 then
      out := out.push (← normFact d.toExpr ty)
  return out

/-- Locate a `width`-byte access at `l`: (region index, cell index, byte offset). -/
def findRegion? (st : St) (l : Lin) (width : Nat) : Option (Nat × Nat × Nat) := Id.run do
  for h : ri in [0:st.regions.size] do
    let R := st.regions[ri]
    if R.lenPf.isSome then continue
    if R.baseLin.sameAtom l then
      let off := (l.c + two64 - R.baseLin.c) % two64
      if off + width ≤ 8 * R.n then
        let i := off / 8
        let k := off % 8
        if k + width ≤ 8 then
          return some (ri, i, k)
  return none

/-- Locate a block of `m` cells at `l`: (region index, first cell). -/
def findBlock? (st : St) (l : Lin) (m : Nat) : Option (Nat × Nat) := Id.run do
  for h : ri in [0:st.regions.size] do
    let R := st.regions[ri]
    if R.lenPf.isSome then continue
    if R.baseLin.sameAtom l then
      let off := (l.c + two64 - R.baseLin.c) % two64
      if off % 8 == 0 && off / 8 + m ≤ R.n then
        return some (ri, off / 8)
  return none

/-- `base + BitVec.ofNat 64 (8 * i + k)` (or `8 * i` when `k = 0`). -/
def cellAddr (base : Expr) (i k : Nat) : MetaM Expr := do
  let m ← mkMulN (mkNatLit 8) (mkNatLit i)
  let off ← if k == 0 then pure m else mkAddN m (mkNatLit k)
  mkAdd base (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) off)

def cellFact (st : St) (R : RegionInfo) (ci : Nat) (hi : Expr) : MetaM Expr := do
  let cellVal := R.cells[ci]!
  let hget ← mkAppM ``AsmVerif.RiscV.Sym.Region.get #[R.hyp, hi, ← mkEqRefl cellVal]
  let addrE ← cellAddr R.base ci 0
  let (addrN, haddr) ← rewriteTo addrE #[] normLemmas
  if addrN == addrE then return hget
  let motive := mkLambda `a .default wordTy (mkEqW (mkApp2 (mkConst ``MachineState.getMem) st.s (mkBVar 0)) cellVal)
  let pf ← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[motive, haddr], hget]
  -- A simp proof's inferred type shows the RHS *before* literal folding, so pin
  -- the type we mean or the fact will not match.
  mkExpectedTypeHint pf (mkEqW (mkApp2 (mkConst ``MachineState.getMem) st.s addrN) cellVal)

/-- Prove `addr = target` for two address expressions with the same normal form. -/
def proveAddrEq (st : St) (addr target : Expr) : MetaM Expr := do
  if addr == target then return ← mkEqRefl addr
  let prop := mkEqW addr target
  match ← proveBySimp prop st.regRules normLemmas with
  | some pf => return pf
  | none => throwError "sym_exec: cannot show address {addr} = {target}"

def proveAddr (st : St) (addr : Expr) (R : RegionInfo) (i k : Nat) : MetaM Expr := do
  proveAddrEq st addr (← cellAddr R.base i k)

/-- `Region a (cells i..i+m) s` from region `R`, with `a` the given address expression. -/
def subRegion (st : St) (R : RegionInfo) (i m : Nat) (a : Expr) : MetaM (Expr × Array Expr × Expr) := do
  if i == 0 && m == R.n then
    let ha ← proveAddrEq st a R.base
    let motive := mkLambda `b .default wordTy (mkApp3 (mkConst ``AsmVerif.RiscV.Sym.Region) (mkBVar 0) R.listExpr st.s)
    let pf ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, ha], R.hyp]
    return (pf, R.cells, R.listExpr)
  let ws := R.cells.extract i (i + m)
  let wsE := mkListLit wordTy ws
  let dropTake ← mkAppM ``List.take #[mkNatLit m, ← mkAppM ``List.drop #[mkNatLit i, R.listExpr]]
  let hws ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy dropTake wsE) wsE
  let ha ← proveAddrEq st a (← cellAddr R.base i 0)
  let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.sub #[R.hyp, mkNatLit i, mkNatLit m, ha, hws]
  return (pf, ws, wsE)

/-- A block of `m` cells at `l` that no one region holds, across adjacent literal regions (a
    frame cut around a callee's output): their join by `Region.append`, for one use. -/
def joinBlock? (st : St) (l : Lin) (m : Nat) : MetaM (Option RegionInfo) := do
  let lit (R : RegionInfo) : Bool :=
    R.lenPf.isNone && R.outW.isNone && R.cells.size == R.n && R.baseLin.sameAtom l
  let some r0 := (List.range st.regions.size).find? (fun ri =>
      let R := st.regions[ri]!
      let off := (l.c + two64 - R.baseLin.c) % two64
      lit R && off % 8 == 0 && off / 8 < R.n) | return none
  let mut cur := st.regions[r0]!
  let need := (l.c + two64 - cur.baseLin.c) % two64 / 8 + m
  let mut steps := 0
  while cur.n < need do
    steps := steps + 1
    if steps > 64 then return none
    let endC := (cur.baseLin.c + 8 * cur.n) % two64
    let some r := (List.range st.regions.size).find? (fun ri =>
        let R := st.regions[ri]!
        lit R && R.baseLin.c == endC && R.n > 0) | return none
    let R := st.regions[r]!
    let ha ← proveAddrEq st (← cellAddr cur.base cur.n 0) R.base
    let motive := mkLambda `b .default wordTy (mkApp3 (mkConst ``AsmVerif.RiscV.Sym.Region) (mkBVar 0) R.listExpr st.s)
    let h2 ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, ha], R.hyp]
    let cells := cur.cells ++ R.cells
    let listE := mkListLit wordTy cells
    let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.append #[cur.hyp, h2]
    let pf ← mkExpectedTypeHint pf (mkApp3 (mkConst ``AsmVerif.RiscV.Sym.Region) cur.base listE st.s)
    cur := { cur with n := cur.n + R.n, cells := cells, listExpr := listE, hyp := pf, hypM := pf,
                      ok := noRegionOk, w := none, roOut := none }
  return some cur

/-! ## Initialisation from the context -/

def decodeCode (b prog pf : Expr) : MetaM CodeInfo := do
  let optInstr := mkApp (mkConst ``Option [0]) (mkConst ``Instr)
  let bv ← bvLit b
  let cells ← listElems prog
  let mut decoded : Array (Option Expr) := #[]
  for c in cells do
    let c ← whnfD c
    match_expr c with
    | Option.some _ x => decoded := decoded.push (some x)
    | _ => decoded := decoded.push none
  let lenTy := mkApp3 (mkConst ``Eq [1]) natTy
    (mkApp2 (mkConst ``List.length [0]) optInstr prog) (mkNatLit cells.size)
  let hlen ← rflOf lenTy (mkNatLit cells.size)
  return ⟨bv, b, prog, decoded, hlen, pf, pf⟩

/-- Which W entry (and cell offset) a region lies in. -/
def wSlot (ws : Array WEntry) (bl : Lin) (n : Nat) : Option (Nat × Nat) := Id.run do
  for h : j in [0:ws.size] do
    let w := ws[j]
    if w.baseLin.sameAtom bl then
      let off := (bl.c + two64 - w.baseLin.c) % two64
      if off % 8 == 0 && off / 8 + n ≤ w.n then return some (j, off / 8)
  return none

/-- Regions over a list variable with more cells than this are kept opaque. -/
def opaqueMin : Nat := 64

/-- `vs.length` as a literal by `simp` over the default simp set (`List.length_append`, the
    models' `@[simp]` length lemmas), with its proof: the size of a region a specification
    states over a model (`commitW … ++ [flag]`) without a length fact in context. -/
def derivedLen (vs : Expr) (extra : Array Expr := #[]) : MetaM (Option (Expr × Expr)) := do
  let lenE ← mkAppM ``List.length #[vs]
  -- the length facts in hand as rewrite rules too (`overlay B J` has `J`'s length, `J.length = 166`)
  let mut thms ← getSimpTheorems
  for h in extra do
    if h.isFVar then thms ← thms.add (.fvar h.fvarId!) #[] h
  let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let simprocs ← Simp.getSimprocs
  let (r, _) ← simp lenE ctx #[simprocs]
  let some _ ← getNatValue? r.expr | return none
  let pf ← match r.proof? with
    | some p => pure p
    | none => mkEqRefl lenE
  return some (r.expr, pf)

/-- A list whose head is a model function rather than a list constructor or combinator: the
    only shape `readPost` atomizes by a derived length. -/
def modelHead (vs : Expr) : Bool :=
  match vs.getAppFn with
  | .const n _ => !(n ∈ [``HAppend.hAppend, ``List.append, ``RiscvZkvm.Rv64.Accel.natToLeLimbs,
      ``List.replicate, ``List.map, ``List.take, ``List.drop, ``List.range, ``AsmVerif.RiscV.Sym.contents])
  | _ => false

/-- A context fact `vs.length = n`. -/
def findLenFact (vs : Expr) (n : Nat) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    match_expr ty with
    | Eq _ lhs rhs =>
      if lhs.isAppOfArity ``List.length 2 && lhs.appArg! == vs then
        if (← getNatValue? rhs) == some n then return some d.toExpr
    | _ => pure ()
  return none

/-- Expand a region over a list variable of known length into a literal. -/
def expandRegion (b vs pf : Expr) (n : Nat) (lens : Array (Expr × Expr × Expr)) :
    MetaM (Expr × Expr × Array Expr) := do
  try
    let cells ← listElems vs
    return (vs, pf, cells)
  catch _ =>
    let hlen ← match lens.find? (fun (l, _, _) => l == vs) with
      | some (_, _, h) => pure h
      | none =>
        -- `contents s b n` has a known length
        if vs.isAppOf ``AsmVerif.RiscV.Sym.contents then
          mkAppM ``AsmVerif.RiscV.Sym.length_contents vs.getAppArgs
        else match ← derivedLen vs with
          | some (_, pf) => pure pf
          | none => throwError "sym_exec: region at {b}: contents are not a literal and no length fact was found"
    let fn ← withLocalDeclD `i natTy fun i => do
      mkLambdaFVars #[i] (← mkAppM ``GetElem?.getElem! #[vs, i])
    let mapE ← mkAppM ``List.map #[fn, ← mkAppM ``List.range #[mkNatLit n]]
    let cells ← (← listElems mapE).mapM fun c => pure c.headBeta
    let lit := mkListLit wordTy cells
    let heq ← mkAppM ``AsmVerif.RiscV.Sym.List.eq_map_range #[vs, hlen]
    let heq' ← mkAppM ``Eq.trans #[heq, ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy mapE lit) lit]
    let pf' ← mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[pf, heq']
    return (lit, pf', cells)

/-- Unpack `StackOk room sp` hypotheses into `Nat` facts `omega` can see. -/
def unpackStackOk : TacticM Unit := do
  let g ← getMainGoal
  let hyps ← g.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOf ``AsmVerif.RiscV.Sym.StackOk then out := out.push d.toExpr
    return out
  for h in hyps do
    for (f, nm) in [(``AsmVerif.RiscV.Sym.StackOk.aligned, "al"), (``AsmVerif.RiscV.Sym.StackOk.lo, "lo"), (``AsmVerif.RiscV.Sym.StackOk.hi, "hi")] do
      let (ty, pf) ← withMainContext do
        let pf ← mkAppM f #[h]
        pure (← inferType pf, pf)
      let _ ← addFact (Name.mkSimple s!"hstk_{nm}") ty pf

/-- Unpack `Disjoint` hypotheses into `Nat` facts `omega` can see. -/
def unpackDisjoint : TacticM Unit := do
  let g ← getMainGoal
  let hyps ← g.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``AsmVerif.RiscV.Sym.Disjoint 4 then out := out.push (d.toExpr, ty)
    return out
  -- `RegionOk`: the region's extent, as `Nat` facts
  let oks ← g.withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``AsmVerif.RiscV.Sym.RegionOk 4 then out := out.push d.toExpr
    return out
  let mut j := 0
  for h in oks do
    let (ty, pf) ← withMainContext do
      let pf ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.inMem #[h]
      let ty ← inferType pf
      let r ← simpWith ty (← layoutRules) #[``AsmVerif.RiscV.Sym.add_ofNat_big, ``BitVec.toNat_add, ``BitVec.toNat_sub,
        ``BitVec.toNat_ofNat, ``RiscvZkvm.Rv64.SP1_MAX_MEMORY]
      if r.expr == ty then pure (ty, pf) else pure (r.expr, ← mkEqMP (← r.getProof) pf)
    let _ ← addFact (Name.mkSimple s!"hokm{j}") ty pf
    j := j + 1
  let mut k := 0
  for (h, ty) in hyps do
    let r? ← withMainContext do
      let r ← simpWith ty (← layoutRules) #[``AsmVerif.RiscV.Sym.add_ofNat_big, ``AsmVerif.RiscV.Sym.Disjoint, ``BitVec.toNat_add, ``BitVec.toNat_sub, ``BitVec.toNat_ofNat]
      if r.expr == ty then return none
      pure (some (r.expr, ← mkEqMP (← r.getProof) h))
    if let some (ty', pf) := r? then
      let _ ← addFact (Name.mkSimple s!"hdj{k}") ty' pf
      k := k + 1

/-- The layout the hypotheses name: through `RoImage L s`, `StackOk L …`, or a `Layout`
    projection inside a `RegionOk` or `CodeWithin` fact. -/
def findLayout : MetaM (Option LayoutInfo) := do
  let isProj (e : Expr) : Bool :=
    e.isAppOfArity ``AsmVerif.RiscV.Sym.Layout.textLo 1 || e.isAppOfArity ``AsmVerif.RiscV.Sym.Layout.textHi 1 ||
    e.isAppOfArity ``AsmVerif.RiscV.Sym.Layout.roBase 1 || e.isAppOfArity ``AsmVerif.RiscV.Sym.Layout.stackTop 1
  let mut L? : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    match_expr ty with
    | AsmVerif.RiscV.Sym.RoImage L _ => L? := some L
    | AsmVerif.RiscV.Sym.StackOk L _ _ => L? := some L
    | _ =>
      if ty.isAppOf ``AsmVerif.RiscV.Sym.RegionOk || ty.isAppOf ``AsmVerif.RiscV.Sym.CodeWithin then
        if let some e := ty.find? isProj then L? := some e.appArg!
    if L?.isSome then break
  let some L := L? | return none
  let val (f : Name) : MetaM Nat := do
    let some v ← getNatValue? (← whnfD (mkApp (mkConst f) L))
      | throwError "sym_exec: `{f}` of the layout {L} does not evaluate to a literal"
    pure v
  let roBase ← val ``AsmVerif.RiscV.Sym.Layout.roBase
  let roBytes ← val ``AsmVerif.RiscV.Sym.Layout.roBytes
  let roChunks ← val ``AsmVerif.RiscV.Sym.Layout.roChunks
  let stackTop ← val ``AsmVerif.RiscV.Sym.Layout.stackTop
  let textLo ← val ``AsmVerif.RiscV.Sym.Layout.textLo
  let textHi ← val ``AsmVerif.RiscV.Sym.Layout.textHi
  return some { L, roBase, roBytes, roChunks, stackTop, textLo, textHi }

def initCore (g : MVarId) (specs : Array SpecInfo) (stops : Array Nat) : MetaM (St × Expr × Expr) := g.withContext do
  let (_, s0) ← goalParts g
  let layout? ← findLayout
  let lctx ← getLCtx
  let mut hpc : Option (Expr × Nat) := none
  let mut regs : Array (Option RegFact) := Array.replicate 32 none
  let mut regionHyps : Array (Expr × Expr × Expr) := #[]
  let mut oks : Array (Expr × Expr × Expr) := #[]   -- (base, n, proof)
  let mut codes : Array CodeInfo := #[]
  let mut hcw : Option Expr := none
  let mut disj : Array (Expr × Expr × Expr × Expr × Expr) := #[]
  let mut unch : Option (Expr × Expr) := none
  let mut priv : Option (Expr × Expr) := none
  let mut lens : Array (Expr × Expr × Expr) := #[]
  let mut ro : Option Expr := none
  let mut roOuts : Array (Expr × Expr) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let pf := d.toExpr
    match_expr ty with
    | Eq _ lhs rhs =>
      match_expr lhs with
      | MachineState.pc s =>
        if s == s0 then
          if let some v ← litValue? rhs then hpc := some (pf, v)
      | MachineState.getReg s r =>
        if s == s0 then
          let i ← regIdx r
          if i != 0 then
            let l ← normLin rhs
            regs := regs.set! i (some ⟨rhs, l, pf⟩)
      | MachineState.privateInput s =>
        if s == s0 then priv := some (rhs, pf)
      | List.length _ l => lens := lens.push (l, rhs, pf)
      | _ => pure ()
    | AsmVerif.RiscV.Sym.Region b vs s => if s == s0 then regionHyps := regionHyps.push (b, vs, pf)
    | AsmVerif.RiscV.Sym.RegionOk lo _ b n =>
      -- a writable block: narrowed to the code window, with its read-only-segment fact
      let roBased ← match layout? with
        | some li => pure ((← getNatValue? (← whnfD lo)) == some li.roBase)
        | none => pure false
      if roBased then
        oks := oks.push (b, n, ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.toText #[pf])
        roOuts := roOuts.push (b, ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.roOut #[pf])
      else oks := oks.push (b, n, pf)
    | AsmVerif.RiscV.Sym.CodeAt b prog s => if s == s0 then codes := codes.push (← decodeCode b prog pf)
    | AsmVerif.RiscV.Sym.CodeWithin _ _ s => if s == s0 then hcw := some pf
    | AsmVerif.RiscV.Sym.Disjoint b₁ n₁ b₂ n₂ => disj := disj.push (b₁, n₁, b₂, n₂, pf)
    | AsmVerif.RiscV.Sym.Unchanged W _ sb => if sb == s0 then unch := some (W, pf)
    | AsmVerif.RiscV.Sym.RoImage _ s => if s == s0 then ro := some pf
    | _ => pure ()
  let some (hpcPf, pcv) := hpc | throwError "sym_exec: no literal `pc` fact for {s0}"
  let some hcwPf := hcw | throwError "sym_exec: no `CodeWithin` fact for {s0}"
  -- the register file: every register has a value, `s₀.getReg xᵢ` if nothing else
  let mut regList := mkListLit wordTy ((List.range 32).toArray.map fun i => if i == 0 then mkWordLit 0 else mkGetReg s0 i)
  let mut hregsPf ← mkExpectedTypeHint (mkApp (mkConst ``AsmVerif.RiscV.Sym.Regs.self) s0) (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) s0 regList)
  for i in [1:32] do
    match regs[i]! with
    | some f =>
      let hlen ← rflOf (← mkEq (← mkAppM ``List.length #[regList]) (mkNatLit 32)) (mkNatLit 32)
      let pf ← mkAppM ``AsmVerif.RiscV.Sym.Regs.update #[hregsPf, hlen, mkNatLit i, ← natLt i 32, f.proof]
      regList ← regListSet regList i f.val
      hregsPf ← mkExpectedTypeHint pf (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) s0 regList)
    | none =>
      let v := mkGetReg s0 i
      regs := regs.set! i (some ⟨v, ⟨some v, 0⟩, default⟩)
  regs := regs.set! 0 (some ⟨mkWordLit 0, Lin.lit 0, default⟩)
  let prodTy ← mkAppM ``Prod #[wordTy, natTy]
  let (W, hunch) ← match unch with
    | some (W, pf) => pure (W, pf)
    | none =>
      let W := mkListLit prodTy #[]
      pure (W, mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Unchanged.refl) W s0)
  let mut wEntries : Array WEntry := #[]
  for e in ← listElems W do
    let e ← whnfD e
    let b := e.getAppArgs[2]!
    let nE := e.getAppArgs[3]!
    let some n ← getNatValue? (← whnfD nE) | throwError "sym_exec: W entry size not a literal {nE}"
    let some (_, _, okPf) ← oks.findM? (fun (b', n', _) => return b' == b && (← isDefEq n' nE))
      | throwError "sym_exec: W entry at {b} has no `RegionOk` fact"
    wEntries := wEntries.push ⟨b, ← normLin b, n, ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.nowrap #[okPf]⟩
  let mut regions : Array RegionInfo := #[]
  for (b, vs, pf) in regionHyps do
    -- the region's own size (a length fact, or a literal list), when it has one;
    -- a `RegionOk` at the same base but of another size is some other region's
    let own? : Option Expr ← match lens.find? (fun (l, _, _) => l == vs) with
      | some (_, nE, _) => pure (some nE)
      | none => (do pure (some (mkNatLit (← listElems vs).size))) <|> pure none
    let ok? ← oks.findM? fun (b', n', _) => do
      if b' != b then return false
      match own? with
      | some nE => isDefEq n' nE
      | none => return true
    let (nE, okPf) ← match ok?, own? with
      | some (_, nE, okPf), _ => pure (nE, okPf)
      | none, some nE => pure (nE, noRegionOk)
      | none, none => throwError "sym_exec: region at {b}: no size"
    let some n ← getNatValue? (← whnfD nE) | throwError "sym_exec: region at {b}: size not a literal {nE}"
    let bl ← normLin b
    let roOut := (roOuts.find? (fun (b', _) => b' == b)).map (·.2)
    -- a large region over a list variable, outside the write set, stays opaque
    let lit? ← try (do let _ ← listElems vs; pure true) catch _ => pure false
    if !lit? && n > opaqueMin && (wSlot wEntries bl n).isNone then
      if let some (_, _, hlen) := lens.find? (fun (l, _, _) => l == vs) then
        regions := regions.push ⟨b, bl, n, #[], vs, pf, pf, okPf, none, none, roOut, some hlen⟩
        continue
    let (vs, pf, cells) ← expandRegion b vs pf n lens
    if n != cells.size then
      throwError "sym_exec: region at {b}: RegionOk says {n} cells, list has {cells.size}"
    regions := regions.push ⟨b, bl, n, cells, vs, pf, pf, okPf, wSlot wEntries bl n, none, roOut, none⟩
  -- region bases are doubleword-aligned: the mask tests the code makes on pointers
  let mut alignFacts : Array Expr := #[]
  for R in regions do
    if R.ok != noRegionOk && R.ok.getAppFn.constName? != some ``AsmVerif.RiscV.Sym.RoImage.ok then
      -- stated about the base in the executor's normal form (`sp + c`, not `sp - d`)
      let h ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.and7 #[R.ok]
      let ty ← inferType h
      let r ← simpWith ty #[] normLemmas
      let h' ← if r.expr == ty then pure h else mkEqMP (← r.getProof) h
      alignFacts := alignFacts.push h'
  let hmem0 ← mkEqRefl (mkApp (mkConst ``MachineState.mem) s0)
  let hcode0 ← mkEqRefl (mkApp (mkConst ``MachineState.code) s0)
  let st : St := { s0 := s0, s := s0, pc := some pcv, pcE := mkWordLit pcv, hpc := hpcPf, regs := regs, regList := regList, hregs := default, sM := s0, hmem := hmem0, regions := regions, codes := codes, hcode := hcode0, hcw0 := hcwPf, hcw := hcwPf, k := 0, W := W, wEntries := wEntries, hunchM := hunch, hunch := hunch, hroM := ro, hro := ro, layout := layout?, priv := priv, disj := disj, toClear := #[], pureFacts := (← pureRules) ++ alignFacts, specs := specs, stops := stops }
  pure (st, mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) s0 regList, hregsPf)

/-- A known `Disjoint a m b n`, in either order. -/
def lookupDisj (disj : Array (Expr × Expr × Expr × Expr × Expr)) (a : Expr) (m : Nat) (b : Expr)
    (n : Nat) : MetaM (Option Expr) := do
  for (b₁, n₁, b₂, n₂, pf) in disj do
    if b₁ == a && b₂ == b then
      if ← isDefEq n₁ (mkNatLit m) <&&> isDefEq n₂ (mkNatLit n) then return some pf
    if b₁ == b && b₂ == a then
      if ← isDefEq n₁ (mkNatLit n) <&&> isDefEq n₂ (mkNatLit m) then
        return some (mkApp5 (mkConst ``AsmVerif.RiscV.Sym.Disjoint.symm) b₁ n₁ b₂ n₂ pf)
  return none

/-- Two blocks at literal offsets from one atom that overlap: not disjoint, no prover needed. -/
def linOverlap (la : Lin) (m : Nat) (lb : Lin) (n : Nat) : Bool :=
  la.atom.isSome && la.sameAtom lb && la.c < lb.c + 8 * n && lb.c < la.c + 8 * m

/-- A sub-block pair of a known disjoint pair (`Disjoint.of_sub`): `[a, a + 8 m)` inside one
    side and `[b, b + 8 n)` inside the other, at literal offsets from the same base atoms. The
    address equations by the normaliser, else by `omega` over their own atoms; never `omega` over
    the context for the disjointness itself (seconds, and a certificate the size of the context). -/
def lookupDisjSub (st : St) (a : Expr) (m : Nat) (b : Expr) (n : Nat) : TacticM (Option Expr) := do
  let la ← normLin a
  let lb ← normLin b
  let fits (l : Lin) (m : Nat) (l' : Lin) (n' : Nat) : Option Nat :=
    if l.sameAtom l' && l'.c ≤ l.c && (l.c - l'.c) % 8 == 0 && (l.c - l'.c) / 8 + m ≤ n' then
      some ((l.c - l'.c) / 8) else none
  -- structural only (`proveBySimp`, as every other address equality): an `omega` fallback
  -- here ran on every candidate pair at every lookup and took `SpendValidatingKey` past 16 GB
  let addrEq (x target : Expr) : TacticM (Option Expr) := do
    if x == target then return some (← mkEqRefl x)
    proveBySimp (mkEqW x target) st.regRules normLemmas
  let build (b₁ : Expr) (n₁ : Nat) (b₂ : Expr) (n₂ : Nat) (pf : Expr) : TacticM (Option Expr) := do
    let some i := fits la m (← normLin b₁) n₁ | return none
    let some j := fits lb n (← normLin b₂) n₂ | return none
    let some ha ← addrEq a (← cellAddr b₁ i 0) | return none
    let some hb ← addrEq b (← cellAddr b₂ j 0) | return none
    let him ← mkDecideProof (natLeE (← mkAddN (mkNatLit i) (mkNatLit m)) (mkNatLit n₁))
    let hjn ← mkDecideProof (natLeE (← mkAddN (mkNatLit j) (mkNatLit n)) (mkNatLit n₂))
    return some (← mkAppM ``AsmVerif.RiscV.Sym.Disjoint.of_sub #[pf, ha, him, hb, hjn])
  for (b₁, n₁E, b₂, n₂E, pf) in st.disj do
    let some n₁ ← getNatValue? (← whnfD n₁E) | continue
    let some n₂ ← getNatValue? (← whnfD n₂E) | continue
    if let some r ← build b₁ n₁ b₂ n₂ pf then return some r
    if let some r ← build b₂ n₂ b₁ n₁ (mkApp5 (mkConst ``AsmVerif.RiscV.Sym.Disjoint.symm) b₁ n₁E b₂ n₂E pf) then return some r
  -- two blocks of one write-set entry (a frame), at non-overlapping literal offsets
  -- (`Disjoint.within` over the entry's no-wrap fact)
  for we in st.wEntries do
    let some i := fits la m we.baseLin we.n | continue
    let some j := fits lb n we.baseLin we.n | continue
    unless i + m ≤ j || j + n ≤ i do continue
    let some ha ← addrEq a (← cellAddr we.base i 0) | continue
    let some hb ← addrEq b (← cellAddr we.base j 0) | continue
    let him ← mkDecideProof (natLeE (← mkAddN (mkNatLit i) (mkNatLit m)) (mkNatLit we.n))
    let hjn ← mkDecideProof (natLeE (← mkAddN (mkNatLit j) (mkNatLit n)) (mkNatLit we.n))
    let hsep ← mkDecideProof (← mkAppM ``Or #[natLeE (← mkAddN (mkNatLit i) (mkNatLit m)) (mkNatLit j),
      natLeE (← mkAddN (mkNatLit j) (mkNatLit n)) (mkNatLit i)])
    return some (← mkAppM ``AsmVerif.RiscV.Sym.Disjoint.within #[we.nw, ha, hb, him, hjn, hsep])
  return none

/-- The layout's constants as hypotheses `hL_roBase : L.roBase = 0x…` (by `rfl`), once. -/
def addLayoutFacts (li : LayoutInfo) : TacticM Unit := do
  let have? (nm : Name) : TacticM Bool := withMainContext do
    return ((← getLCtx).findFromUserName? nm).isSome
  for (f, v, nm) in [(``AsmVerif.RiscV.Sym.Layout.roBase, li.roBase, `hL_roBase),
      (``AsmVerif.RiscV.Sym.Layout.roBytes, li.roBytes, `hL_roBytes),
      (``AsmVerif.RiscV.Sym.Layout.textLo, li.textLo, `hL_textLo),
      (``AsmVerif.RiscV.Sym.Layout.textHi, li.textHi, `hL_textHi),
      (``AsmVerif.RiscV.Sym.Layout.stackTop, li.stackTop, `hL_stackTop)] do
    if ← have? nm then continue
    let (ty, pf) ← withMainContext do
      let ty ← mkEq (mkApp (mkConst f) li.L) (mkNatLit v)
      pure (ty, ← mkExpectedTypeHint (← mkEqRefl (mkNatLit v)) ty)
    let _ ← addFact nm ty pf

def initState (specs : Array SpecInfo) (stops : Array Nat) : TacticM St := do
  if let some li ← withMainContext findLayout then addLayoutFacts li
  unpackStackOk
  unpackDisjoint
  let (st, regsTy, regsPf) ← initCore (← getMainGoal) specs stops
  let hregsF ← addFact `hregs0 regsTy regsPf
  -- the register proofs first (`initCore` leaves placeholders): the structural disjointness
  -- below rewrites addresses with the register rules
  let st ← withMainContext ({ st with hregs := hregsF }).refresh
  -- regions outside `W` and provably disjoint from all of it are read-only
  let wElems ← withMainContext (listElems st.W)
  let mut regions := st.regions
  for ri in [0:regions.size] do
    let R := regions[ri]!
    if R.w.isSome then continue
    let outW ← withMainContext do
      let mut pf ← mkAppOptM ``AsmVerif.RiscV.Sym.disj_nil #[some R.base, some (mkNatLit R.n)]
      for j in (List.range wElems.size).reverse do
        let e ← whnfD wElems[j]!
        let (wb, wn) := (e.getAppArgs[2]!, e.getAppArgs[3]!)
        let prop := mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Disjoint) R.base (mkNatLit R.n) (← mkAppM ``Prod.fst #[e]) (← mkAppM ``Prod.snd #[e])
        let known ← match ← getNatValue? (← whnfD wn) with
          | some n => do
            match ← lookupDisj st.disj R.base R.n wb n with
            | some h => pure (some h)
            | none => lookupDisjSub st R.base R.n wb n
          | none => pure none
        let hd ← match known with
          | some h => mkExpectedTypeHint h prop
          | none =>
            if let some n := ← getNatValue? (← whnfD wn) then
              if linOverlap R.baseLin R.n (← normLin wb) n then return none
            match ← proveByOmega prop with
            | some h => pure h
            | none => return none
        pf ← mkAppM ``AsmVerif.RiscV.Sym.disj_cons #[hd, pf]
      pure (some pf)
    if let some o := outW then
      let fv ← addFact (Name.mkSimple s!"hout{ri}") (← withMainContext (inferType o)) o
      regions := regions.set! ri { R with outW := some fv }
  withMainContext ({ st with regions := regions }).refresh

/-! ## Fetch -/

structure Fetched where
  code : CodeInfo
  idx : Nat
  ins : Expr
  hfetch : Expr   -- : s.code s.pc = some ins
  deriving Inhabited

def fetch (st : St) (pc : Nat) : MetaM Fetched := do
  let optInstr := mkApp (mkConst ``Option [0]) (mkConst ``Instr)
  for c in st.codes do
    if c.base ≤ pc && pc < c.base + 4 * c.prog.size then
      let i := (pc - c.base) / 4
      let some ins := c.prog[i]! | throwError "sym_exec: no instruction at {pc} (hole)"
      let hiLit ← natLt i c.prog.size
      let lenE := mkApp2 (mkConst ``List.length [0]) optInstr c.progExpr
      let hi := mkApp5 (mkConst ``Nat.lt_of_lt_of_eq) (mkNatLit i) (mkNatLit c.prog.size) lenE
        hiLit (mkApp4 (mkConst ``Eq.symm [1]) natTy lenE (mkNatLit c.prog.size) c.hlen)
      let getBang ← mkAppM ``GetElem?.getElem! #[c.progExpr, mkNatLit i]
      let someIns := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Instr) ins
      -- `prog[i]! = some ins`: through the module's packed form when it has one
      -- (`prog_packed : prog = decodeWords (unpackWords packed len)`, from `gen-image`), so
      -- that the kernel does one shift of `packed` rather than walk `i` cells of the literal
      -- at every step; otherwise by `rfl`
      let hprog ← do
        let packed? : Option Expr ← do
          let .const pn ls := c.progExpr | pure none
          let ln := Name.str pn.getPrefix "prog_packed"
          if (← getEnv).contains ln then pure (some (mkConst ln ls)) else pure none
        match packed? with
        | some hpk =>
          -- hpk : prog = decodeWords (unpackWords packed len)
          let some (_, _, rhs) := (← inferType hpk).eq? | throwError "sym_exec: prog_packed shape"
          let unpackE := rhs.appArg!
          let nE := unpackE.appFn!.appArg!
          let lenE := unpackE.appArg!
          let hi ← mkDecideProof (natLtE (mkNatLit i) lenE)
          let wordE := mkApp2 (mkConst ``AsmVerif.RiscV.wordOfPacked) nE (mkNatLit i)
          let decE := mkApp (mkConst ``RiscvZkvm.Interpreter.decode) wordE
          let hdec ← rflOf (mkApp3 (mkConst ``Eq [1]) optInstr decE someIns) someIns
          let hget ← mkAppM ``AsmVerif.RiscV.getElem!_decodeWords_unpack #[hi, hdec]
          -- prog[i]! = some ins, by rewriting `prog` with `hpk`
          let motive := mkLambda `p .default (mkApp (mkConst ``List [0]) optInstr)
            (mkApp3 (mkConst ``Eq [1]) optInstr (mkApp2 (mkConst ``GetElem?.getElem! [0, 0, 0]) (mkBVar 0) (mkNatLit i)) someIns)
          let _ := motive
          mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[← withLocalDeclD `p (mkApp (mkConst ``List [0]) optInstr) fun p => do
              mkLambdaFVars #[p] (← mkAppM ``GetElem?.getElem! #[p, mkNatLit i]), hpk], hget]
        | none => rflOf (mkApp3 (mkConst ``Eq [1]) optInstr getBang someIns) someIns
      let pcTarget ← mkAdd (mkWordLit c.base) (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64)
        (← mkMulN (mkNatLit 4) (mkNatLit i)))
      let some hpcEq ← proveBySimp (mkEqW (mkPc st.s) pcTarget) #[st.hpc] normLemmas
        | throwError "sym_exec: pc {pc} ≠ {pcTarget}"
      let hfetch ← mkAppM ``AsmVerif.RiscV.Sym.fetch_of_codeAt #[c.hyp, mkNatLit i, hi, hprog, hpcEq]
      return ⟨c, i, ins, hfetch⟩
  throwError "sym_exec: pc {pc} is not covered by any `CodeAt` hypothesis"

def covered (st : St) (pc : Nat) : Bool :=
  st.codes.any fun c => c.base ≤ pc && pc < c.base + 4 * c.prog.size

/-! ## Steps -/

abbrev SymM := StateRefT St TacticM

def regName (i : Nat) : Name := Name.mkSimple s!"hx{i}"

/-- The shape of a successor state. -/
inductive Kind where
  | reg (rd : Nat) (v : Expr) (lin : Lin)
  | mem (ri ci : Nat) (addr newCell : Expr)
  | pc
  | ww (ri off : Nat) (a : Expr) (ws : Array Expr) (wsE : Expr)
  | commit
  deriving Inhabited

structure Step where
  shape : Expr
  kind : Kind
  newPc : Option Nat
  newPcE : Expr

def congrGetReg (i : Nat) (h : Expr) : MetaM Expr :=
  mkAppM ``congrArg #[mkLambda `t .default msTy (mkApp2 (mkConst ``MachineState.getReg) (mkBVar 0) (mkReg i)), h]

def congrProj (fn : Name) (h : Expr) : MetaM Expr :=
  mkAppM ``congrArg #[mkConst fn, h]

def shapePre (k : Kind) : String :=
  match k with
  | .reg .. => "regShape" | .mem .. => "memShape" | .pc => "pcShape"
  | .ww .. => "wwShape" | .commit => "commitShape"

/-- Prove a projection fact off the shape by the shape's lemma. -/
def proj (k : Kind) (field : String) (target : Expr) : MetaM Expr :=
  lemmaApp (`AsmVerif.RiscV.Sym ++ Name.mkSimple (shapePre k ++ "_" ++ field)) target

def wMem (st : St) (wi : Nat) : MetaM Expr := do
  let entries ← listElems st.W
  let prodTy ← mkAppM ``Prod #[wordTy, natTy]
  let mut memPf ← mkAppOptM ``List.mem_cons_self #[some prodTy, some entries[wi]!, some (mkListLit prodTy (entries.extract (wi+1) entries.size))]
  for j in (List.range wi).reverse do
    memPf ← mkAppM ``List.mem_cons_of_mem #[entries[j]!, memPf]
  return memPf

/-- A write-set entry with another base that covers `R` by its bounds (a heap block inside the
    heap range), with the `Covers` proof: the slot of a region `wSlot` cannot place. -/
def coverEntry (st : St) (R : RegionInfo) : TacticM (Option (Nat × Expr)) := do
  if let some (_, _, wi, h) := st.covers.find? (fun (b, n, _, _) => b == R.base && n == R.n) then
    return some (wi, h)
  -- only entries at a literal address (the heap range): a symbolic block cannot be placed by
  -- `omega` inside another variable's entry, and each failure costs a second
  for wi in [0:st.wEntries.size] do
    let we := st.wEntries[wi]!
    if we.baseLin.atom.isSome then continue
    let prop := mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Covers) we.base (mkNatLit we.n) R.base (mkNatLit R.n)
    if let some h ← proveByOmega prop then return some (wi, h)
  return none

/-- The hypotheses sharing a free variable or the head constant with `ty`: the context an
    `omega` or an `assumption` call saw, for an error message. -/
def relatedHyps (ty : Expr) : MetaM MessageData := do
  let fvs := (← ty.collectFVars.run {}).2.fvarIds
  let head := ty.getAppFn
  let mut md : MessageData := ""
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let tfvs := (← t.collectFVars.run {}).2.fvarIds
    if (fvs.size > 0 && tfvs.any fvs.contains) || (head.isConst && t.getAppFn == head) then
      md := md ++ m!"\n  {d.userName} : {t}"
  return md

/-- `offCode` and `nowrap` of every `RegionOk` fact in context, the segment bounds unfolded, as
    `Nat` facts for `omega`. Once per run; `false` when they were already there. -/
def addRegionOkFacts : SymM Bool := do
  if (← get).okFacts then return false
  modify fun st => { st with okFacts := true }
  let mut added := false
  let decls ← withMainContext do (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``AsmVerif.RiscV.Sym.RegionOk 4 then return acc.push d.toExpr else return acc
  for h in decls do
    for (proj, nm) in [(``AsmVerif.RiscV.Sym.RegionOk.offCode, `hok_off), (``AsmVerif.RiscV.Sym.RegionOk.nowrap, `hok_nw)] do
      let (ty, pf) ← withMainContext do
        let pf ← mkAppM proj #[h]
        let t ← instantiateMVars (← inferType pf)
        let r ← simpWith t (← layoutRules) #[] (dec := false)
        match r.proof? with
        | none => pure (t, pf)
        | some p => pure (r.expr, ← mkAppM ``Eq.mp #[p, pf])
      let _ ← addFact nm ty pf
      added := true
  return added

/-- The disjointness fact between two tracked regions, proved by `omega` and cached
    if it is not in context. -/
def getDisj (R₁ R₂ : RegionInfo) : SymM Expr := do
  let st ← get
  if let some pf ← lookupDisj st.disj R₁.base R₁.n R₂.base R₂.n then return pf
  let prop := mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Disjoint) R₁.base (mkNatLit R₁.n) R₂.base (mkNatLit R₂.n)
  let pf? ← withMainContext (lookupDisjSub st R₁.base R₁.n R₂.base R₂.n)
  let pf? ← match pf? with
    | some pf => pure (some pf)
    | none => withMainContext (proveByOmega prop)
  -- a region the caller only knows to lie off the image (`RegionOk roBase textHi b n`) against a
  -- read-only block: the `RegionOk` bounds, once, then again
  let pf? ← match pf? with
    | some pf => pure (some pf)
    | none => do
      if ← addRegionOkFacts then withMainContext (proveByOmega prop) else pure none
  let some pf := pf?
    | throwError "sym_exec: cannot show regions at {R₁.base} ({R₁.n}) and {R₂.base} ({R₂.n}) disjoint; the facts over their variables:{← withMainContext (relatedHyps prop)}"
  let fv ← addFact `hdisj prop pf
  modify fun st => { st with disj := st.disj.push (R₁.base, mkNatLit R₁.n, R₂.base, mkNatLit R₂.n, fv) }
  return fv

/-- `base.toNat + 8 n ≤ roBase ∨ roBase + roBytes ≤ base.toNat` for a region. -/
def roOutOf (li : LayoutInfo) (R : RegionInfo) : TacticM Expr := do
  if let some h := R.roOut then return h
  let toN ← mkAppM ``BitVec.toNat #[R.base]
  let ext ← mkAppM ``HAdd.hAdd #[toN, mkNatLit (8 * R.n)]
  let prop ← roOutProp li ext toN
  match ← proveByOmega prop with
  | some p =>
    -- stated with `8 * n` as the lemmas expect
    let ty ← roOutProp li (← mkAppM ``HAdd.hAdd #[toN, ← mkAppM ``HMul.hMul #[mkNatLit 8, mkNatLit R.n]]) toN
    mkExpectedTypeHint p ty
  | none => throwError "sym_exec: cannot show the region at {R.base} lies outside the read-only segment"

/-- A write-set entry `(b, n)` off the read-only segment through a tracked region containing
    it (`roOutOf`, then `roOut_sub`): an output block the frame facts alone do not place. -/
def roOutOfEntry (st : St) (b n : Expr) : TacticM (Option Expr) := do
  let some nv ← getNatValue? (← whnfD n) | return none
  let bl ← normLin b
  let some ba := bl.atom | return none
  for R in st.regions do
    if R.ok == noRegionOk then continue
    let some ra := R.baseLin.atom | continue
    unless ba == ra do continue
    if bl.c < R.baseLin.c then continue
    let d := bl.c - R.baseLin.c
    if d % 8 != 0 then continue
    let i := d / 8
    if i + nv > R.n then continue
    let roOut ← roOutOf (← st.layoutE) R
    let hnw ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.nowrap #[R.ok]
    let ha ← proveAddrEq st b (← cellAddr R.base i 0)
    let him ← mkDecideProof (natLeE (mkNatLit (i + nv)) (mkNatLit R.n))
    return some (← mkAppM ``AsmVerif.RiscV.Sym.roOut_sub #[roOut, hnw, mkNatLit i, mkNatLit nv, ha, him])
  return none

/-- `hd : Disjoint R.base R.n b n` as `Disjoint R.base R.listExpr.length b n`, the form the frame
    lemmas take; a cast through `lenPf` for an opaque region (a literal list's length is `R.n`
    by `rfl`). -/
def disjAsLength (R : RegionInfo) (hd : Expr) (b nE : Expr) : MetaM Expr := do
  let some hl := R.lenPf | return hd
  let motive ← withLocalDeclD `k natTy fun k => do
    mkLambdaFVars #[k] (mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Disjoint) R.base k b nE)
  mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, hl], hd]

/-- Derive the successor's facts. `hdef : shape = s'`. -/
def finish (sh : Step) (close : Expr → MetaM Expr) : SymM Unit := do
  -- disjointness facts the memory step needs, before the goal moves on
  let st0 ← get
  let tA ← IO.monoMsNow
  let mut disjFor : Array (Option Expr) := #[]
  match sh.kind with
  | .mem tri .. | .ww tri .. =>
    for ri in [0:st0.regions.size] do
      if ri == tri || st0.regions[ri]!.outW.isSome then disjFor := disjFor.push none
      else disjFor := disjFor.push (some (← getDisj st0.regions[ri]! st0.regions[tri]!))
  | _ => pure ()
  let tB ← IO.monoMsNow
  if tB - tA > 500 then trace[AsmVerif.sym.time] "  finish: disjointness {tB - tA} ms"
  let st ← get
  let (s', hdef) ← advance (sh.shape) (fun k => do
    let pf ← close k
    trace[AsmVerif.sym.size] "step {st.k} pc {st.pc}: close {dagSize (← instantiateMVars pf)} shape {dagSize sh.shape}"
    return pf) (st.k + 1)
  let tC ← IO.monoMsNow
  if tC - tB > 500 then trace[AsmVerif.sym.time] "  finish: advance/close {tC - tB} ms"
  -- pc
  let pcPf ← withMainContext do
    mkAppM ``AsmVerif.RiscV.Sym.pc_chain #[hdef, ← proj sh.kind "pc" (mkEqW (mkPc sh.shape) sh.newPcE)]
  let hpcF ← addFact `hpc (mkEqW (mkPc s') sh.newPcE) pcPf
  -- the register file
  let (list', regsPf) ← withMainContext do
    let pE := sh.newPcE
    match sh.kind with
    | .reg rd v _ =>
      if rd == 0 then
        pure (st.regList, ← mkAppM ``AsmVerif.RiscV.Sym.Regs.setReg0 #[st.hregs, v, pE])
      else
        let hlen ← rflOf (← mkEq (← mkAppM ``List.length #[st.regList]) (mkNatLit 32)) (mkNatLit 32)
        let pf ← mkAppM ``AsmVerif.RiscV.Sym.Regs.setReg #[st.hregs, hlen, mkNatLit rd, ← natLt rd 32,
          ← mkDecideProof (← mkAppM ``Ne #[mkNatLit rd, mkNatLit 0]), v, pE]
        pure (← regListSet st.regList rd v, pf)
    | .pc => pure (st.regList, ← mkAppM ``AsmVerif.RiscV.Sym.Regs.setPC #[st.hregs, pE])
    | .mem _ _ a v => pure (st.regList, ← mkAppM ``AsmVerif.RiscV.Sym.Regs.setMem #[st.hregs, a, v, pE])
    | .ww _ _ a _ wsE => pure (st.regList, ← mkAppM ``AsmVerif.RiscV.Sym.Regs.writeWords #[st.hregs, a, wsE, pE])
    | .commit => pure (st.regList, ← mkAppM ``AsmVerif.RiscV.Sym.Regs.commit #[st.hregs, pE])
  let hregsPf ← withMainContext do
    let pf ← mkAppM ``AsmVerif.RiscV.Sym.Regs.of_eq #[regsPf, hdef]
    mkExpectedTypeHint pf (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) s' list')
  let hregsF ← addFact `hregs (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) s' list') hregsPf
  trace[AsmVerif.sym.size] "  hregs {dagSize (← instantiateMVars hregsPf)} pc {dagSize pcPf}"
  let mut regs' := st.regs
  if let .reg rd v lin := sh.kind then
    if rd != 0 then regs' := regs'.set! rd (some ⟨v, lin, default⟩)
  -- code
  let (hcTy, hcPf) ← withMainContext do
    let target ← mkEq (mkApp (mkConst ``MachineState.code) sh.shape) (mkApp (mkConst ``MachineState.code) st.s)
    let pf ← mkAppM ``AsmVerif.RiscV.Sym.code_chain #[hdef, ← proj sh.kind "code" target, st.hcode]
    pure (← inferType pf, pf)
  let hcodeF ← addFact `hcode hcTy hcPf
  -- private input
  let priv' ← match st.priv with
    | none => pure none
    | some (v, pf) =>
      let (ty, pf') ← withMainContext do
        let target ← mkEq (mkApp (mkConst ``MachineState.privateInput) sh.shape) (mkApp (mkConst ``MachineState.privateInput) st.s)
        let pf' ← mkAppM ``AsmVerif.RiscV.Sym.priv_chain #[hdef, ← proj sh.kind "privateInput" target, pf]
        pure (← inferType pf', pf')
      let fv ← addFact `hpriv ty pf'
      pure (some (v, fv))
  -- memory
  let mut regions' : Array RegionInfo := st.regions
  let mut sM := st.sM
  let mut hmem := st.hmem
  let mut hunchM := st.hunchM
  let mut hroM := st.hroM
  let mut clearNow : Array FVarId := st.toClear
  let mut newClear : Array FVarId := #[hpcF.fvarId!, hregsF.fvarId!, hcodeF.fvarId!, hdef.fvarId!]
  if let some (_, pf) := priv' then newClear := newClear.push pf.fvarId!
  match sh.kind with
  | .mem .. | .ww .. =>
    regions' := #[]
    for ri in [0:st.regions.size] do
      let R := st.regions[ri]!
      if R.outW.isSome then
        regions' := regions'.push R
        continue
      let (ty, pf, R') ← withMainContext do
        match sh.kind with
        | .mem tri ci addr newCell =>
          if ri == tri then
            let cells' := R.cells.set! ci newCell
            let list' := mkListLit wordTy cells'
            let setExpr := mkApp4 (mkConst ``List.set [0]) wordTy R.listExpr (mkNatLit ci) newCell
            let hvs ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy setExpr list') list'
            let hiTy := natLtE (mkNatLit ci) (mkApp2 (mkConst ``List.length [0]) wordTy R.listExpr)
            let hi ← mkExpectedTypeHint (← natLt ci R.n) hiTy
            let ha ← mkEqRefl addr
            let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.set_sd #[R.hyp, R.ok, hi, hdef, ha, hvs]
            pure (← inferType pf, pf, { R with cells := cells', listExpr := list' })
          else
            let T := st.regions[tri]!
            let hd ← disjAsLength R disjFor[ri]!.get! T.base (mkNatLit T.n)
            let hj ← natLt ci T.n
            let ha ← mkEqRefl addr
            let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.frame_sd #[R.hyp, hd, hj, hdef, ha]
            pure (← inferType pf, pf, R)
        | .ww tri off a ws wsE =>
          if ri == tri then
            let cells' := (R.cells.extract 0 off) ++ ws ++ (R.cells.extract (off + ws.size) R.n)
            let list' := mkListLit wordTy cells'
            let lhs ← mkAppM ``HAppend.hAppend #[← mkAppM ``HAppend.hAppend #[← mkAppM ``List.take #[mkNatLit off, R.listExpr], wsE],
              ← mkAppM ``List.drop #[← mkAppM ``HAdd.hAdd #[mkNatLit off, ← mkAppM ``List.length #[wsE]], R.listExpr]]
            let hvs ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy lhs list') list'
            let hnw0 ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.nowrap #[← R.okE]
            let hnw ← mkExpectedTypeHint hnw0 (natLeE (← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[R.base],
              ← mkAppM ``HMul.hMul #[mkNatLit 8, ← mkAppM ``List.length #[R.listExpr]]]) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]))
            let hi ← mkDecideProof (natLeE (← mkAppM ``HAdd.hAdd #[mkNatLit off, ← mkAppM ``List.length #[wsE]]) (← mkAppM ``List.length #[R.listExpr]))
            let ha ← proveAddrEq st a (← cellAddr R.base off 0)
            let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.writeWords_sub #[R.hyp, hnw, wsE, hi, ha, hdef, hvs]
            pure (← inferType pf, pf, { R with cells := cells', listExpr := list' })
          else
            let T := st.regions[tri]!
            let hd ← disjAsLength R disjFor[ri]!.get! T.base (mkNatLit T.n)
            let hlen ← mkDecideProof (natLeE (← mkAppM ``HAdd.hAdd #[mkNatLit off, ← mkAppM ``List.length #[wsE]]) (mkNatLit T.n))
            let ha ← proveAddrEq st a (← cellAddr T.base off 0)
            let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.frame_writeWords_sub #[R.hyp, hd, hlen, ha, hdef]
            pure (← inferType pf, pf, R)
        | _ => throwError "unreachable"
      let fv ← addFact (Name.mkSimple s!"hR{ri}") ty pf
      if R.hypM.isFVar then clearNow := clearNow.push R.hypM.fvarId!
      regions' := regions'.push { R' with hypM := fv }
    let tD ← IO.monoMsNow
    if tD - tC > 500 then trace[AsmVerif.sym.time] "  finish: regions {tD - tC} ms"
    -- the frame
    let hunch' ← withMainContext do match sh.kind with
      | .mem tri ci addr _ =>
        let T := st.regions[tri]!
        match T.w with
        | some (wi, off) =>
          let we := st.wEntries[wi]!
          let memPf ← wMem st wi
          let hj ← natLt (off + ci) we.n
          let ha ← proveAddrEq st addr (← cellAddr we.base (off + ci) 0)
          mkAppM ``AsmVerif.RiscV.Sym.Unchanged.store #[st.hunch, memPf, hj, we.nw, hdef, ha]
        | none =>
          -- a region inside an entry with another base (a heap block in the heap range)
          let some (wi, hc) ← coverEntry st T
            | throwError "sym_exec: store into a region outside W (at {T.base})"
          let memPf ← wMem st wi
          let hi ← natLt ci T.n
          let hnw ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.nowrap #[← T.okE]
          let ha ← proveAddrEq st addr (← cellAddr T.base ci 0)
          mkAppM ``AsmVerif.RiscV.Sym.Unchanged.store_cover #[st.hunch, memPf, hc, hi, hnw, hdef, ha]
      | .ww tri off a _ wsE =>
        let T := st.regions[tri]!
        let some (wi, woff) := T.w | throwError "sym_exec: accelerator write into a region outside W"
        let we := st.wEntries[wi]!
        let memPf ← wMem st wi
        let hlen ← mkDecideProof (natLeE (← mkAppM ``HAdd.hAdd #[mkNatLit (woff + off), ← mkAppM ``List.length #[wsE]]) (mkNatLit we.n))
        let ha ← proveAddrEq st a (← cellAddr we.base (woff + off) 0)
        mkAppM ``AsmVerif.RiscV.Sym.Unchanged.writeWords_at #[st.hunch, memPf, mkNatLit (woff + off), hlen, we.nw, ha, hdef]
      | _ => throwError "unreachable"
    -- the read-only image survives a write outside it
    if let some hro := st.hro then
      let li ← st.layoutE
      let pf ← withMainContext do
        match sh.kind with
        | .mem tri ci _ v =>
          let T := st.regions[tri]!
          let roOut ← roOutOf li T
          let hnw ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.nowrap #[← T.okE]
          let ha ← mkAppM ``AsmVerif.RiscV.Sym.outsideRo_cell #[← natLt ci T.n, hnw, roOut]
          let pf ← mkAppM ``AsmVerif.RiscV.Sym.RoImage.setMem #[hro, ha, v, sh.newPcE]
          mkAppM ``AsmVerif.RiscV.Sym.RoImage.of_eq #[pf, hdef]
        | .ww _ _ a ws wsE =>
          let toN ← mkAppM ``BitVec.toNat #[a]
          let ext ← mkAppM ``HAdd.hAdd #[toN, mkNatLit (8 * ws.size)]
          let prop ← roOutProp li ext toN
          let some ha ← proveByOmega prop | throwError "sym_exec: accelerator write into the read-only segment?"
          let some hnw ← proveByOmega (natLeE ext (mkNatLit (2 ^ 64))) | throwError "sym_exec: accelerator write wraps"
          let lenE ← mkAppM ``List.length #[wsE]
          let ha ← mkExpectedTypeHint ha (← roOutProp li (← mkAppM ``HAdd.hAdd #[toN, ← mkAppM ``HMul.hMul #[mkNatLit 8, lenE]]) toN)
          let hnw ← mkExpectedTypeHint hnw (natLeE (← mkAppM ``HAdd.hAdd #[toN, ← mkAppM ``HMul.hMul #[mkNatLit 8, lenE]]) (← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]))
          let pf ← mkAppM ``AsmVerif.RiscV.Sym.RoImage.writeWords #[hro, ha, hnw, sh.newPcE]
          mkAppM ``AsmVerif.RiscV.Sym.RoImage.of_eq #[pf, hdef]
        | _ => throwError "unreachable"
      let fv ← addFact `hro (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.RoImage) li.L s') pf
      if let some h := st.hroM then if h.isFVar then clearNow := clearNow.push h.fvarId!
      hroM := some fv
    let hunchTy ← withMainContext do inferType hunch'
    let hunchF ← addFact `hunch hunchTy hunch'
    if st.hunchM.isFVar then clearNow := clearNow.push st.hunchM.fvarId!
    hunchM := hunchF
    sM := s'
    hmem ← withMainContext do mkEqRefl (mkApp (mkConst ``MachineState.mem) s')
  | k =>
    let (ty, pf) ← withMainContext do
      let target ← mkEq (mkApp (mkConst ``MachineState.mem) sh.shape) (mkApp (mkConst ``MachineState.mem) st.s)
      let pf ← mkAppM ``AsmVerif.RiscV.Sym.mem_chain #[hdef, ← proj k "mem" target, st.hmem]
      pure (← inferType pf, pf)
    let fv ← addFact `hmem ty pf
    newClear := newClear.push fv.fvarId!
    hmem := fv
  -- clear the superseded facts (a state still named by a fact survives)
  clearFacts clearNow
  if st.k > 0 && st.s != st.sM && st.s != st.s0 then clearFacts #[st.s.fvarId!]
  let st' := { st with s := s', pc := sh.newPc, pcE := sh.newPcE, hpc := hpcF, regs := regs', regList := list', hregs := hregsF, sM := sM, hmem := hmem, regions := regions', hcode := hcodeF, k := st.k + 1, hunchM := hunchM, hroM := hroM, priv := priv', toClear := newClear, pureFacts := ← liveFacts st.pureFacts }
  set (← withMainContext st'.refresh)

/-- The `execInstrBr` unfold lemma for a constructor. -/
def execLemma (ins : Expr) : MetaM Name := do
  let ins ← whnfD ins
  return `AsmVerif.RiscV.Sym ++ Name.mkSimple ("exec_" ++ ins.getAppFn.constName!.getString!)

/-- The value of register `i`, naming it by an atom if the executor does not know it. -/
def valueOf (i : Nat) : SymM RegFact := do
  let st ← get
  match st.regs[i]! with
  | some f => return f
  | none =>
    let e := mkGetReg st.s i
    let (a, h) ← atomize e wordTy (Name.mkSimple s!"r{i}_{st.k}")
    let f : RegFact := ⟨a, ⟨some a, 0⟩, h⟩
    modify fun st => { st with regs := st.regs.set! i (some f) }
    return f

/-- Normalize a raw value expression under the register facts. -/
def normValue (raw : Expr) (extra : Array Expr := #[]) : SymM (Expr × Expr × Lin) := do
  let st ← get
  withMainContext do
    let pr := st.pureFacts
    let (v, pf) ← rewriteTo raw (st.regRules ++ extra ++ #[st.hpc] ++ pr) normLemmas
    let l ← normLin v
    return (v, pf, l)

/-- Name a big non-linear value by an atom. -/
def maybeAtomize (v pf : Expr) (l : Lin) : SymM (Expr × Expr × Lin) := do
  match l.atom with
  | some a =>
    if a.isFVar || exprSize a < 12 then return (v, pf, l)
    let st ← get
    let (x, hx) ← atomize v wordTy (Name.mkSimple s!"v{st.k}")
    let pf' ← withMainContext do mkAppM ``Eq.trans #[pf, hx]
    return (x, pf', ⟨some x, 0⟩)
  | none => return (v, pf, l)

/-- `stepSp1 s = some (execInstrBr s ins)` for a non-memory, non-system instruction. -/
def plainStep (f : Fetched) : MetaM Expr := do
  let hmem ← rflOf (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp (mkConst ``Instr.isMemAccess) f.ins) (mkConst ``Bool.false)) (mkConst ``Bool.false)
  let hne1 ← mkDecideProof (mkApp3 (mkConst ``Ne [1]) (mkConst ``Instr) f.ins (mkConst ``Instr.ECALL))
  let hne2 ← mkDecideProof (mkApp3 (mkConst ``Ne [1]) (mkConst ``Instr) f.ins (mkConst ``Instr.EBREAK))
  mkAppM ``AsmVerif.RiscV.Sym.stepSp1_plain #[f.hfetch, hmem, hne1, hne2]

/-- The unfold lemma and its whole RHS. -/
def unfoldEq (s : Expr) (f : Fetched) : MetaM (Expr × Expr) := do
  let lem ← execLemma f.ins
  let args := (← whnfD f.ins).getAppArgs
  let eq ← mkAppM lem (#[s] ++ args)
  let eqTy ← inferType eq
  let some (_, _, rhs) := eqTy.eq? | throwError "exec lemma shape"
  return (eq, rhs)

/-- `close` for an ordinary step: `hstep : stepSp1 s = some X`, `hX : X = shape`. -/
def stepClose (hstep hX : Expr) (kMV : Expr) : MetaM Expr := do
  let hstep' ← mkAppM ``Eq.trans #[hstep, ← mkAppM ``congrArg #[mkApp (mkConst ``Option.some [0]) msTy, hX]]
  mkAppM ``AsmVerif.RiscV.Sym.Safe.step_gen #[hstep', kMV]

/-- A register-writing step from its raw value and raw pc. -/
def regStep (hstep : Expr) (rd : Nat) (rawV rawPc : Expr) (eq : Expr)
    (extra : Array Expr := #[]) : SymM Unit := do
  let t0 ← IO.monoMsNow
  let (v, hv, lin) ← normValue rawV extra
  -- a mask of a named value (`v &&& 7`, an alignment test): unfold the atoms,
  -- it may be a constant
  let (v, hv, lin) ← do
    let dflt := (v, hv, lin)
    if lin.atom.isNone || !v.isAppOfArity ``HAnd.hAnd 6 then pure dflt else
    let some c ← withMainContext (litValue? v.appArg!) | pure dflt
    -- alignment masks only (`&&& 7`, `&&& 3`, …), not the `zext.b` of a flag
    if c ≥ 8 then pure dflt else
    let st ← get
    withMainContext do
      let unf ← atomUnfoldRules v
      if unf.isEmpty && st.pureFacts.isEmpty then return dflt
      let (v', pf') ← rewriteTo v (unf ++ st.pureFacts) (normLemmas ++ #[``AsmVerif.RiscV.Sym.negw_and7, ``AsmVerif.RiscV.Sym.Meta.and7_add])
      let lin' ← normLin v'
      if lin'.atom.isSome then return dflt
      return (v', ← mkEqTrans hv pf', lin')
  -- `sext.w` (`addiw rd, rs, 0`) of a value below `2^31`, and `x <<< 32 >>> 32` of one below
  -- `2^32`, are the value (its width from its structure): an unsigned bounds check on `rd`
  -- then bounds the index the code shifts next, which `omega` cannot see through `signExtend`
  let (v, hv, lin) ← do
    let dflt := (v, hv, lin)
    let res? ← withMainContext do
      let isTrunc (e : Expr) := e.isAppOfArity ``BitVec.truncate 3 || e.isAppOfArity ``BitVec.setWidth 3
      let widthOk (x : Expr) (m : Nat) : MetaM (Option Expr) := do
        let some (k, hk) ← widthBound x | return none
        if k > m then return none
        if k == m then return some hk
        return some (← mkAppM ``AsmVerif.RiscV.Sym.wb_mono #[hk, ← mkDecideProof (natLeE (mkNatLit k) (mkNatLit m))])
      if v.isAppOfArity ``BitVec.signExtend 3 then
        let inner := v.appArg!
        let (core, add0) ← if inner.isAppOfArity ``HAdd.hAdd 6 then do
            let z := inner.appArg!
            let zz := if isTrunc z then z.appArg! else z
            if (← litValue? zz) == some 0 then pure (inner.appFn!.appArg!, true) else pure (inner, false)
          else pure (inner, false)
        if isTrunc core && (← getNatValue? core.appFn!.appArg!) == some 32 then
          let x := core.appArg!
          if let some hk ← widthOk x 31 then
            let lem := if add0 then ``AsmVerif.RiscV.Sym.sextw_add0_of_lt else ``AsmVerif.RiscV.Sym.sextw_of_lt
            return some (x, ← mkAppM lem #[hk])
        return none
      match_expr v with
      | HShiftRight.hShiftRight _ _ _ _ y c2 =>
        trace[AsmVerif.sym] "width: shr candidate {v}"
        unless (← litValue? c2) == some 32 || (← getNatValue? c2) == some 32 do return none
        -- `y` is the atom of the preceding `slli`: read it through its definition
        let (y', hy?) ← if y.isFVar then do
            let mut r : Option (Expr × Expr) := none   -- (rhs, h : rhs = y)
            for d in ← getLCtx do
              if d.isImplementationDetail then continue
              unless d.userName.toString.endsWith "_def" do continue
              if let some (_, rhs, a) := (← instantiateMVars d.type).eq? then
                if a == y then
                  r := some (rhs, d.toExpr)
                  break
            match r with
            | some (rhs, h) => pure (rhs, some h)
            | none => pure (y, none)
          else pure (y, none)
        match_expr y' with
        | HShiftLeft.hShiftLeft _ _ _ _ x c1 =>
          unless (← litValue? c1) == some 32 || (← getNatValue? c1) == some 32 do return none
          let some hk ← widthOk x 32 | return none
          let pf ← mkAppM ``AsmVerif.RiscV.Sym.shl_shr32_of_lt #[hk]      -- x <<< 32 >>> 32 = x
          match hy? with
          | none => return some (x, pf)
          | some h =>
            -- y >>> 32 = x <<< 32 >>> 32 = x
            let fn ← withLocalDeclD `w wordTy fun w => do mkLambdaFVars #[w] (← mkAppM ``HShiftRight.hShiftRight #[w, c2])
            let step ← mkCongrArg fn (← mkEqSymm h)
            return some (x, ← mkEqTrans (← mkExpectedTypeHint step (← mkEq v (← mkAppM ``HShiftRight.hShiftRight #[y', c2]))) pf)
        | _ => return none
      | _ => return none
    match res? with
    | some (x, pf) => withMainContext do
      trace[AsmVerif.sym] "width: {v} ~> {x}"
      pure (x, ← mkEqTrans hv pf, ← normLin x)
    | none => pure dflt
  let t1 ← IO.monoMsNow
  let (v, hv, lin) ← maybeAtomize v hv lin
  let (pcv, hpcv, pcl) ← normValue rawPc
  let t2 ← IO.monoMsNow
  if t1 - t0 > 1000 then
    trace[AsmVerif.sym.time] "slow normValue {t1 - t0} ms on {rawV} ~> {v}"
  if t2 - t1 > 1000 then trace[AsmVerif.sym.time] "slow atomize/pc {t2 - t1} ms"
  let st ← get
  let s := st.s
  let hshape ← withMainContext do
    mkAppM ``Eq.trans #[eq, ← mkAppM ``congr #[← mkAppM ``congrArg #[mkConst ``MachineState.setPC,
      ← mkAppM ``congrArg #[mkApp2 (mkConst ``MachineState.setReg) s (mkReg rd), hv]], hpcv]]
  let shape := mkSetPC (mkSetReg s rd v) pcv
  let newPc := match pcl.atom with | none => some pcl.c | some _ => none
  finish { shape, kind := .reg rd v lin, newPc, newPcE := pcv } (stepClose hstep hshape)

def mkMpr (pred : Name) (ha pf : Expr) : MetaM Expr := do
  let motive := mkLambda `a .default wordTy (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp (mkConst pred) (mkBVar 0)) (mkConst ``Bool.true))
  mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, ha], pf]

def memStepProof (f : Fetched) (hok : Expr) : MetaM Expr := do
  let hmemT ← rflOf (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp (mkConst ``Instr.isMemAccess) f.ins) (mkConst ``Bool.true)) (mkConst ``Bool.true)
  let hcsrs ← rflOf (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp (mkConst ``AsmVerif.RiscV.Sym.isCSRS) f.ins) (mkConst ``Bool.false)) (mkConst ``Bool.false)
  mkAppM ``AsmVerif.RiscV.Sym.stepSp1_mem #[f.hfetch, hmemT, hcsrs, hok]

def modZero (k m : Nat) : MetaM Expr := do
  natEq (← mkModN (mkNatLit k) (mkNatLit m)) (mkNatLit 0)

/-- A `pc`-only step whose target is decided. `hrest : rhs = s.setPC target`. -/
def pcStep (hstep eq hrest : Expr) (target : Nat) : SymM Unit := do
  let st ← get
  let pcv := mkWordLit target
  let shape := mkSetPC st.s pcv
  let hshape ← withMainContext do mkAppM ``Eq.trans #[eq, hrest]
  finish { shape, kind := .pc, newPc := some target, newPcE := pcv } (stepClose hstep hshape)

/-- Branch simp set. -/
def branchLemmas : Array Name := normLemmas ++ #[``BitVec.ult, ``BitVec.slt, ``bne, ``beq_iff_eq,
  ``BitVec.add_right_inj, ``BitVec.add_left_inj, ``decide_eq_true_eq, ``decide_eq_false_iff_not,
  ``Bool.not_eq_true, ``ite_true, ``ite_false, ``BitVec.ofNat_eq_ofNat, ``if_pos, ``if_neg,
  ``Bool.not_eq_false, ``bne_iff_ne, ``ne_eq, ``not_false_eq_true, ``not_true_eq_false]

/-! ## Loads and stores -/

/-- A load from the read-only segment: the chunk holding it, as a region. -/
def roChunkRegion (st : St) (al : Lin) (width : Nat) : MetaM (Option (RegionInfo × Nat × Nat)) := do
  let some hro := st.hro | return none
  let some li := st.layout | return none
  if al.atom.isSome then return none
  let a := al.c
  let lo := li.roBase
  if a < lo || a + width > lo + li.roBytes then return none
  let k := (a - lo) / 512
  let off := (a - lo) % 512
  let cells ← listElems (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Layout.roChunk) li.L (mkNatLit k))
  if off + width > 8 * cells.size || off % 8 + width > 8 then return none
  let listE := mkListLit wordTy cells
  let base := mkWordLit (lo + 512 * k)
  let hk ← mkDecideProof (natLtE (mkNatLit k) (mkApp (mkConst ``AsmVerif.RiscV.Sym.Layout.roChunks) li.L))
  let hyp ← mkExpectedTypeHint (← mkAppM ``AsmVerif.RiscV.Sym.RoImage.get #[hro, mkNatLit k, hk])
    (mkApp3 (mkConst ``AsmVerif.RiscV.Sym.Region) base listE st.s)
  let hcwTy ← inferType st.hcw
  let loE := hcwTy.getAppArgs[0]!
  let hiE := hcwTy.getAppArgs[1]!
  let hlo ← mkDecideProof (natLeE (← mkAppM ``HAdd.hAdd #[li.roBaseE, li.roBytesE]) loE)
  let ok ← mkAppM ``AsmVerif.RiscV.Sym.RoImage.ok #[li.L, loE, hiE, hlo, mkNatLit k, hk]
  let ok ← mkExpectedTypeHint ok (mkApp4 (mkConst ``AsmVerif.RiscV.Sym.RegionOk) loE hiE base (mkNatLit cells.size))
  let R : RegionInfo := ⟨base, Lin.lit (lo + 512 * k), cells.size, cells, listE, hyp, hyp, ok, none, none, none, none⟩
  return some (R, off / 8, off % 8)

/-- A fact with its statement normalised by the register facts and `normLemmas`,
    so that it matches subterms the goal's normalisation has already rewritten. -/
def normFactBy (rules : Array Expr) (h : Expr) : MetaM Expr := do
  let ty ← inferType h
  let r ← simpWith ty rules normLemmas
  if r.expr == ty || r.expr.isConstOf ``True then return h
  mkEqMP (← r.getProof) h

/-- A load at a symbolic offset into a tracked region: `addr = R.base + ofNat e`
    with `e` in bounds (and, for a doubleword, `8 ∣ e`). Returns the region, the
    offset `e` and the bound `e < 8 n`. -/
def symbolicLoc (st : St) (addr : Expr) (width : Nat) : TacticM (Option (RegionInfo × Expr × Expr)) := do
  -- unfold one atom first, so the offset stays over the atoms the branch facts name
  for lim in [1, 8] do
    for R in st.regions do
      if R.ok == noRegionOk then continue
      let d ← mkAppM ``HSub.hSub #[addr, R.base]
      let (dN, _) ← rewriteTo d (st.regRules ++ (← atomUnfoldRules addr lim)) #[``AsmVerif.RiscV.Sym.add_sub_cancel_left', ``AsmVerif.RiscV.Sym.add_add_sub_cancel_left',
        ``BitVec.add_zero, ``BitVec.zero_add, ``BitVec.sub_self, ``AsmVerif.RiscV.Sym.ofNat_ushiftRight,
        ``AsmVerif.RiscV.Sym.add_add_sub_add_cancel', ``BitVec.add_sub_cancel, ``AsmVerif.RiscV.Sym.add_add_sub_cancel_right',
        ``AsmVerif.RiscV.Sym.add_lit_sub_lit]
      trace[AsmVerif.sym] "symbolicLoc: {addr} - {R.base} ~> {dN}"
      -- an offset `d` that is a word expression, not `ofNat e`: read it as `ofNat d.toNat`
      let e ← match_expr dN with
        | BitVec.ofNat _ e => pure e
        | _ =>
          if R.lenPf.isNone || !dN.hasFVar || (dN.find? (·.isConstOf ``HSub.hSub)).isSome then continue
          mkAppM ``BitVec.toNat #[dN]
      if (← getNatValue? e).isSome && R.lenPf.isNone then continue
      let bound := natLtE e (mkNatLit (8 * R.n))
      let some hb ← proveByOmega bound (extras := true) | continue
      if width == 8 then
        let some _ ← proveByOmega (← mkEq (← mkAppM ``HMod.hMod #[e, mkNatLit 8]) (mkNatLit 0)) (extras := true) | continue
      return some (R, e, hb)
  return none

/-! ## Sub-word loads through sub-word stores (`asmverif.sym.foldBytes`) -/

/-- The definition `h : e = a` of an atom `a`, from its `_def` hypothesis. -/
def atomDef? (a : Expr) : MetaM (Option (Expr × Expr)) := do
  unless a.isFVar do return none
  let lctx ← getLCtx
  let r? ← lctx.findDeclRevM? fun d => do
    if d.isImplementationDetail then return none
    unless d.userName.toString.endsWith "_def" do return none
    let ty ← instantiateMVars d.type
    match ty.eq? with
    | some (_, lhs, rhs) => return (if rhs == a then some (lhs, d.toExpr) else none)
    | none => return none
  return r?

/-- `extractW c q` for a width of `W` bytes. -/
def mkExtractW (W : Nat) (c : Expr) (q : Nat) : Expr :=
  let f := match W with
    | 1 => ``RiscvZkvm.Rv64.extractByte
    | 2 => ``RiscvZkvm.Rv64.extractHalfword
    | _ => ``RiscvZkvm.Rv64.extractWord32
  mkApp2 (mkConst f) c (mkNatLit q)

/-- A store expression `replaceV w p x`: `(V, w, p, x)`. -/
def storeView? (e : Expr) : MetaM (Option (Nat × Expr × Nat × Expr)) := do
  let V? : Option Nat :=
    if e.isAppOfArity ``RiscvZkvm.Rv64.replaceByte 3 then some 1
    else if e.isAppOfArity ``RiscvZkvm.Rv64.replaceHalfword 3 then some 2
    else if e.isAppOfArity ``RiscvZkvm.Rv64.replaceWord32 3 then some 4
    else none
  let some V := V? | return none
  let some p ← getNatValue? e.appFn!.appArg! | return none
  return some (V, e.appFn!.appFn!.appArg!, p, e.appArg!)

/-- `extractW c q = v`: the `W`-byte unit `q` of the cell `c`, read through the stores that built
    it (skipping disjoint ones), down to the store that wrote exactly that unit, a literal cell,
    or a cell of a `List.replicate` atom. -/
partial def foldSubword (c : Expr) (W q : Nat) (fuel : Nat := 64) : MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return none
  let c ← instantiateMVars c
  let ext := mkExtractW W c q
  if (← litValue? c).isSome then return some (ext, ← mkEqRefl ext)
  -- `c = e`, `e` a store or a replicated cell
  let (e, hce) ← do
    if (← storeView? c).isSome then pure (c, ← mkEqRefl c)
    else if c.isAppOfArity ``GetElem?.getElem! 8 then pure (c, ← mkEqRefl c)
    else match ← atomDef? c with
      | some (e, h) => pure (e, ← mkEqSymm h)
      | none => return none
  let lam ← withLocalDeclD `x wordTy fun x => mkLambdaFVars #[x] (mkExtractW W x q)
  let h0 ← mkCongrArg lam hce          -- extractW c q = extractW e q
  if let some (V, w, p, x) ← storeView? e then
    if V == W && p == q then
      let h1 ← mkAppM (Name.mkStr `AsmVerif.RiscV.Sym s!"extract{W}_replace{W}_self") #[w, mkNatLit q, x, ← natLt q (8 / W)]
      return some (x, ← mkEqTrans h0 h1)
    if W * q + W ≤ V * p || V * p + V ≤ W * q then
      let some (v, h2) ← foldSubword w W q (fuel - 1) | return none
      let hdisj ← mkDecideProof (← mkAppM ``Or #[
        mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat) (mkNatLit (W * q + W)) (mkNatLit (V * p)),
        mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat) (mkNatLit (V * p + V)) (mkNatLit (W * q))])
      let h1 ← mkAppM (Name.mkStr `AsmVerif.RiscV.Sym s!"extract{W}_replace{V}_disj")
        #[w, mkNatLit q, mkNatLit p, x, ← natLt q (8 / W), ← natLt p (8 / V), hdisj]
      return some (v, ← mkEqTrans h0 (← mkEqTrans h1 h2))
    if V > W && V * p ≤ W * q && W * q + W ≤ V * p + V then
      -- the unit lies inside the stored one: a unit of the stored value
      let hin ← mkDecideProof (← mkAppM ``And #[
        mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat) (mkNatLit (V * p)) (mkNatLit (W * q)),
        mkApp4 (mkConst ``LE.le [0]) natTy (mkConst ``instLENat) (mkNatLit (W * q + W)) (mkNatLit (V * p + V))])
      let h1 ← mkAppM (Name.mkStr `AsmVerif.RiscV.Sym s!"extract{W}_replace{V}_in")
        #[w, mkNatLit q, mkNatLit p, x, ← natLt q (8 / W), ← natLt p (8 / V), hin]
      let xE ← mkAppM ``BitVec.zeroExtend #[mkNatLit 64, x]
      -- `q - (V/W)·p` as the lemma states it, then as a numeral
      let q' := q - V / W * p
      let hq ← mkEqRefl (mkNatLit q')
      let _ := hq
      let v := mkExtractW W xE q'
      let h1' ← mkAppM ``Eq.trans #[h1, ← mkEqRefl v]
      return some (v, ← mkEqTrans h0 h1')
    return none
  -- `acc[i]!` of an atom `acc = List.replicate n x`
  if e.isAppOfArity ``GetElem?.getElem! 8 then
    let acc := e.appFn!.appFn!.appArg!
    let some i ← getNatValue? e.appFn!.appArg! | return none
    let some (le, hl) ← atomDef? acc | return none
    unless le.isAppOfArity ``List.replicate 3 do return none
    let some n ← getNatValue? le.appFn!.appArg! | return none
    unless i < n do return none
    let x := le.appArg!
    unless (← litValue? x).isSome do return none
    -- acc[i]! = x
    let lamL ← withLocalDeclD `l (mkApp (mkConst ``List [0]) wordTy) fun l => do
      mkLambdaFVars #[l] (← mkAppM ``GetElem?.getElem! #[l, mkNatLit i])
    let hacc ← mkCongrArg lamL (← mkEqSymm hl)          -- acc[i]! = (replicate n x)[i]!
    let hrep ← mkAppM ``AsmVerif.RiscV.Sym.getElem!_replicate_word #[mkNatLit n, mkNatLit i, x, ← natLt i n]
    let hcell ← mkEqTrans hacc hrep                      -- e = x
    let h1 ← mkCongrArg lam hcell                        -- extractW e q = extractW x q
    return some (mkExtractW W x q, ← mkEqTrans h0 h1)
  return none

/-- The value of a closed bit-vector term of the shapes a folded load produces: a literal, a
    truncation or zero extension, or a unit of one. `(width, value)`. -/
partial def closedBV? (e : Expr) : MetaM (Option (Nat × Nat)) := do
  let e ← instantiateMVars e
  if let some ⟨w, v⟩ ← bvValue? e then return some (w, v.toNat)
  if e.isAppOfArity ``BitVec.truncate 3 || e.isAppOfArity ``BitVec.zeroExtend 3
      || e.isAppOfArity ``BitVec.setWidth 3 then
    let some b ← getNatValue? e.appFn!.appArg! | return none
    let some (_, v) ← closedBV? e.appArg! | return none
    return some (b, v % 2 ^ b)
  for (f, W) in [(``RiscvZkvm.Rv64.extractByte, 1), (``RiscvZkvm.Rv64.extractHalfword, 2),
      (``RiscvZkvm.Rv64.extractWord32, 4)] do
    if e.isAppOfArity f 2 then
      let some q ← getNatValue? e.appArg! | return none
      let some (_, v) ← closedBV? e.appFn!.appArg! | return none
      return some (8 * W, (v >>> (8 * W * q)) % 2 ^ (8 * W))
  return none

/-- The facts for a folded sub-word load: `extractW cell q = v`, and when `v` is a constant, its value
    and its zero and sign extensions. -/
def subwordFoldFacts (cell : Expr) (W k : Nat) : MetaM (Array Expr) := do
  unless (← getOptions).getBool `asmverif.sym.foldBytes false do return #[]
  if (← litValue? cell).isSome then return #[]
  let q := k / W
  let some (v, h) ← foldSubword cell W q
    | do trace[AsmVerif.sym] "byte fold: no fold for unit {q} of width {W} in {cell}"; return #[]
  trace[AsmVerif.sym] "byte fold: unit {q} of width {W} in {cell} is {v}"
  let bits := 8 * W
  -- the fact over the cell as `simp` will have normalised it by the time it reaches the load
  -- (an index into a literal list reduced, a literal folded): the fold then fires regardless
  -- of the traversal order
  let hs ← do
    let lhs := (← inferType h).eq?.get!.2.1
    let r ← simpWith lhs #[] normLemmas (dec := false)
    if r.expr == lhs then pure #[h]
    else match r.proof? with
      | some p => pure #[h, ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[p], h]]
      | none => pure #[h]
  let some (_, sub) ← closedBV? v | return hs
  let subE := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit bits) (mkNatLit sub)
  let h1 ← mkDecideProof (← mkEq v subE)
  let zE ← mkAppM ``BitVec.zeroExtend #[mkNatLit 64, subE]
  let h2 ← mkDecideProof (← mkEq zE (mkWordLit sub))
  let sgn := if sub ≥ 2 ^ (bits - 1) then sub + (2 ^ 64 - 2 ^ bits) else sub
  let sE ← mkAppM ``BitVec.signExtend #[mkNatLit 64, subE]
  let h3 ← mkDecideProof (← mkEq sE (mkWordLit sgn))
  return hs ++ #[h1, h2, h3]

/-- A doubleword load of a cell of a `List.replicate` atom with a literal element: that literal. -/
def replicateCellFacts (cell : Expr) : MetaM (Array Expr) := do
  unless (← getOptions).getBool `asmverif.sym.foldBytes false do return #[]
  let cell ← instantiateMVars cell
  unless cell.isAppOfArity ``GetElem?.getElem! 8 do return #[]
  let acc := cell.appFn!.appFn!.appArg!
  let some i ← getNatValue? cell.appFn!.appArg! | return #[]
  let some (le, hl) ← atomDef? acc | return #[]
  unless le.isAppOfArity ``List.replicate 3 do return #[]
  let some n ← getNatValue? le.appFn!.appArg! | return #[]
  unless i < n do return #[]
  let x := le.appArg!
  unless (← litValue? x).isSome do return #[]
  let lamL ← withLocalDeclD `l (mkApp (mkConst ``List [0]) wordTy) fun l => do
    mkLambdaFVars #[l] (← mkAppM ``GetElem?.getElem! #[l, mkNatLit i])
  let hacc ← mkCongrArg lamL (← mkEqSymm hl)
  let hrep ← mkAppM ``AsmVerif.RiscV.Sym.getElem!_replicate_word #[mkNatLit n, mkNatLit i, x, ← natLt i n]
  return #[← mkEqTrans hacc hrep]

def symbolicLoad (f : Fetched) (rd rs1 width : Nat) (signed : Bool) (R : RegionInfo) (e hb : Expr) :
    SymM Unit := do
  let st ← get
  let s := st.s
  let (hstep, eq, rawV, pcE, extra) ← withMainContext do
    let args := (← whnfD f.ins).getAppArgs
    let rawAddr ← mkAdd (mkGetReg s rs1) (mkApp (mkConst ``signExtend12) args[2]!)
    let iE ← mkAppM ``HDiv.hDiv #[e, mkNatLit 8]
    let kE ← mkAppM ``HMod.hMod #[e, mkNatLit 8]
    let some hi ← proveByOmega (natLtE iE (mkNatLit R.n)) (extras := true) | throwError "sym_exec: symbolic load bound"
    let some hk ← proveByOmega (natLtE kE (mkNatLit 8)) (extras := true) | throwError "sym_exec: symbolic load offset"
    let target ← if width == 8 then
        mkAdd R.base (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (← mkMulN (mkNatLit 8) iE))
      else
        mkAdd R.base (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (← mkAddN (← mkMulN (mkNatLit 8) iE) kE))
    -- `rawAddr = R.base + ofNat e` by normalisation (both sides unfold the same atoms), then
    -- `e = 8 (e / 8) [+ e % 8]` by `omega` / `Nat.div_add_mod` gives `rawAddr = target`; the
    -- split is applied after the simp since the simp unfolds the atoms inside `e` as well
    let hsplit ← if width == 8 then
        match ← proveByOmega (← mkEq (← mkMulN (mkNatLit 8) iE) e) (extras := true) with
        | some p => pure p
        | none => throwError "sym_exec: symbolic load alignment"
      else mkAppM ``Nat.div_add_mod #[e, mkNatLit 8]
    let addrN ← mkAdd R.base (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) e)
    let fnE ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] (← mkAdd R.base (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) k))
    let fix (h raw : Expr) : MetaM Expr := do
      mkExpectedTypeHint (← mkEqTrans h (← mkCongrArg fnE (← mkEqSymm hsplit))) (mkEqW raw target)
    let unf ← atomUnfoldRules (← rewriteTo rawAddr st.regRules normLemmas).1
    let addrSimp := normLemmas ++ #[``AsmVerif.RiscV.Sym.ofNat_ushiftRight, ``BitVec.ofNat_toNat, ``BitVec.setWidth_eq]
    let ha ← match ← proveBySimp (mkEqW rawAddr addrN) (st.regRules ++ unf) addrSimp with
      | some p => fix p rawAddr
      | none => throwError "sym_exec: symbolic load address {rawAddr} = {addrN}"
    let pre : Array (Option Expr) := #[some s, some (mkReg rd), some (mkReg rs1), some args[2]!]
    let hok : Expr ← if width == 8 then
        mkAppOptM ``AsmVerif.RiscV.Sym.memOk_LD (pre ++ #[some (← mkMpr ``isValidDwordAccessSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.dwordOk #[← R.okE, hi]))])
      else if width == 1 then
        let ad ← mkMpr ``isValidMemAddrSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.addrOk #[← R.okE, hi, hk])
        mkAppOptM (if signed then ``AsmVerif.RiscV.Sym.memOk_LB else ``AsmVerif.RiscV.Sym.memOk_LBU) (pre ++ #[some ad])
      else throwError "sym_exec: symbolic loads of width {width} are not supported"
    let hstep ← memStepProof f hok
    let hiL ← match R.lenPf with
      | some h => mkAppM ``Nat.lt_of_lt_of_eq #[hi, ← mkEqSymm h]
      | none => mkExpectedTypeHint hi (natLtE iE (← mkAppM ``List.length #[R.listExpr]))
    let hget ← mkAppM ``AsmVerif.RiscV.Sym.Region.get' #[R.hyp, iE, hiL]
    let (eq, rhs) ← unfoldEq s f
    let setRegE := rhs.getAppArgs[0]!
    let rawV := setRegE.getAppArgs[2]!
    let pcE := rhs.getAppArgs[1]!
    -- the loaded value at the normalised address `R.base + ofNat e`
    let (rawN, _) ← rewriteTo rawAddr st.regRules normLemmas
    let haN ← match ← proveBySimp (mkEqW rawN addrN) unf addrSimp with
      | some p => fix p rawN
      | none => throwError "sym_exec: symbolic load address {rawN} = {addrN}"
    let extra ← if width == 1 then do
        let hc ← mkAppM ``AsmVerif.RiscV.Sym.getByte_cell #[← R.okE, hi, hk, s, haN]
        -- `s.getByte rawN = extractByte (vs[e/8]!) (e%8)`
        let hv ← mkAppM ``Eq.trans #[hc, ← mkAppM ``congrArg #[
          ← withLocalDeclD `w wordTy fun w => do mkLambdaFVars #[w] (← mkAppM ``extractByte #[w, kE]), hget]]
        pure #[hv, ha]
      else do
        let hv ← mkAppM ``Eq.trans #[← mkAppM ``congrArg #[mkApp (mkConst ``MachineState.getMem) s, haN], hget]
        pure #[hv, ha]
    let _ := hb
    pure (hstep, eq, rawV, pcE, extra)
  regStep hstep rd rawV pcE eq extra

def loadStep (f : Fetched) (rd rs1 off width : Nat) (signed : Bool) : SymM Bool := do
  let base ← valueOf rs1
  let st ← get
  let s := st.s
  let al := base.lin.addC (sext 12 off)
  let found ← match findRegion? st al width with
    | some (ri, ci, k) => pure (some (st.regions[ri]!, ci, k))
    | none => withMainContext (roChunkRegion st al width)
  let some (R, ci, k) := found | do
      if let some (R, e, hb) ← withMainContext (symbolicLoc st (← withMainContext al.toExpr) width) then
        symbolicLoad f rd rs1 width signed R e hb
        return true
      logInfo m!"sym_exec: stopping at load from {← withMainContext al.toExpr} at pc {st.pc}: no region"; return false
  let (hstep, eq, rawV, pcE, extra) ← withMainContext do
    let args := (← whnfD f.ins).getAppArgs
    let rawAddr ← mkAdd (mkGetReg s rs1) (mkApp (mkConst ``signExtend12) args[2]!)
    let ha ← proveAddr st rawAddr R ci k
    let hi ← natLt ci R.n
    let hk ← natLt k 8
    let pre : Array (Option Expr) := #[some s, some (mkReg rd), some (mkReg rs1), some args[2]!]
    let hok : Expr ← if width == 8 then
        mkAppOptM ``AsmVerif.RiscV.Sym.memOk_LD (pre ++ #[some (← mkMpr ``isValidDwordAccessSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.dwordOk #[← R.okE, hi]))])
      else
        let ad ← mkMpr ``isValidMemAddrSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.addrOk #[← R.okE, hi, hk])
        match width with
        | 4 =>
          let al ← mkMpr ``isAligned4 ha (← mkAppM ``AsmVerif.RiscV.Sym.aligned4Ok #[← R.okE, hi, hk, ← modZero k 4])
          mkAppOptM (if signed then ``AsmVerif.RiscV.Sym.memOk_LW else ``AsmVerif.RiscV.Sym.memOk_LWU) (pre ++ #[some ad, some al])
        | 2 =>
          let al ← mkMpr ``isAligned2 ha (← mkAppM ``AsmVerif.RiscV.Sym.aligned2Ok #[← R.okE, hi, hk, ← modZero k 2])
          mkAppOptM (if signed then ``AsmVerif.RiscV.Sym.memOk_LH else ``AsmVerif.RiscV.Sym.memOk_LHU) (pre ++ #[some ad, some al])
        | _ => mkAppOptM (if signed then ``AsmVerif.RiscV.Sym.memOk_LB else ``AsmVerif.RiscV.Sym.memOk_LBU) (pre ++ #[some ad])
    let hstep ← memStepProof f hok
    let hget ← cellFact st R ci hi
    let (eq, rhs) ← unfoldEq s f
    let setRegE := rhs.getAppArgs[0]!
    let rawV := setRegE.getAppArgs[2]!
    let pcE := rhs.getAppArgs[1]!
    let cellLemma? : Option Expr ← match width with
      | 4 => some <$> mkAppM ``AsmVerif.RiscV.Sym.getWord32_cell #[← R.okE, hi, hk, s, ha]
      | 2 => some <$> mkAppM ``AsmVerif.RiscV.Sym.getHalfword_cell #[← R.okE, hi, hk, s, ha]
      | 1 => some <$> mkAppM ``AsmVerif.RiscV.Sym.getByte_cell #[← R.okE, hi, hk, s, ha]
      | _ => pure none
    let cellLemma? ← cellLemma?.mapM fun h => (normFactBy st.regRules h : MetaM Expr)
    -- a sub-word of a literal cell (a jump table, a constant table) is a literal: the
    -- extraction and the extension, each by `decide`
    let folds : Array Expr ← do
      let some c ← litValue? R.cells[ci]! | pure #[]
      if width == 8 then pure #[] else
      let bits := 8 * width
      let sub := (c >>> (8 * (k / width * width))) % (2 ^ bits)
      let subE := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit bits) (mkNatLit sub)
      let extrE ← match width with
        | 4 => pure (mkApp2 (mkConst ``RiscvZkvm.Rv64.extractWord32) R.cells[ci]! (mkNatLit (k / 4)))
        | 2 => pure (mkApp2 (mkConst ``RiscvZkvm.Rv64.extractHalfword) R.cells[ci]! (mkNatLit (k / 2)))
        | _ => pure (mkApp2 (mkConst ``RiscvZkvm.Rv64.extractByte) R.cells[ci]! (mkNatLit k))
      let h1 ← mkDecideProof (← mkEq extrE subE)
      let zE ← mkAppM ``BitVec.zeroExtend #[mkNatLit 64, subE]
      let h2 ← mkDecideProof (← mkEq zE (mkWordLit sub))
      let sgn := if sub ≥ 2 ^ (bits - 1) then sub + (2 ^ 64 - 2 ^ bits) else sub
      let sE ← mkAppM ``BitVec.signExtend #[mkNatLit 64, subE]
      let h3 ← mkDecideProof (← mkEq sE (mkWordLit sgn))
      pure #[h1, h2, h3]
    let bfold ← if width == 8 then replicateCellFacts R.cells[ci]! else subwordFoldFacts R.cells[ci]! width k
    let extra := (match cellLemma? with | some l => #[l] | none => #[ha]) ++ #[hget] ++ folds ++ bfold
    pure (hstep, eq, rawV, pcE, extra)
  regStep hstep rd rawV pcE eq extra
  return true

def storeStep (f : Fetched) (rs1 rs2 off width : Nat) : SymM Bool := do
  let base ← valueOf rs1
  let _ ← valueOf rs2
  let st ← get
  let s := st.s
  let al := base.lin.addC (sext 12 off)
  let some (ri, ci, k) := findRegion? st al width
    | do logInfo m!"sym_exec: stopping at store to {← al.toExpr} at pc {st.pc}: no region"; return false
  let R := st.regions[ri]!
  if R.w.isNone then
    match ← withMainContext (coverEntry st R) with
    | none => throwError "sym_exec: store into read-only region at {R.base}, pc {st.pc}"
    | some (wi, h) =>
      unless st.covers.any (fun (b, n, _, _) => b == R.base && n == R.n) do
        modify fun st => { st with covers := st.covers.push (R.base, R.n, wi, h) }
  let (hstep, eq, rhs, cellAddrE, hget, hcellL?) ← withMainContext do
    let args := (← whnfD f.ins).getAppArgs
    let rawAddr ← mkAdd (mkGetReg s rs1) (mkApp (mkConst ``signExtend12) args[2]!)
    let ha ← proveAddr st rawAddr R ci k
    let hi ← natLt ci R.n
    let hk ← natLt k 8
    let hw ← natLt 0 width
    let hkw ← natLe (k + width) 8
    let hnc ← mkAppM ``AsmVerif.RiscV.Sym.noCodeOk #[← R.okE, st.hcw, hi, hk, hw, hkw]
    let hnc' ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[mkLambda `a .default wordTy (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkApp3 (mkConst ``noCodeAt) s (mkBVar 0) (mkNatLit width)) (mkConst ``Bool.true)), ha], hnc]
    let pre : Array (Option Expr) := #[some s, some (mkReg rs1), some (mkReg rs2), some args[2]!]
    let hok : Expr ← match width with
      | 8 => mkAppOptM ``AsmVerif.RiscV.Sym.memOk_SD (pre ++ #[some (← mkMpr ``isValidDwordAccessSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.dwordOk #[← R.okE, hi])), some hnc'])
      | 4 =>
        let ad ← mkMpr ``isValidMemAddrSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.addrOk #[← R.okE, hi, hk])
        let al ← mkMpr ``isAligned4 ha (← mkAppM ``AsmVerif.RiscV.Sym.aligned4Ok #[← R.okE, hi, hk, ← modZero k 4])
        mkAppOptM ``AsmVerif.RiscV.Sym.memOk_SW (pre ++ #[some ad, some al, some hnc'])
      | 2 =>
        let ad ← mkMpr ``isValidMemAddrSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.addrOk #[← R.okE, hi, hk])
        let al ← mkMpr ``isAligned2 ha (← mkAppM ``AsmVerif.RiscV.Sym.aligned2Ok #[← R.okE, hi, hk, ← modZero k 2])
        mkAppOptM ``AsmVerif.RiscV.Sym.memOk_SH (pre ++ #[some ad, some al, some hnc'])
      | _ =>
        let ad ← mkMpr ``isValidMemAddrSp1 ha (← mkAppM ``AsmVerif.RiscV.Sym.addrOk #[← R.okE, hi, hk])
        mkAppOptM ``AsmVerif.RiscV.Sym.memOk_SB (pre ++ #[some ad, some hnc'])
    let hstep ← memStepProof f hok
    let hget ← cellFact st R ci hi
    let (eq, rhs) ← unfoldEq s f
    let cellAddrE ← cellAddr R.base ci 0
    let trunc (w : Nat) : Expr := mkApp3 (mkConst ``BitVec.truncate) (mkNatLit 64) (mkNatLit w) (mkGetReg s rs2)
    let cellLemma? : Option Expr ← match width with
      | 4 => some <$> mkAppM ``AsmVerif.RiscV.Sym.setWord32_cell #[← R.okE, hi, hk, s, trunc 32, ha]
      | 2 => some <$> mkAppM ``AsmVerif.RiscV.Sym.setHalfword_cell #[← R.okE, hi, hk, s, trunc 16, ha]
      | 1 => some <$> mkAppM ``AsmVerif.RiscV.Sym.setByte_cell #[← R.okE, hi, hk, s, trunc 8, ha]
      | _ => pure none
    -- stated over the normalised address and value, as the goal's subterms will be
    let cellLemma? ← cellLemma?.mapM fun h => (normFactBy st.regRules h : MetaM Expr)
    pure (hstep, eq, rhs, cellAddrE, hget, cellLemma?)
  let cellVal := R.cells[ci]!
  let trunc (w : Nat) : Expr := mkApp3 (mkConst ``BitVec.truncate) (mkNatLit 64) (mkNatLit w) (mkGetReg s rs2)
  let newCellRaw : Expr := match width with
    | 8 => mkGetReg s rs2
    | 4 => mkApp3 (mkConst ``replaceWord32) cellVal (mkNatLit (k / 4)) (trunc 32)
    | 2 => mkApp3 (mkConst ``replaceHalfword) cellVal (mkNatLit (k / 2)) (trunc 16)
    | _ => mkApp3 (mkConst ``replaceByte) cellVal (mkNatLit k) (trunc 8)
  let (newCell, _, ncl) ← normValue newCellRaw
  let newCell0 := newCell
  let (newCell, hAtom, _) ← maybeAtomize newCell (← withMainContext (mkEqRefl newCell)) ncl
  -- `hAtom : newCell0 = newCell`; a rule only when an atom was introduced
  let atomDefs := if newCell == newCell0 then #[] else #[hAtom]
  let pcE := rhs.getAppArgs[1]!
  let (pcv, hpcv, _) ← normValue pcE
  let st ← get
  let shape := mkSetPC (mkSetMem s cellAddrE newCell) pcv
  let tS ← IO.monoMsNow
  let hshape ← withMainContext do
    let pr := st.pureFacts
    let prop := mkApp3 (mkConst ``Eq [1]) msTy rhs shape
    -- the atom definitions, oriented `expr = atom`, fold the value back into its name
    let extra := (match hcellL? with | some l => #[l] | none => #[]) ++ #[hget, hpcv, st.hpc] ++ st.regRules ++ pr ++ atomDefs
    let some hrest ← proveBySimp prop extra normLemmas
      | do
        let r ← simpWith prop extra normLemmas
        throwError "sym_exec: store shape at pc {st.pc} did not normalize: {r.expr}"
    mkAppM ``Eq.trans #[eq, hrest]
  let tS' ← IO.monoMsNow
  if tS' - tS > 500 then trace[AsmVerif.sym.time] "  store: shape {tS' - tS} ms"
  finish { shape, kind := .mem ri ci cellAddrE newCell, newPc := some ((st.pc.getD 0 + 4) % two64), newPcE := pcv }
    (stepClose hstep hshape)
  return true

/-! ## System calls -/

/-- `natToLeLimbs 4 v` as a literal list. -/
def limbs4 (v : Expr) : MetaM (Array Expr × Expr) := do
  let e ← mkAppM ``RiscvZkvm.Rv64.Accel.natToLeLimbs #[mkNatLit 4, v]
  let cells ← listElems e
  return (cells, mkListLit wordTy cells)

/-- `ECALL`. Returns `true` to continue, `false` to stop. -/
def ecallStep (f : Fetched) : SymM Bool := do
  let t0 ← valueOf 5
  let st ← get
  let s := st.s
  let some id := (if t0.lin.atom.isNone then some t0.lin.c else none)
    | do logInfo m!"sym_exec: stopping at ECALL with symbolic t0 at pc {st.pc}"; return false
  let pc4 := ((st.pc.getD 0) + 4) % two64
  let pcv := mkWordLit pc4
  let hpc4 ← withMainContext do
    match ← proveBySimp (mkEqW (← mkAdd (mkPc s) (mkWordLit 4)) pcv) #[st.hpc] normLemmas with
    | some p => pure p
    | none => throwError "sym_exec: pc + 4"
  let idLit := mkWordLit id
  let ht0 ← withMainContext do
    match ← proveBySimp (mkEqW (mkGetReg s 5) idLit) #[t0.proof] normLemmas with
    | some p => pure p
    | none => throwError "sym_exec: t0"
  if id == 0 then
    let a0 ← valueOf 10
    if a0.lin.atom.isNone && a0.lin.c != 0 then
      let g ← getMainGoal
      g.withContext do
        let hne ← match ← proveBySimp (← mkAppM ``Ne #[mkGetReg s 10, mkWordLit 0]) #[a0.proof] normLemmas with
          | some p => pure p
          | none => throwError "sym_exec: a0 ≠ 0"
        let (P, _) ← goalParts g
        g.assign (← mkAppOptM ``AsmVerif.RiscV.Sym.Safe.reject #[some P, some s, some f.hfetch,
          some (← mkExpectedTypeHint ht0 (mkEqW (mkGetReg s 5) (mkWordLit 0))), some hne])
      replaceMainGoal []
      logInfo m!"sym_exec: rejecting HALT (a0 = {a0.lin.c}) at pc {st.pc}"
      return false
    logInfo m!"sym_exec: stopping at HALT at pc {st.pc}"
    return false
  if id == 0x10 || id == 0x1a then
    -- COMMIT / COMMIT_DEFERRED_PROOFS
    let isCommit := id == 0x10
    let lem := if isCommit then ``AsmVerif.RiscV.Sym.Safe.commit else ``AsmVerif.RiscV.Sym.Safe.commitDeferred
    let idE := if isCommit then mkConst ``Sp1.COMMIT else mkConst ``Sp1.COMMIT_DEFERRED_PROOFS
    let base := if isCommit then mkApp (mkConst ``MachineState.sp1Commit) s else s
    let orig := mkSetPC base (← withMainContext (mkAdd (mkPc s) (mkWordLit 4)))
    let shape := mkSetPC base pcv
    let close (kMV : Expr) : MetaM Expr := do
      let heq ← mkAppM ``congrArg #[mkApp (mkConst ``MachineState.setPC) base, hpc4]  -- orig = shape
      let k' ← withLocalDeclD `t msTy fun t => do
        withLocalDeclD `h (mkEqMS orig t) fun h => do
          mkLambdaFVars #[t, h] (mkApp2 kMV t (← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[heq], h]))
      let ht0' ← mkExpectedTypeHint ht0 (mkEqW (mkGetReg s 5) idE)
      mkAppM lem #[f.hfetch, ht0', k']
    finish { shape, kind := if isCommit then .commit else .pc, newPc := some pc4, newPcE := pcv } close
    return true
  if id == 0x1011d || id == 0x10136 || id == 0x137 then
    let a0 ← valueOf 10
    let a1 ← valueOf 11
    let st ← get
    let isMul := id == 0x1011d
    let isAdd := id == 0x10136
    let m0 := if isMul then 4 else 8
    let some (r0, i0) := findBlock? st a0.lin m0
      | do logInfo m!"sym_exec: stopping at accelerator: no region for a0 at pc {st.pc}"; return false
    let (hx, xs, xE) ← withMainContext (subRegion st st.regions[r0]! i0 m0 a0.val)
    let hxl ← withMainContext do rflOf (← mkEq (← mkAppM ``List.length #[xE]) (mkNatLit m0)) (mkNatLit m0)
    let _ := xs
    -- second operand (not for DOUBLE)
    let snd ← if id == 0x137 then pure none else do
      let some (r1, i1) := findBlock? st a1.lin 8
        | throwError "sym_exec: accelerator: no region for a1 at pc {st.pc}"
      let (hy, _, yE) ← withMainContext (subRegion st st.regions[r1]! i1 8 a1.val)
      let hyl ← withMainContext do rflOf (← mkEq (← mkAppM ``List.length #[yE]) (mkNatLit 8)) (mkNatLit 8)
      pure (some (hy, yE, hyl))
    -- the result, named
    let (resE, resTy) ← withMainContext do
      if isMul then
        let (_, yE, _) := snd.get!
        let X ← mkAppM ``RiscvZkvm.Rv64.Accel.leLimbsToNat #[xE]
        let ys ← listElems yE
        let Y ← mkAppM ``RiscvZkvm.Rv64.Accel.leLimbsToNat #[mkListLit wordTy (ys.extract 0 4)]
        let M ← mkAppM ``RiscvZkvm.Rv64.Accel.leLimbsToNat #[mkListLit wordTy (ys.extract 4 8)]
        pure (← mkModN (← mkMulN X Y) M, natTy)
      else if isAdd then
        let (_, yE, _) := snd.get!
        pure (← mkAppM ``RiscvZkvm.Rv64.Accel.curveAddL #[mkConst ``Sp1.pallasP, mkNatLit 4, xE, yE], listWordTy)
      else
        pure (← mkAppM ``RiscvZkvm.Rv64.Accel.curveDblL #[mkConst ``Sp1.pallasP, mkNatLit 4, xE], listWordTy)
    let (v, hv) ← atomize resE resTy (Name.mkSimple s!"acc{st.k}")
    let st ← get
    let s := st.s
    -- the written cells: `natToLeLimbs 4 v` for a product, eight opaque limbs of `v` for a point
    let (ws, wsE) ← withMainContext do
      if isMul then limbs4 v
      else
        let cells ← (List.range 8).toArray.mapM fun i => mkAppM ``GetElem?.getElem! #[v, mkNatLit i]
        pure (cells, mkListLit wordTy cells)
    let shape := mkSetPC (mkApp3 (mkConst ``MachineState.writeWords) s a0.val wsE) pcv
    let close (kMV : Expr) : MetaM Expr := do
      -- orig: (s.writeWords a0 (F resE)).setPC (s.pc + 4)
      let pcPlus ← mkAdd (mkPc s) (mkWordLit 4)
      let F : Expr → MetaM Expr := fun r => do
        if isMul then mkAppM ``RiscvZkvm.Rv64.Accel.natToLeLimbs #[mkNatLit 4, r] else pure r
      let fnE ← withLocalDeclD `r resTy fun r => do
        withLocalDeclD `p wordTy fun p => do
          mkLambdaFVars #[r, p] (mkSetPC (mkApp3 (mkConst ``MachineState.writeWords) s a0.val (← F r)) p)
      let heq ← mkAppM ``congr #[← mkAppM ``congrArg #[fnE, hv], hpc4]   -- orig = shapeV
      let orig := mkSetPC (mkApp3 (mkConst ``MachineState.writeWords) s a0.val (← F resE)) pcPlus
      -- For a product `shapeV` is defeq to `shape` (the literal list). For a point, `v`
      -- is a list atom, expanded to `[v[0]!, …, v[7]!]` through its length.
      let heq ← if isMul then pure heq else do
        let hlen0 ← if isAdd then
            let (_, yE, _) := snd.get!
            mkAppM ``AsmVerif.RiscV.Sym.length_curveAddL #[xE, yE]
          else mkAppM ``AsmVerif.RiscV.Sym.length_curveDblL #[xE]
        let hlenV ← mkAppM ``Eq.trans #[← mkAppM ``congrArg #[mkConst ``List.length [0] |>.app wordTy, ← mkAppM ``Eq.symm #[hv]], hlen0]
        let hexp ← mkAppM ``AsmVerif.RiscV.Sym.List.eq_map_range #[v, hlenV]
        let mapE := (← inferType hexp).appArg!
        let hexp' ← mkAppM ``Eq.trans #[hexp, ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy mapE wsE) wsE]
        let fn2 ← withLocalDeclD `L listWordTy fun L => do
          mkLambdaFVars #[L] (mkSetPC (mkApp3 (mkConst ``MachineState.writeWords) s a0.val L) pcv)
        mkAppM ``Eq.trans #[heq, ← mkAppM ``congrArg #[fn2, hexp']]
      let k' ← withLocalDeclD `t msTy fun t => do
        withLocalDeclD `h (mkEqMS orig t) fun h => do
          let pf ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[heq], h]
          mkLambdaFVars #[t, h] (mkApp2 kMV t (← mkExpectedTypeHint pf (mkEqMS shape t)))
      let ha0 := a0.proof
      if isMul then
        let (hy, _, hyl) := snd.get!
        let ha1 := a1.proof
        mkAppM ``AsmVerif.RiscV.Sym.Safe.uint256Mul #[f.hfetch, ← mkExpectedTypeHint ht0 (mkEqW (mkGetReg s 5) (mkConst ``Sp1.UINT256_MUL)), ha0, ha1, hx, hxl, hy, hyl, k']
      else if isAdd then
        let (hy, _, hyl) := snd.get!
        let ha1 := a1.proof
        mkAppM ``AsmVerif.RiscV.Sym.Safe.pallasAdd #[f.hfetch, ← mkExpectedTypeHint ht0 (mkEqW (mkGetReg s 5) (mkConst ``Sp1.PALLAS_ADD)), ha0, ha1, hx, hxl, hy, hyl, k']
      else
        mkAppM ``AsmVerif.RiscV.Sym.Safe.pallasDouble #[f.hfetch, ← mkExpectedTypeHint ht0 (mkEqW (mkGetReg s 5) (mkConst ``Sp1.PALLAS_DOUBLE)), ha0, hx, hxl, k']
    finish { shape, kind := .ww r0 i0 a0.val ws wsE, newPc := some pc4, newPcE := pcv } close
    return true
  logInfo m!"sym_exec: stopping at ECALL {id} at pc {st.pc}"
  return false

/-! ## Function specifications at calls -/

/-- The conclusion of a (possibly curried) implication. -/
partial def piConclusion (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => piConclusion b
  | _ => e

def isContinuation (ty : Expr) : Bool :=
  ty.isForall && (piConclusion ty).isAppOf ``AsmVerif.RiscV.Sym.Safe

def piArity (e : Expr) : Nat :=
  match e with
  | .forallE _ _ b _ => piArity b + 1
  | _ => 0

/-- `RegionOk lo hi a n` for a block inside a tracked region, else by `omega`. -/
partial def proveRegionOk (st : St) (ty : Expr) : TacticM Expr := do
  let_expr AsmVerif.RiscV.Sym.RegionOk lo0 hi0 a nE := ty | throwError "proveRegionOk"
  let some n ← getNatValue? (← whnfD nE) | do
    -- a size with a literal value in context (`J.length = 166`): prove it at the literal
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
      unless (← getNatValue? rhs).isSome do continue
      unless ← withReducible (isDefEq lhs nE) do continue
      let pf ← proveRegionOk st (mkApp4 (mkConst ``AsmVerif.RiscV.Sym.RegionOk) lo0 hi0 a rhs)
      let motive ← withLocalDeclD `n natTy fun x =>
        mkLambdaFVars #[x] (mkApp4 (mkConst ``AsmVerif.RiscV.Sym.RegionOk) lo0 hi0 a x)
      return ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, d.toExpr], pf]
    throwError "RegionOk: size not a literal {nE}"
  let l ← normLin a
  if let some (ri, i) := findBlock? st l n then
   let R := st.regions[ri]!
   if R.ok != noRegionOk then
    let hle ← natLe (i + n) R.n
    let ha ← proveAddrEq st a (← cellAddr R.base i 0)
    let pf ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.sub' #[← R.okE, mkNatLit i, mkNatLit n, hle, ha]
    if ← isDefEq (← inferType pf) ty then return pf
  let_expr AsmVerif.RiscV.Sym.RegionOk lo hi _ _ := ty | throwError "proveRegionOk"
  -- a hypothesis with the same, or a wider, code window over a block containing this one
  -- (`roBase < textLo`: a `roBase` fact gives the `textLo` one by `RegionOk.weaken`)
  let loV? ← getNatValue? (← whnfD lo)
  let hiV? ← getNatValue? (← whnfD hi)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dty ← instantiateMVars d.type
    let_expr AsmVerif.RiscV.Sym.RegionOk lo' hi' b' nE' := dty | continue
    let same ← pure ((← isDefEq lo lo') && (← isDefEq hi hi'))
    let wider ← if same then pure false else do
      match loV?, hiV?, ← getNatValue? (← whnfD lo'), ← getNatValue? (← whnfD hi') with
      | some lov, some hiv, some lov', some hiv' => pure (lov' ≤ lov && hiv ≤ hiv')
      | _, _, _, _ => pure false
    unless same || wider do continue
    let some n' ← getNatValue? (← whnfD nE') | continue
    let l' ← normLin b'
    unless l'.sameAtom l do continue
    let off := (l.c + two64 - l'.c) % two64
    unless off % 8 == 0 && off / 8 + n ≤ n' do continue
    let i := off / 8
    let hle ← natLe (i + n) n'
    let ha ← proveAddrEq st a (← cellAddr b' i 0)
    let mut pf ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.sub' #[d.toExpr, mkNatLit i, mkNatLit n, hle, ha]
    if wider then
      pf ← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.weaken #[pf, ← mkDecideProof (natLeE lo' lo), ← mkDecideProof (natLeE hi hi')]
    if ← isDefEq (← inferType pf) ty then return pf
  let toN ← mkAppM ``BitVec.toNat #[a]
  let ext ← mkAppM ``HAdd.hAdd #[toN, ← mkAppM ``HMul.hMul #[mkNatLit 8, nE]]
  let p1 ← mkEq (← mkAppM ``HMod.hMod #[toN, mkNatLit 8]) (mkNatLit 0)
  let p2 := natLeE ext (mkConst ``RiscvZkvm.Rv64.SP1_MAX_MEMORY)
  let p3 ← mkAppM ``Or #[natLeE ext lo, natLeE hi toN]
  let some h1 ← proveByOmega p1 | throwError "sym_exec: RegionOk alignment for {a}"
  let some h2 ← proveByOmega p2 | throwError "sym_exec: RegionOk bound for {a}"
  let some h3 ← proveByOmega p3 | throwError "sym_exec: RegionOk code window for {a}"
  mkAppM ``AsmVerif.RiscV.Sym.RegionOk.of_nat #[h1, h2, h3]

/-- Cells of a precondition's region pattern of the form `?m + c` against values `a + c'`:
    `?m := a + (c' - c)`, so that a specification stated at `q + 5` meets a reader advanced to
    `q + 37` (`isDefEq` alone does not do the arithmetic). -/
def unifyLinCells (pats vals : Array Expr) : MetaM Unit := do
  for (p, v) in pats.zip vals do
    let p ← instantiateMVars p
    unless p.isAppOfArity ``HAdd.hAdd 6 do continue
    let m := p.appFn!.appArg!
    unless m.isMVar do continue
    if ← m.mvarId!.isAssigned then continue
    let lp ← normLin p.appArg!
    unless lp.atom.isNone do continue
    let lv ← normLin v
    let some a := lv.atom | continue
    let d := (lv.c + two64 - lp.c) % two64
    let e ← if d == 0 then pure a else mkAdd a (mkWordLit d)
    discard <| isDefEq m e

/-- `ws = vs` cell by cell, a cell by `rfl` or as an address equation (`q + 37 = q + 32 + 5`):
    the region a precondition names, up to the linear normal form of its cells. -/
def listEqByLin (st : St) (ws vs : Array Expr) : MetaM (Option Expr) := do
  unless ws.size == vs.size do return none
  let mut pf ← mkEqRefl (mkListLit wordTy #[])
  let mut tw : Expr := mkListLit wordTy #[]
  let mut tv : Expr := mkListLit wordTy #[]
  for i in (List.range ws.size).reverse do
    let w := ws[i]!; let v ← instantiateMVars vs[i]!
    -- reducible first: a default-transparency check of `q + 1033 + 5` against `q + 1032 + 6`
    -- unfolds the `BitVec` arithmetic (minutes); the linear normal form settles it at once
    let h ← if ← withReducible (isDefEq w v) then mkEqRefl w else
      try proveAddrEq st w v catch _ =>
        if ← isDefEq w v then mkEqRefl w else return none
    pf ← mkCongr (← mkCongrArg (mkApp (mkConst ``List.cons [0]) wordTy) h) pf
    tw := mkApp3 (mkConst ``List.cons [0]) wordTy w tw
    tv := mkApp3 (mkConst ``List.cons [0]) wordTy v tv
  return some pf

/-- Discharge one precondition of a specification from the facts. -/
partial def discharge (ty : Expr) : SymM Expr := do
  let st ← get
  let s := st.s
  let ty ← instantiateMVars ty
  -- register equations may assign a data argument
  if let some (_, lhs, rhs) := ty.eq? then
    match_expr lhs with
    | MachineState.getReg s' r =>
      if s' == s then
        let i ← regIdx r
        let f ← valueOf i
        let rhs ← instantiateMVars rhs
        if rhs.isMVar then
          -- in the goal's context: the value may be an atom introduced on the way
          let _ ← withMainContext (isDefEq rhs f.val)
          return f.proof
        if rhs.hasExprMVar then
          -- a shape with data arguments to fill (`x13 = zeroExtend 64 (flag ?Q ?B)`): unify with
          -- the value, else with the atom's definition
          if ← withMainContext (isDefEq rhs f.val) then return f.proof
          let r? ← withMainContext do
            for d in ← getLCtx do
              if d.isImplementationDetail then continue
              unless d.userName.toString.endsWith "_def" do continue
              let dty ← instantiateMVars d.type
              if let some (_, e, a) := dty.eq? then
                if a == f.val then
                  if ← isDefEq rhs e then
                    return some (← mkAppM ``Eq.trans #[f.proof, ← mkAppM ``Eq.symm #[d.toExpr]])
            return none
          if let some pf := r? then return pf
          let defs ← withMainContext do
            let mut out : Array MessageData := #[]
            for d in ← getLCtx do
              if d.isImplementationDetail then continue
              unless d.userName.toString.endsWith "_def" do continue
              let dty ← instantiateMVars d.type
              if let some (_, e, a) := dty.eq? then
                if a == f.val then out := out.push m!"{d.userName} : {e} = {a}"
            pure out
          throwError "sym_exec: precondition {ty}: the register holds {f.val}, defined by {defs}"
        let st ← get
        return ← withMainContext do
          let pr := st.pureFacts
          match ← proveBySimp ty (#[f.proof] ++ st.regRules ++ pr) normLemmas with
          | some p => pure p
          | none => throwError "sym_exec: precondition {ty}"
    | MachineState.pc s' =>
      if s' == s then
        return ← withMainContext do
          match ← proveBySimp ty #[st.hpc] normLemmas with
          | some p => pure p
          | none => throwError "sym_exec: precondition {ty}"
    | MachineState.code s' =>
      -- `s.code = c`: the code of the start state, then a hypothesis about it
      if s' == s then
        return ← withMainContext do
          let rhs ← instantiateMVars rhs
          let c0 := mkApp (mkConst ``MachineState.code) st.s0
          if ← isDefEq c0 rhs then return st.hcode
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            if ← withReducible (isDefEq d.type (← mkEq c0 rhs)) then
              return ← mkAppM ``Eq.trans #[st.hcode, d.toExpr]
          throwError "sym_exec: precondition {ty}"
    | MachineState.privateInput s' =>
      if s' == s then
        let some (v, pf) := st.priv | throwError "sym_exec: no private-input fact"
        if (← instantiateMVars rhs).isMVar then
          let _ ← withMainContext (isDefEq rhs v)
          return pf
        if ← withMainContext (isDefEq rhs v) then return pf
    | _ => pure ()
  -- `∃ ws, ws.length = n ∧ Region b ws s`: the region the executor has at `b`
  if ty.isAppOfArity ``Exists 2 then
    let p := ty.appArg!
    let (ws, regTy, lenTy) ← withMainContext do
      let ws ← mkFreshExprMVar ty.appFn!.appArg!
      let body ← whnfR (p.beta #[ws])
      let some (lenTy, regTy) := body.and? | throwError "sym_exec: precondition {ty}"
      -- `ws.length = n`: `ws` is `n` unknowns, so that a block inside a region is found
      if let some (_, _, rhs) := lenTy.eq? then
        if let some n ← getNatValue? rhs then
          let elemTy := (← inferType ws).appArg!
          let cells ← (List.range n).toArray.mapM fun _ => mkFreshExprMVar elemTy
          let _ ← isDefEq ws (mkListLit elemTy cells)
      pure (ws, regTy, lenTy)
    let pReg ← discharge regTy
    return ← withMainContext do
      let lenTy ← instantiateMVars lenTy
      let pLen ← match ← proveBySimp lenTy #[] #[``List.length_cons, ``List.length_nil] with
        | some p => pure p
        | none =>
          let some (_, _, rhs) := lenTy.eq? | throwError "sym_exec: region length for {ty}"
          try rflOf lenTy rhs catch _ => throwError "sym_exec: region length for {ty}"
      mkAppOptM ``Exists.intro #[none, some p, some (← instantiateMVars ws),
        some (← mkAppM ``And.intro #[pLen, pReg])]
  withMainContext do
  -- a continuation-shaped premise (a panic arm, or a contract the callee itself assumes): the
  -- caller's hypothesis of the same shape, its code state ours (the binder `u.code = sₖ.code`
  -- is composed with `sₖ.code = s.code`)
  if isContinuation ty then
    let some pf ← forallTelescope ty fun xs body => do
        let n := xs.size
        let mut ci : Option Nat := none
        for i in [:n] do
          let t ← instantiateMVars (← inferType xs[i]!)
          if let some (_, l, r) := t.eq? then
            let c := ``RiscvZkvm.Rv64.MachineState.code
            if l.isAppOfArity c 1 && r.isAppOfArity c 1 then
              ci := some i
              break
        -- the code chains from the start state: `sₖ.code = s₀.code`, and through a
        -- hypothesis `s₀.code = c` (a run resumed by `sym_reframe` has `hcode0 : s₀.code = s.code`)
        let c0 := mkApp (mkConst ``MachineState.code) st.s0
        let mut chains : Array Expr := #[st.hcode]
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let some (_, l, _) := (← instantiateMVars d.type).eq? | continue
          unless l == c0 do continue
          chains := chains.push (← mkAppM ``Eq.trans #[st.hcode, d.toExpr])
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          unless isContinuation d.type && piArity d.type == n do continue
          for chain in chains do
            let r ← observing? do
              let mut args : Array Expr := #[]
              for i in [:n] do
                if ci == some i then args := args.push (← mkAppM ``Eq.trans #[xs[i]!, chain])
                else args := args.push xs[i]!
              let app ← mkAppM' d.toExpr args
              -- reducible: a hypothesis of the same arity but another statement (the caller's
              -- own continuation) must fail fast, not unfold the models in it
              unless ← withReducible (isDefEq (← inferType app) body) do failure
              mkLambdaFVars xs app
            if let some pf := r then return some pf
        return none
      | throwError "sym_exec: no hypothesis for the continuation-shaped precondition {ty}"
    return pf
  match_expr ty with
  | AsmVerif.RiscV.Sym.CodeAt b prog s' =>
    if s' == s then
      for c in st.codes do
        if (← bvLit b) == c.base then
          if ← isDefEq prog c.progExpr then return c.hyp
    throwError "sym_exec: no CodeAt fact for {b}"
  | AsmVerif.RiscV.Sym.CodeWithin _ _ s' =>
    if s' == s then
      if ← isDefEq ty (← inferType st.hcw) then return st.hcw
    throwError "sym_exec: CodeWithin mismatch {ty}"
  | AsmVerif.RiscV.Sym.Region a vs s' =>
    if s' == s then
      let a ← instantiateMVars a
      let l ← normLin a
      let vs ← instantiateMVars vs
      let m? : Option Nat ← (do let es ← listElems vs; pure (some es.size)) <|> pure none
      -- a block across adjacent regions: their join, for this use only
      let st ← match m? with
        | some m =>
          if (findBlock? st l m).isNone then
            match ← (try joinBlock? st l m catch _ => pure none) with
            | some R => pure { st with regions := st.regions.push R }
            | none => pure st
          else pure st
        | none => pure st
      -- a list variable with a length fact in context: a block of that many cells
      let varLen? : Option (Nat × Expr) ← match m? with
        | some _ => pure none
        | none => do
          let mut r := none
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            let dty ← instantiateMVars d.type
            match_expr dty with
            | Eq _ lhs rhs =>
              if lhs.isAppOfArity ``List.length 2 && lhs.appArg! == vs then
                if let some n ← getNatValue? rhs then r := some (n, d.toExpr); break
            | _ => pure ()
          pure r
      -- (a variable's region: a block of its length, else the region at exactly this base)
      let exactBase : Option (Nat × Nat × Nat) :=
        (List.range st.regions.size).findSome? fun (ri : Nat) =>
          let R : RegionInfo := st.regions[ri]!
          if R.baseLin.sameAtom l && R.baseLin.c == l.c then some (ri, 0, R.n) else none
      let blk := match m? with
        | some m => (findBlock? st l m).map fun (p : Nat × Nat) => (p.1, p.2, m)
        | none => match varLen? with
          | some (n, _) => ((findBlock? st l n).map fun (p : Nat × Nat) => (p.1, p.2, n)) <|> exactBase
          | none => exactBase
      let some (ri, i, m) := blk | do
        -- an opaque region of that size at this base: its cells as `vs[i]!`
        let some m := m? | throwError "sym_exec: no region for precondition {ty}"
        let some ri := (List.range st.regions.size).find? (fun ri =>
            let R : RegionInfo := st.regions[ri]!
            R.lenPf.isSome && R.baseLin.sameAtom l && R.baseLin.c == l.c && R.n == m)
          | throwError "sym_exec: no region for precondition {ty}"
        let R := st.regions[ri]!
        let (lit, pf, _) ← expandRegion R.base R.listExpr R.hyp R.n
          #[(R.listExpr, mkNatLit R.n, R.lenPf.get!)]
        unless ← isDefEq vs lit do throwError "sym_exec: region contents mismatch for {ty}"
        let ha ← proveAddrEq st a R.base
        let motive := mkLambda `b .default wordTy (mkApp3 (mkConst ``AsmVerif.RiscV.Sym.Region) (mkBVar 0) lit st.s)
        return ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, ha], pf]
      let R := st.regions[ri]!
      -- the whole region under its own (possibly opaque) list: the hypothesis itself
      if i == 0 && m == R.n then
        try unifyLinCells (← listElems vs) (← listElems R.listExpr) catch _ => pure ()
        if ← withReducible (isDefEq vs R.listExpr) then
          let ha ← proveAddrEq st a R.base
          let motive := mkLambda `b .default wordTy (mkApp3 (mkConst ``AsmVerif.RiscV.Sym.Region) (mkBVar 0) R.listExpr st.s)
          return ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, ha], R.hyp]
      let (pf, _, wsE) ← subRegion st R i m a
      try unifyLinCells (← listElems vs) (← listElems wsE) catch _ => pure ()
      if ← withReducible (isDefEq vs wsE) then return pf
      if let some heq ← (try listEqByLin st (← listElems wsE) (← listElems vs) catch _ => pure none) then
        return ← mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[pf, heq]
      if ← isDefEq vs wsE then return pf
      -- a list variable whose cells `vs[k]!` the block holds (a copy of an expanded input, a
      -- contract's buffer): fold them back under it through its length fact
      if let some (_, hlen) := varLen? then
        let fn ← withLocalDeclD `i natTy fun i => do
          mkLambdaFVars #[i] (← mkAppM ``GetElem?.getElem! #[vs, i])
        let mapE ← mkAppM ``List.map #[fn, ← mkAppM ``List.range #[mkNatLit m]]
        let heq ← mkAppM ``AsmVerif.RiscV.Sym.List.eq_map_range #[vs, hlen]
        let heq' ← mkAppM ``Eq.trans #[heq, ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy mapE wsE) wsE]
        return ← mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[pf, ← mkAppM ``Eq.symm #[heq']]
      throwError "sym_exec: region contents mismatch for {ty}"
    throwError "sym_exec: precondition {ty}"
  | AsmVerif.RiscV.Sym.RegionOk _ _ _ _ => proveRegionOk st ty
  | AsmVerif.RiscV.Sym.RoImage _ s' =>
    if s' == s then
      if let some h := st.hro then return h
    throwError "sym_exec: no read-only image fact for {ty}"
  | _ =>
    -- an assumption?
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if ← withReducible (isDefEq d.type ty) then return d.toExpr
    if let some (a, mE, b, nE) := ty.app4? ``AsmVerif.RiscV.Sym.Disjoint then
      if let (some m, some n) := (← getNatValue? (← whnfD mE), ← getNatValue? (← whnfD nE)) then
        if let some pf ← lookupDisj st.disj a m b n then return pf
        if let some pf ← lookupDisjSub st a m b n then return pf
    -- `StackOk` field by field: `omega` on the structure as a whole, over every `2^64`
    -- quotient of the context, fails first and costs seconds each time
    if ty.isAppOf ``AsmVerif.RiscV.Sym.StackOk then
      let args := ty.getAppArgs
      let L := args[0]!; let room := args[1]!; let sp := args[2]!
      let toN ← mkAppM ``BitVec.toNat #[sp]
      let some h1 ← proveByOmega (← mkEq (← mkAppM ``HMod.hMod #[toN, mkNatLit 16]) (mkNatLit 0)) | throwError "StackOk alignment"
      let some h2 ← proveByOmega (natLeE (← mkAppM ``HAdd.hAdd #[room, mkNatLit 0x10000]) toN) | throwError "StackOk room"
      let some h3 ← proveByOmega (natLeE toN (mkApp (mkConst ``AsmVerif.RiscV.Sym.Layout.stackTop) L)) | throwError "StackOk top"
      return mkApp6 (mkConst ``AsmVerif.RiscV.Sym.StackOk.mk) L room sp h1 h2 h3
    let pr := st.pureFacts
    if let some p ← proveBySimp ty (st.regRules ++ pr) (normLemmas ++ #[``List.length_cons, ``List.length_nil]) then
      return p
    if let some p ← proveByOmega ty then return p
    throwError "sym_exec: cannot discharge precondition{indentExpr ty}\nthe hypotheses sharing its variables or head:{← relatedHyps ty}"

/-- A list that is not a literal as the literal of its cells: a `::` prefix over a variable
    tail whose length `lens` knows (`tag :: L` with `L.length = 8`), with the equation. -/
partial def expandListExpr (vs : Expr) (lens : Array (Expr × Expr × Expr)) :
    MetaM (Option (Expr × Expr)) := do
  match_expr vs with
  | List.cons _ a t =>
    let some (tl, h) ← expandListExpr t lens | return none
    let f ← withLocalDeclD `l listWordTy fun l => do mkLambdaFVars #[l] (← mkAppM ``List.cons #[a, l])
    return some (← mkAppM ``List.cons #[a, tl], ← mkAppM ``congrArg #[f, h])
  | _ =>
    let some (_, nE, hlen) := lens.find? (fun (l, _, _) => l == vs) | return none
    let some n ← getNatValue? (← whnfD nE) | return none
    let heq ← mkAppM ``AsmVerif.RiscV.Sym.List.eq_map_range #[vs, hlen]
    let mapE := (← inferType heq).appArg!
    let cells ← (List.range n).toArray.mapM fun i => mkAppM ``GetElem?.getElem! #[vs, mkNatLit i]
    let lit := mkListLit wordTy cells
    return some (lit, ← mkAppM ``Eq.trans #[heq, ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy mapE lit) lit])

/-- Read a specification's postcondition hypotheses back into an executor state. -/
def readPost (old : St) (t : Expr) (hyps : Array Expr) : SymM Unit := do
  let mut hpc? : Option (Expr × Expr × Option Nat) := none
  let mut regs : Array (Option RegFact) := Array.replicate 32 none
  let mut hcw? : Option Expr := none
  let mut priv : Option (Expr × Expr) := none
  let mut hU? : Option (Expr × Expr) := none
  let mut postRegions : Array (Expr × Expr × Expr) := #[]
  let mut lens : Array (Expr × Expr × Expr) := #[]
  let mut disj := old.disj
  let mut consumed : Array FVarId := #[]
  let mut purePost : Array Expr := #[]
  regs := regs.set! 0 (some ⟨mkWordLit 0, Lin.lit 0, mkApp (mkConst ``AsmVerif.RiscV.Sym.getReg_x0) t⟩)
  for h in hyps do
    let ty ← withMainContext do instantiateMVars (← inferType h)
    match_expr ty with
    | Eq _ lhs rhs =>
      match_expr lhs with
      | MachineState.pc t' =>
        if t' == t then
          let (v, pf) ← withMainContext do
            let pr := old.pureFacts
            let (v, pf) ← rewriteTo rhs (old.regRules ++ pr) normLemmas
            pure (v, ← mkAppM ``Eq.trans #[h, pf])
          let lit ← withMainContext (litValue? v)
          hpc? := some (v, pf, lit)
      | MachineState.getReg t' r =>
        if t' == t then
          let i ← withMainContext (regIdx r)
          let (v, pf, l) ← withMainContext do
            let pr := old.pureFacts
            let (v, pf) ← rewriteTo rhs (old.regRules ++ pr) normLemmas
            pure (v, ← mkAppM ``Eq.trans #[h, pf], ← normLin v)
          regs := regs.set! i (some ⟨v, l, pf⟩)
      | MachineState.code t' =>
        if t' == t then
          -- `t.code = s.code` (the caller's state), or already `t.code = s₀.code`
          let rhs ← instantiateMVars rhs
          if rhs == mkApp (mkConst ``MachineState.code) old.s0 && old.s != old.s0 then
            hcw? := some h
          else
            hcw? := some (← withMainContext do mkAppM ``Eq.trans #[h, old.hcode])
      | MachineState.privateInput t' =>
        if t' == t then
          let rhs ← instantiateMVars rhs
          match old.priv with
          | some (v, pf) =>
            -- `t.privateInput = s.privateInput` chains onto the caller's fact; any other value (a
            -- `HINT_READ` consuming the stream) replaces it
            if rhs == mkApp (mkConst ``MachineState.privateInput) old.s then
              let pf' ← withMainContext do mkAppM ``Eq.trans #[h, pf]
              priv := some (v, pf')
            else priv := some (rhs, h)
          | none => priv := some (rhs, h)
      | List.length _ l => lens := lens.push (l, rhs, h)
      | _ => purePost := purePost.push h
    | AsmVerif.RiscV.Sym.CalleeSaved _ _ =>
      for i in [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] do
        if let some f := old.regs[i]! then
          let pf ← withMainContext do
            let hmem ← mkDecideProof (← mkAppM ``Membership.mem #[mkConst ``AsmVerif.RiscV.Sym.calleeSavedRegs, mkReg i])
            mkAppM ``AsmVerif.RiscV.Sym.CalleeSaved.get #[h, mkReg i, hmem, f.proof]
          if regs[i]!.isNone then regs := regs.set! i (some ⟨f.val, f.lin, pf⟩)
      consumed := consumed.push h.fvarId!
    | AsmVerif.RiscV.Sym.Unchanged W' _ _ => hU? := some (W', h); consumed := consumed.push h.fvarId!
    | AsmVerif.RiscV.Sym.Region b vs t' => if t' == t then postRegions := postRegions.push (b, vs, h)
    | AsmVerif.RiscV.Sym.Disjoint b₁ n₁ b₂ n₂ => disj := disj.push (b₁, n₁, b₂, n₂, h)
    | _ => purePost := purePost.push h
  -- the context's length facts too: a post region over a list the caller's spec names
  -- (`Region ptr Bv t` with the caller's `Bv.length = 137`)
  lens := lens ++ (← withMainContext do
    let mut out : Array (Expr × Expr × Expr) := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOfArity ``List.length 2 do continue
      out := out.push (lhs.appArg!, rhs, d.toExpr)
    pure out)
  -- a computed block `natToLeLimbs n e` is named: `e` becomes an atom, so the
  -- next call's operands do not nest this one's expression
  let mut postClear : Array FVarId := #[]
  let mut postRegions' : Array (Expr × Expr × Expr) := #[]
  for qi in [0:postRegions.size] do
    let (qb, qvs, qh) := postRegions[qi]!
    postClear := postClear.push qh.fvarId!
    -- a post region re-stating an opaque tracked region under its own list (a contract keeping
    -- a caller's block it may not write: the hasher's tables): raw here, a no-op patch below,
    -- never its cells (a 1024-word table expanded takes gigabytes)
    if old.regions.any (fun R => R.lenPf.isSome && R.base == qb && R.listExpr == qvs) then
      postRegions' := postRegions'.push (qb, qvs, qh)
      continue
    if qvs.isAppOfArity ``RiscvZkvm.Rv64.Accel.natToLeLimbs 2 && exprSize qvs.appArg! ≥ 12 then
      let e := qvs.appArg!
      let (v, hv) ← atomize e natTy (Name.mkSimple s!"acc{old.k}_{qi}")
      let f := qvs.appFn!
      let h' ← withMainContext do
        mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[qh, ← mkAppM ``congrArg #[f, hv]]
      postRegions' := postRegions'.push (qb, mkApp f v, h')
      -- the other post facts about the value, stated about its atom
      purePost ← withMainContext do
        purePost.mapM fun h => do
          let ty ← instantiateMVars (← inferType h)
          let abst ← kabstract ty e
          if !abst.hasLooseBVars then return h
          let motive := mkLambda `x .default natTy abst
          mkAppM ``Eq.mp #[← mkAppM ``congrArg #[motive, hv], h]
    else if !qvs.isFVar && !qvs.isAppOf ``List.cons && !qvs.isAppOf ``List.nil then
      -- any other computed list (`curveAddL …`): a list atom, its cells `v[i]!`
      let lenE ← withMainContext (mkAppM ``List.length #[qvs])
      -- the length facts among the post's hypotheses and the context first (all of them: an
      -- append `B ++ B'` takes its parts' facts, `B'.length = 4 * len.toNat` with `len` a
      -- literal reduced by the simprocs); never `decide`, which would evaluate a model
      -- function (`mulLoop … 255 …`)
      let lenRules := lens.map fun (_, _, h) => h
      let r ← withMainContext (simpWith lenE lenRules #[``AsmVerif.RiscV.Sym.length_curveAddL, ``AsmVerif.RiscV.Sym.length_curveDblL,
        ``List.length_cons, ``List.length_nil, ``List.length_append, ``List.length_map,
        ``List.length_range] (dec := false))
      -- else by `simp` with the default simp set: the models' `@[simp]` length lemmas
      let len? : Option (Nat × Expr) ← withMainContext do
        match ← getNatValue? r.expr with
        | some n => pure (some (n, ← r.getProof))
        | none =>
          -- a model application only (`domainPtW x y`): an append or a `natToLeLimbs` block
          -- stays raw, its cells normalise at the loads (`(A ++ [c])[4]!` to `c`)
          if !modelHead qvs then pure none else match ← derivedLen qvs lenRules with
          | some (nE, pf) => match ← getNatValue? nE with
            | some n => pure (some (n, pf))
            | none => pure none
          | none => pure none
      match len? with
      | none => postRegions' := postRegions'.push (qb, qvs, qh)
      | some (n, hlen0) =>
        let (v, hv) ← atomize qvs listWordTy (Name.mkSimple s!"acc{old.k}_{qi}")
        -- the other post facts about the list (a tag byte of a model's first cell), stated
        -- about its atom
        purePost ← withMainContext do
          purePost.mapM fun h => do
            let ty ← instantiateMVars (← inferType h)
            let abst ← kabstract ty qvs
            if !abst.hasLooseBVars then return h
            let motive := mkLambda `x .default listWordTy abst
            mkAppM ``Eq.mp #[← mkAppM ``congrArg #[motive, hv], h]
        let h' ← withMainContext do
          let hlenV ← mkAppM ``Eq.trans #[← mkAppM ``congrArg #[mkApp (mkConst ``List.length [0]) wordTy,
            ← mkAppM ``Eq.symm #[hv]], hlen0]
          let hexp ← mkAppM ``AsmVerif.RiscV.Sym.List.eq_map_range #[v, hlenV]   -- v = map
          let mapE := (← inferType hexp).appArg!
          let cells ← (List.range n).toArray.mapM fun i => mkAppM ``GetElem?.getElem! #[v, mkNatLit i]
          let lit := mkListLit wordTy cells
          let hexp' ← mkAppM ``Eq.trans #[hexp, ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy mapE lit) lit]
          mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[qh, ← mkAppM ``Eq.trans #[hv, hexp']]
        let cells ← withMainContext do
          (List.range n).toArray.mapM fun i => mkAppM ``GetElem?.getElem! #[v, mkNatLit i]
        postRegions' := postRegions'.push (qb, mkListLit wordTy cells, h')
    else if qvs.isAppOf ``List.cons &&
        !(← withMainContext (try (do let _ ← listElems qvs; pure true) catch _ => pure false)) then
      -- `tag :: L` with `L.length = n` among the post's facts
      match ← withMainContext (expandListExpr qvs lens) with
      | some (lit, heq) =>
        let h' ← withMainContext do mkAppM ``AsmVerif.RiscV.Sym.Region.of_eq #[qh, heq]
        postRegions' := postRegions'.push (qb, lit, h')
      | none => postRegions' := postRegions'.push (qb, qvs, qh)
    else postRegions' := postRegions'.push (qb, qvs, qh)
  postRegions := postRegions'
  let some (pcv, hpcPf, pcLit) := hpc? | throwError "sym_exec: specification says nothing about the return pc"
  let some hcode := hcw? | throwError "sym_exec: specification does not preserve the code"
  let some (W', hU) := hU? | throwError "sym_exec: specification has no `Unchanged` frame"
  -- the frame: the callee's write set is covered by ours
  let wEntries' ← withMainContext do listElems W'
  let hcover ← withMainContext do
    let prodTy ← mkAppM ``Prod #[wordTy, natTy]
    let mut pf ← mkAppOptM ``AsmVerif.RiscV.Sym.cover_nil #[some old.W]
    for j in (List.range wEntries'.size).reverse do
      let e ← whnfD wEntries'[j]!
      let b := e.getAppArgs[2]!; let n := e.getAppArgs[3]!
      let mut found : Option Expr := none
      let bl ← normLin b
      for wi in [0:old.wEntries.size] do
        if found.isSome then break
        let we := old.wEntries[wi]!
        -- a cover has the same base atom (`omega` on any other pair fails, at seconds each), or
        -- is an entry at a literal address (the heap range, the input area)
        unless we.baseLin.sameAtom bl || we.baseLin.atom.isNone do continue
        let prop := mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Covers) we.base (mkNatLit we.n) b n
        if let some hc ← proveByOmega prop then
          let entries ← listElems old.W
          let mut memPf ← mkAppOptM ``List.mem_cons_self #[some prodTy, some entries[wi]!, some (mkListLit prodTy (entries.extract (wi+1) entries.size))]
          for jj in (List.range wi).reverse do
            memPf ← mkAppM ``List.mem_cons_of_mem #[entries[jj]!, memPf]
          let hc ← mkExpectedTypeHint hc (mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Covers) (← mkAppM ``Prod.fst #[entries[wi]!]) (← mkAppM ``Prod.snd #[entries[wi]!]) (← mkAppM ``Prod.fst #[e]) (← mkAppM ``Prod.snd #[e]))
          found := some (← mkAppM ``AsmVerif.RiscV.Sym.cover_cons #[memPf, hc, pf])
      match found with
      | some p => pf := p
      | none => throwError "sym_exec: callee writes {b} ({n}), which our frame does not cover"
    pure pf
  let hunch ← withMainContext do mkAppM ``AsmVerif.RiscV.Sym.Unchanged.trans_cover #[old.hunch, hU, hcover]
  -- regions
  let mut usedPost : Array Bool := Array.replicate postRegions.size false
  let mut regions : Array RegionInfo := #[]
  -- a region the callee's write set may meet: survives whole, in part, or as unknown contents
  let survive : RegionInfo → SymM (Option RegionInfo) := fun R => do
      -- disjoint from the whole write set: survives
      let failRef ← IO.mkRef (none : Option (Expr × Nat × Expr × Nat))
      let knownFail := (← get).disjFail
      let r? ← withMainContext do
        let mut pf ← mkAppOptM ``AsmVerif.RiscV.Sym.disj_nil #[some R.base, some (mkNatLit R.n)]
        for j in (List.range wEntries'.size).reverse do
          let e ← whnfD wEntries'[j]!
          let b := e.getAppArgs[2]!; let nE := e.getAppArgs[3]!
          let projProp := mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Disjoint) R.base (mkNatLit R.n) (← mkAppM ``Prod.fst #[e]) (← mkAppM ``Prod.snd #[e])
          -- a caller's fact first (`lookupDisj`, either order), then `omega`
          let known? ← do
            match ← getNatValue? (← whnfD nE) with
            | some n => do
              match ← lookupDisj old.disj R.base R.n b n with
              | some h => pure (some h)
              | none => lookupDisjSub old R.base R.n b n
            | none => pure none
          let hd ← match known? with
            | some h => pure h
            | none =>
              -- overlapping blocks of one frame: not disjoint (an `omega` failure costs seconds)
              let n? ← getNatValue? (← whnfD nE)
              if let some n := n? then
                if linOverlap R.baseLin R.n (← normLin b) n then return none
                if knownFail.contains (R.base, R.n, b, n) then return none
              let prop := mkApp4 (mkConst ``AsmVerif.RiscV.Sym.Disjoint) R.base (mkNatLit R.n) b nE
              let some hd ← proveByOmega prop
                | do
                  if let some n := n? then failRef.set (some (R.base, R.n, b, n))
                  return none
              pure hd
          let hd ← mkExpectedTypeHint hd projProp
          pf ← mkAppM ``AsmVerif.RiscV.Sym.disj_cons #[hd, pf]
        let hn ← match R.lenPf with
          | some h => pure h
          | none => rflOf (← mkEq (← mkAppM ``List.length #[R.listExpr]) (mkNatLit R.n)) (mkNatLit R.n)
        some <$> mkAppM ``AsmVerif.RiscV.Sym.Region.of_unchanged' #[R.hyp, hU, hn, pf]
      if let some f ← failRef.get then modify fun st => { st with disjFail := st.disjFail.push f }
      match r? with
      | some pf => return some { R with hyp := pf }
      | none =>
        -- a write set meeting only part of it: that part becomes unknown, the rest survives
        -- (a callee's frame cut out of a caller region that also holds live cells)
        let part? : Option RegionInfo ← withMainContext do
          let mut lo := R.n
          let mut hi := 0
          for j in [0:wEntries'.size] do
            let e ← whnfD wEntries'[j]!
            let some n ← getNatValue? (← whnfD e.getAppArgs[3]!) | continue
            let bl ← normLin e.getAppArgs[2]!
            unless bl.sameAtom R.baseLin do continue
            let d := (bl.c + two64 - R.baseLin.c) % two64
            let dI : Int := if d ≥ two64 / 2 then (d : Int) - (two64 : Int) else (d : Int)
            let s1 := dI + 8 * (n : Int)
            if s1 ≤ 0 || dI ≥ 8 * (R.n : Int) then continue
            let loC := if dI ≤ 0 then 0 else (dI / 8).toNat
            let hiC := min R.n ((s1 + 7) / 8).toNat
            lo := min lo loC
            hi := max hi hiC
          if hi ≤ lo || (lo == 0 && hi == R.n) then return none
          let i := lo
          let m := hi - lo
          try
            let qb ← if i == 0 then pure R.base else mkAdd R.base (mkWordLit (8 * i))
            let qvs ← mkAppM ``AsmVerif.RiscV.Sym.contents #[t, qb, mkNatLit m]
            let qh ← mkAppM ``AsmVerif.RiscV.Sym.Region.junk #[qb, mkNatLit m, t]
            let (qvs', qh', _) ← expandRegion qb qvs qh m lens
            let hle ← mkDecideProof (natLeE (← mkAppM ``HAdd.hAdd #[mkNatLit i, ← mkAppM ``List.length #[qvs']]) (← mkAppM ``List.length #[R.listExpr]))
            let ha ← proveAddrEq old qb (← cellAddr R.base i 0)
            let mut hout ← mkAppOptM ``AsmVerif.RiscV.Sym.out_nil #[some R.base, some (mkNatLit R.n), some (mkNatLit i), some (mkNatLit m)]
            for j in (List.range wEntries'.size).reverse do
              let e ← whnfD wEntries'[j]!
              let prop ← withLocalDeclD `j natTy fun jv => do
                let body ← mkArrow (natLtE jv (mkNatLit R.n))
                  (← mkArrow (← mkAppM ``Or #[natLtE jv (mkNatLit i), natLeE (← mkAppM ``HAdd.hAdd #[mkNatLit i, mkNatLit m]) jv])
                    (← mkAppM ``Not #[← mkAppM ``AsmVerif.RiscV.Sym.InRegion #[← mkAdd R.base (← mkAppM ``BitVec.ofNat #[mkNatLit 64, ← mkAppM ``HMul.hMul #[mkNatLit 8, jv]]), ← mkAppM ``Prod.fst #[e], ← mkAppM ``Prod.snd #[e]]]))
                mkForallFVars #[jv] body
              let some hd ← proveByOmegaIntro prop | throwError "partial junk: outside"
              hout ← mkAppM ``AsmVerif.RiscV.Sym.out_cons #[hd, hout]
            let cells' := (R.cells.extract 0 i) ++ (← listElems qvs') ++ (R.cells.extract (i + m) R.n)
            let list' := mkListLit wordTy cells'
            let lhs ← mkAppM ``HAppend.hAppend #[← mkAppM ``HAppend.hAppend #[← mkAppM ``List.take #[mkNatLit i, R.listExpr], qvs'],
              ← mkAppM ``List.drop #[← mkAppM ``HAdd.hAdd #[mkNatLit i, ← mkAppM ``List.length #[qvs']], R.listExpr]]
            let hvs ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy lhs list') list'
            let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.patch #[R.hyp, hU, hle, ha, qh', hout, hvs]
            return some { R with cells := cells', listExpr := list', hyp := pf }
          catch _ => return none
        match part? with
        | some R' => return some R'
        | none =>
          -- the callee may write all of it. Outside our own write set (a heap block the callee
          -- may free or reuse: the old buffer of a `realloc`) it says nothing worth keeping and
          -- may alias what the callee returns, so it is forgotten
          if R.w.isNone && (← withMainContext (coverEntry old R)).isSome then return none
          -- else it is still a region, of unknown contents
          let R' ← withMainContext do
            let vs ← mkAppM ``AsmVerif.RiscV.Sym.contents #[t, R.base, mkNatLit R.n]
            let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.junk #[R.base, mkNatLit R.n, t]
            let (vs', pf', cells) ← expandRegion R.base vs pf R.n lens
            pure { R with cells := cells, listExpr := vs', hyp := pf', hypM := pf', lenPf := none }
          return some R'
  for R in old.regions do
    if R.outW.isSome then
      regions := regions.push R
      continue
    -- a post region inside R: patch
    let mut patched : Option RegionInfo := none
    let mut split? : Option (Nat × Nat) := none
    for qi in [0:postRegions.size] do
      if patched.isSome then break
      let (qb, qvs, qh) := postRegions[qi]!
      -- the region re-stated under its own list: kept as it is, at `t`
      if R.lenPf.isSome && R.base == qb && R.listExpr == qvs then
        patched := some { R with hyp := qh, hypM := qh }
        usedPost := usedPost.set! qi true
        break
      let ql ← withMainContext (normLin qb)
      let qcells : Array Expr ← withMainContext (do
        try
          let nE ← readPost.lenOf qvs lens
          let some n ← getNatValue? (← whnfD nE) | return #[]
          let (_, _, cells) ← expandRegion qb qvs qh n lens
          return cells
        catch _ => return #[])
      if qcells.isEmpty then continue
      if R.baseLin.sameAtom ql then
        let off := (ql.c + two64 - R.baseLin.c) % two64
        if off % 8 == 0 && off / 8 + qcells.size ≤ R.n then
          let i := off / 8
          let m := qcells.size
          let r? ← withMainContext do
           try
            let (qvs', qh', _) ← expandRegion qb qvs qh m lens
            let hle ← mkDecideProof (natLeE (← mkAppM ``HAdd.hAdd #[mkNatLit i, ← mkAppM ``List.length #[qvs']]) (← mkAppM ``List.length #[R.listExpr]))
            let ha ← proveAddrEq old qb (← cellAddr R.base i 0)
            -- every cell outside the patch is outside W'
            let mut hout ← mkAppOptM ``AsmVerif.RiscV.Sym.out_nil #[some R.base, some (mkNatLit R.n), some (mkNatLit i), some (mkNatLit m)]
            for j in (List.range wEntries'.size).reverse do
              let e ← whnfD wEntries'[j]!
              let prop ← withLocalDeclD `j natTy fun jv => do
                let body ← mkArrow (natLtE jv (mkNatLit R.n))
                  (← mkArrow (← mkAppM ``Or #[natLtE jv (mkNatLit i), natLeE (← mkAppM ``HAdd.hAdd #[mkNatLit i, mkNatLit m]) jv])
                    (← mkAppM ``Not #[← mkAppM ``AsmVerif.RiscV.Sym.InRegion #[← mkAdd R.base (← mkAppM ``BitVec.ofNat #[mkNatLit 64, ← mkAppM ``HMul.hMul #[mkNatLit 8, jv]]), ← mkAppM ``Prod.fst #[e], ← mkAppM ``Prod.snd #[e]]]))
                mkForallFVars #[jv] body
              let some hd ← proveByOmegaIntro prop
                | throwError "sym_exec: cannot show region {R.base} outside the callee's write {e}"
              hout ← mkAppM ``AsmVerif.RiscV.Sym.out_cons #[hd, hout]
            let cells' := (R.cells.extract 0 i) ++ (← listElems qvs') ++ (R.cells.extract (i + m) R.n)
            let list' := mkListLit wordTy cells'
            let lhs ← mkAppM ``HAppend.hAppend #[← mkAppM ``HAppend.hAppend #[← mkAppM ``List.take #[mkNatLit i, R.listExpr], qvs'],
              ← mkAppM ``List.drop #[← mkAppM ``HAdd.hAdd #[mkNatLit i, ← mkAppM ``List.length #[qvs']], R.listExpr]]
            let hvs ← rflOf (mkApp3 (mkConst ``Eq [1]) listWordTy lhs list') list'
            let pf ← mkAppM ``AsmVerif.RiscV.Sym.Region.patch #[R.hyp, hU, hle, ha, qh', hout, hvs]
            pure (some { R with cells := cells', listExpr := list', hyp := pf })
           catch _ => pure none
          match r? with
          | some r =>
            patched := some r
            usedPost := usedPost.set! qi true
          | none =>
            -- other cells of `R` meet the write set: cut `R` around the post region
            if split?.isNone then split? := some (i, m)
    match patched with
    | some R' => regions := regions.push R'
    | none =>
      match split? with
      | some (i, m) =>
        for (j, len) in [(0, i), (i + m, R.n - (i + m))] do
          if len == 0 then continue
          let piece ← withMainContext do
            let a ← if j == 0 then pure R.base else mkAdd R.base (mkWordLit (8 * j))
            let (pf, ws, wsE) ← subRegion old R j len a
            let lin ← normLin a
            let ok ← if R.ok == noRegionOk then pure noRegionOk else do
              let hle ← natLe (j + len) R.n
              let ha ← proveAddrEq old a (← cellAddr R.base j 0)
              mkAppM ``AsmVerif.RiscV.Sym.RegionOk.sub' #[R.ok, mkNatLit j, mkNatLit len, hle, ha]
            pure ({ base := a, baseLin := lin, n := len, cells := ws, listExpr := wsE, hyp := pf, hypM := pf,
                    ok := ok, w := wSlot old.wEntries lin len } : RegionInfo)
          if let some r ← survive piece then regions := regions.push r
      | none => if let some r ← survive R then regions := regions.push r
  -- a post region that is not a patch is authoritative for its cells: the survivors under it
  -- are dropped, or cut to their part outside it (two regions over one cell would let a load
  -- read the junked one and lose the callee's result)
  for qi in [0:postRegions.size] do
    if usedPost[qi]! then continue
    let (qb, qvs, _) := postRegions[qi]!
    let ql ← withMainContext (normLin qb)
    if ql.atom.isNone then continue
    let n? ← withMainContext do
      try
        let e ← readPost.lenOf qvs lens
        getNatValue? (← whnfD e)
      catch _ => pure none
    let some n := n? | continue
    let qlo := ql.c
    let qhi := ql.c + 8 * n
    let mut kept : Array RegionInfo := #[]
    for R in regions do
      if R.lenPf.isSome || !R.baseLin.sameAtom ql || R.cells.size != R.n then
        kept := kept.push R; continue
      let rlo := R.baseLin.c
      let rhi := R.baseLin.c + 8 * R.n
      if rhi ≤ qlo || qhi ≤ rlo then kept := kept.push R; continue
      let pieces : List (Nat × Nat) :=
        [(0, if qlo > rlo then (qlo - rlo) / 8 else 0),
         (if qhi < rhi then (qhi - rlo) / 8 else R.n, if qhi < rhi then (rhi - qhi) / 8 else 0)]
      for (j, len) in pieces do
        if len == 0 then continue
        let piece ← withMainContext do
          let a ← if j == 0 then pure R.base else mkAdd R.base (mkWordLit (8 * j))
          let (pf, ws, wsE) ← subRegion old R j len a
          let lin ← normLin a
          let ok ← if R.ok == noRegionOk then pure noRegionOk else do
            let hle ← natLe (j + len) R.n
            let ha ← proveAddrEq old a (← cellAddr R.base j 0)
            mkAppM ``AsmVerif.RiscV.Sym.RegionOk.sub' #[R.ok, mkNatLit j, mkNatLit len, hle, ha]
          pure ({ base := a, baseLin := lin, n := len, cells := ws, listExpr := wsE, hyp := pf, hypM := pf,
                  ok := ok, w := wSlot old.wEntries lin len } : RegionInfo)
        kept := kept.push piece
    regions := kept
  -- post regions not used as patches become regions of their own
  for qi in [0:postRegions.size] do
    if usedPost[qi]! then continue
    let (qb, qvs, qh) := postRegions[qi]!
    let r ← withMainContext do
      let ql ← normLin qb
      let ok ← proveRegionOk { old with regions := regions } (← mkAppM ``AsmVerif.RiscV.Sym.RegionOk #[← mkNatLitOf old.hcw 0, ← mkNatLitOf old.hcw 1, qb, ← lenOf qvs lens])
      let some n ← getNatValue? (← whnfD (← lenOf qvs lens)) | throwError "post region size"
      -- a large block over a list variable (a contract's buffer) stays opaque, as in `initState`:
      -- a later specification names that list
      let lit? ← try (do let _ ← listElems qvs; pure true) catch _ => pure false
      if !lit? && n > opaqueMin && (wSlot old.wEntries ql n).isNone then
        let hlen? ← match lens.find? (fun (l, _, _) => l == qvs) with
          | some (_, _, h) => pure (some h)
          | none => (·.map (·.2)) <$> derivedLen qvs
        if let some hlen := hlen? then
          return (⟨qb, ql, n, #[], qvs, qh, qh, ok, none, none, none, some hlen⟩ : RegionInfo)
      let (vs, pf, cells) ← expandRegion qb qvs qh n lens
      pure (⟨qb, ql, n, cells, vs, pf, pf, ok, wSlot old.wEntries ql n, none, none, none⟩ : RegionInfo)
    regions := regions.push r
  -- the register file of `t`
  let regs0 := regs
  let (regList, hregsPf, regsT) ← withMainContext do
    let mut regList := mkListLit wordTy ((List.range 32).toArray.map fun i => if i == 0 then mkWordLit 0 else mkGetReg t i)
    let mut hregsPf ← mkExpectedTypeHint (mkApp (mkConst ``AsmVerif.RiscV.Sym.Regs.self) t) (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) t regList)
    let mut regs := regs0
    for i in [1:32] do
      match regs[i]! with
      | some f =>
        let hlen ← rflOf (← mkEq (← mkAppM ``List.length #[regList]) (mkNatLit 32)) (mkNatLit 32)
        let pf ← mkAppM ``AsmVerif.RiscV.Sym.Regs.update #[hregsPf, hlen, mkNatLit i, ← natLt i 32, f.proof]
        regList ← regListSet regList i f.val
        hregsPf ← mkExpectedTypeHint pf (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) t regList)
      | none =>
        let v := mkGetReg t i
        regs := regs.set! i (some ⟨v, ⟨some v, 0⟩, default⟩)
    pure (regList, hregsPf, regs)
  -- facts
  let hpcF ← addFact `hpc (← withMainContext do inferType hpcPf) hpcPf
  let hregsF ← addFact `hregs (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.Regs) t regList) hregsPf
  let hcodeF ← addFact `hcode (← withMainContext do inferType hcode) hcode
  let mut regions' : Array RegionInfo := #[]
  for ri in [0:regions.size] do
    let R := regions[ri]!
    if R.outW.isSome then
      regions' := regions'.push R
      continue
    let fv ← addFact (Name.mkSimple s!"hR{ri}") (← withMainContext do inferType R.hyp) R.hyp
    regions' := regions'.push { R with hyp := fv, hypM := fv }
  let hunchF ← addFact `hunch (← withMainContext do inferType hunch) hunch
  -- post facts restated about an atom are terms over this step's hypotheses:
  -- make them hypotheses of their own, so that clearing those leaves them
  let mut purePostF : Array Expr := #[]
  for h in purePost do
    if h.isFVar then purePostF := purePostF.push h
    else purePostF := purePostF.push (← addFact (Name.mkSimple s!"hpost{old.k}") (← withMainContext do inferType h) h)
  purePost := purePostF
  -- the read-only image, if the callee's write set avoids it: each entry off the segment by
  -- `omega`, over the `RegionOk` bounds of the caller's blocks when the frame facts alone do
  -- not place it (an output block the caller only knows to lie off the image)
  let hroT ← match old.hro with
    | none => pure none
    | some hro =>
      let li ← old.layoutE
      let mut pf := mkApp (mkConst ``AsmVerif.RiscV.Sym.roW_nil) li.L
      let mut ok := true
      for j in (List.range wEntries'.size).reverse do
        let e ← withMainContext do whnfD wEntries'[j]!
        let (prop, ty) ← withMainContext do
          let b := e.getAppArgs[2]!; let n := e.getAppArgs[3]!
          let toN ← mkAppM ``BitVec.toNat #[b]
          let prop ← roOutProp li (← mkAppM ``HAdd.hAdd #[toN, ← mkAppM ``HMul.hMul #[mkNatLit 8, n]]) toN
          let ty ← roOutProp li (← mkAppM ``HAdd.hAdd #[← mkAppM ``BitVec.toNat #[← mkAppM ``Prod.fst #[e]], ← mkAppM ``HMul.hMul #[mkNatLit 8, ← mkAppM ``Prod.snd #[e]]])
            (← mkAppM ``BitVec.toNat #[← mkAppM ``Prod.fst #[e]])
          pure (prop, ty)
        let mut hd? ← withMainContext (proveByOmega prop)
        if hd?.isNone then
          hd? ← withMainContext (roOutOfEntry old e.getAppArgs[2]! e.getAppArgs[3]!)
        match hd? with
        | none =>
          trace[AsmVerif.sym] "the read-only image fact is not carried past the call: the write set's entry {e} is not shown off the segment"
          ok := false
          break
        | some hd =>
          let hd ← withMainContext do mkExpectedTypeHint hd ty
          pf ← withMainContext do mkAppM ``AsmVerif.RiscV.Sym.roW_cons #[hd, pf]
      if ok then
        let p ← withMainContext do mkAppM ``AsmVerif.RiscV.Sym.RoImage.of_unchanged #[hro, hU, pf]
        pure (some (← addFact `hro (mkApp2 (mkConst ``AsmVerif.RiscV.Sym.RoImage) li.L t) p))
      else pure none
  let priv' ← match priv with
    | some (v, pf) => pure (some (v, ← addFact `hpriv (← withMainContext do inferType pf) pf))
    | none => pure none
  let mut oldClear := old.toClear ++ consumed
  for R in old.regions do if R.hypM.isFVar && R.outW.isNone then oldClear := oldClear.push R.hypM.fvarId!
  if old.hunchM.isFVar then oldClear := oldClear.push old.hunchM.fvarId!
  if let some h := old.hroM then if h.isFVar then oldClear := oldClear.push h.fvarId!
  oldClear := oldClear ++ postClear
  clearFacts oldClear
  let mut newClear : Array FVarId := #[hpcF.fvarId!, hregsF.fvarId!, hcodeF.fvarId!]
  if let some (_, pf) := priv' then newClear := newClear.push pf.fvarId!
  let hmem ← withMainContext do mkEqRefl (mkApp (mkConst ``MachineState.mem) t)
  let st' := { old with s := t, pc := pcLit, pcE := pcv, hpc := hpcF, regs := regsT, regList := regList, hregs := hregsF, sM := t, hmem := hmem, regions := regions', hcode := hcodeF, k := old.k + 1, hunchM := hunchF, hroM := hroT, priv := priv', disj := disj, toClear := newClear, pureFacts := ← liveFacts (old.pureFacts ++ purePost) }
  set (← withMainContext st'.refresh)
where
  mkNatLitOf (hcw : Expr) (i : Nat) : MetaM Expr := do
    let ty ← inferType hcw
    return ty.getAppArgs[i]!
  lenOf (vs : Expr) (lens : Array (Expr × Expr × Expr)) : MetaM Expr := do
    match lens.find? (fun (l, _, _) => l == vs) with
    | some (_, n, _) => return n
    | none =>
      try return mkNatLit (← listElems vs).size
      catch _ =>
        let some (n, _) ← derivedLen vs
          | throwError "sym_exec: post region {vs}: not a literal, and its length is not known"
        return n
  proveByOmegaIntro (prop : Expr) : TacticM (Option Expr) := do
    let mv ← mkFreshExprMVar prop
    let saved ← getGoals
    try
      setGoals [mv.mvarId!]
      evalTactic (← `(tactic| (
        intro j hj hji
        (try simp (config := {decide := true}) only [AsmVerif.RiscV.Sym.add_ofNat_big, AsmVerif.RiscV.Sym.InRegion, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, not_and,
          Nat.not_lt])
        omega)))
      setGoals saved
      return some (← instantiateMVars mv)
    catch _ =>
      setGoals saved
      return none

/-- Apply a specification at the current state; `true` when it closes the path (it has no continuation:
    a `Safe P s` fact about every state at its pc, such as a panic entry). -/
def applySpec (spec : SpecInfo) : SymM Bool := do
  let st ← get
  let g ← getMainGoal
  let (c, mvs) ← g.withContext do
    let c ← match spec.term? with
      | some e => pure e
      | none => mkConstWithFreshMVarLevels spec.name
    let (mvs, _, concl) ← forallMetaTelescope (← instantiateMVars (← inferType c))
    unless ← isDefEq concl (← g.getType) do
      throwError "sym_exec: {spec.name} does not conclude `Safe P s` for this state:{indentExpr concl}\nvs{indentExpr (← g.getType)}"
    pure (c, mvs)
  -- a list argument with a length precondition `xs.length = n` is a list of `n`
  -- unknowns, so that the region it names can be found by its size
  g.withContext do
    for mv in mvs do
      let ty ← instantiateMVars (← inferType mv)
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOfArity ``List.length 2 do continue
      let l ← instantiateMVars lhs.appArg!
      unless l.isMVar do continue
      let some n ← getNatValue? rhs | continue
      let elemTy := lhs.appFn!.appArg!
      let cells ← (List.range n).toArray.mapM fun _ => mkFreshExprMVar elemTy
      l.mvarId!.assign (mkListLit elemTy cells)
  let mut cont : Option Expr := none
  -- the continuation is the last continuation-shaped argument; earlier ones (panic
  -- continuations `∀ u, u.pc = c → u.code = s.code → Safe P u`) are preconditions
  let lastCont? ← g.withContext do
    let mut r : Option Expr := none
    for mv in mvs do
      if isContinuation (← instantiateMVars (← inferType mv)) then r := some mv
    pure r
  -- preconditions in order, deferring those that mention a data argument a later
  -- one determines (a length fact before its region)
  let mut pending := mvs
  let mut progress := true
  while progress && !pending.isEmpty do
    progress := false
    let mut later := #[]
    for mv in pending do
      if ← g.withContext mv.mvarId!.isAssigned then continue
      let ty ← g.withContext do instantiateMVars (← inferType mv)
      if !(← g.withContext (isProp ty)) then continue
      if isContinuation ty && lastCont? == some mv then cont := some mv; continue
      let deferrable := ty.hasExprMVar && !(ty.isAppOf ``AsmVerif.RiscV.Sym.Region) && !(ty.eq?.any fun (_, l, _) =>
        l.isAppOf ``MachineState.getReg || l.isAppOf ``MachineState.pc)
      if deferrable && pending.size > 1 then
        later := later.push mv; continue
      let natCmp := !ty.hasExprMVar && (ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4) &&
        ty.getAppArgs[0]! == mkConst ``Nat
      let quick? ← if natCmp && (← get).multiSpec then g.withContext do
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            let dty ← instantiateMVars d.type
            if dty == ty then return some (some d.toExpr)
            -- decided false by a split arm: this specification does not apply here
            if dty == mkNot ty then
              throwError "sym_exec: {spec.name}: precondition{indentExpr ty}\nis false here"
          match ← proveByOmega ty (clusterOnly := true) with
          | some p => return some (some p)
          | none => return some none
        else pure none
      if let some r := quick? then
        if r.isNone then
          modify fun st => { st with undecided := st.undecided <|> some ty }
          throwError "sym_exec: {spec.name}: precondition{indentExpr ty}\nnot decided by the facts"
      let tP0 ← IO.monoMsNow
      let pf ← try (match quick? with | some (some p) => pure p | _ => discharge ty) catch e =>
        if natCmp then
          modify fun st => { st with undecided := st.undecided <|> some ty }
        let tP1 ← IO.monoMsNow
        if tP1 - tP0 > 1000 then trace[AsmVerif.sym.time] "  {spec.name}: {tP1 - tP0} ms failing on {ty}"
        throwError "sym_exec: {spec.name}: discharging{indentExpr ty}\n{e.toMessageData}"
      let tP1 ← IO.monoMsNow
      if tP1 - tP0 > 1000 then trace[AsmVerif.sym.time] "  {spec.name}: {tP1 - tP0} ms on {ty}"
      g.withContext do
        let lctx ← getLCtx
        let pf' ← instantiateMVars pf
        if pf'.hasAnyFVar (fun fv => !lctx.contains fv) then
          throwError "sym_exec: {spec.name}: the proof of{indentExpr ty}\nmentions a cleared hypothesis"
      let ok ← g.withContext (isDefEq mv pf)
      unless ok do throwError "sym_exec: precondition proof does not fit {ty}"
      progress := true
    if later.size == pending.size then
      -- nothing determined the deferred ones: discharge them as they are
      for mv in later do
        let ty ← g.withContext do instantiateMVars (← inferType mv)
        let pf ← discharge ty
        unless ← g.withContext (isDefEq mv pf) do throwError "sym_exec: precondition proof does not fit {ty}"
      later := #[]
    pending := later
  let some contMV := cont | do
    let g ← getMainGoal
    g.withContext do
      for mv in mvs do
        if !(← mv.mvarId!.isAssigned) then
          throwError "sym_exec: {spec.name}: argument {mv} of type {← inferType mv} not determined"
      g.assign (← instantiateMVars (mkAppN c mvs))
    replaceMainGoal []
    logInfo m!"sym_exec: applied {spec.name} at pc {spec.entry}, closing the path"
    return true
  let g ← getMainGoal
  let (t, hyps) ← g.withContext do
    for mv in mvs do
      if !(← mv.mvarId!.isAssigned) && mv != contMV then
        throwError "sym_exec: {spec.name}: argument {mv} of type {← inferType mv} not determined"
    let contTy ← instantiateMVars (← inferType contMV)
    let newG ← mkFreshExprSyntheticOpaqueMVar contTy
    contMV.mvarId!.assign newG
    g.assign (← instantiateMVars (mkAppN c mvs))
    let n := piArity contTy
    let names : List Name := `t :: (List.range (n - 1)).map fun i => Name.mkSimple s!"post{st.k}_{i}"
    let (fvs, g2) ← newG.mvarId!.introN n names
    replaceMainGoal [g2]
    -- the postcondition's hypotheses; data binders (`∀ t r0 r1 …`) are atoms, not facts
    let props ← g2.withContext do
      (fvs.extract 1 fvs.size).filterM fun fv => do isProp (← inferType (mkFVar fv))
    pure (mkFVar fvs[0]!, props.map mkFVar)
  trace[AsmVerif.sym] "{spec.name}: preconditions discharged"
  try readPost st t hyps
  catch e => throwError "sym_exec: {spec.name}: reading the postcondition back: {e.toMessageData}"
  logInfo m!"sym_exec: applied {spec.name} at pc {spec.entry}"
  return false

/-! ## Branches -/

inductive Res where
  | cont
  | stop
  | split (branches : Array (MVarId × Expr × Nat))   -- goal, hypothesis, target pc
  | splitHere (branches : Array (MVarId × Expr))    -- goal, hypothesis; the pc unchanged
  | done                                              -- the path is closed

def branchStep (f : Fetched) (rs1 rs2 off : Nat) (kind : String) : SymM Res := do
  let a ← valueOf rs1
  let b ← valueOf rs2
  let st ← get
  let s := st.s
  let pc := st.pc.getD 0
  let pc4 := (pc + 4) % two64
  let tgt := (pc + sext 13 off) % two64
  let cond : Option Bool := match a.lin.atom, b.lin.atom with
    | none, none =>
      let x := a.lin.c; let y := b.lin.c
      let sx : Int := if x < 2^63 then x else (x : Int) - two64
      let sy : Int := if y < 2^63 then y else (y : Int) - two64
      some <| match kind with
        | "BEQ" => x == y | "BNE" => x != y
        | "BLTU" => x < y | "BGEU" => x ≥ y
        | "BLT" => sx < sy | "BGE" => sx ≥ sy | _ => false
    | some p, some q =>
      if p == q then
        match kind with
        | "BEQ" => some (a.lin.c == b.lin.c)
        | "BNE" => some (a.lin.c != b.lin.c)
        | _ => none
      else none
    | _, _ => none
  let (hstep, eq, rhs) ← withMainContext do
    let hstep ← plainStep f
    let (eq, rhs) ← unfoldEq s f
    pure (hstep, eq, rhs)
  -- an unsigned compare of two offsets from one pointer: decided by `omega`
  -- from the no-wrap facts (`RegionOk`), as a fact for the step's `simp`
  let mut cmpFacts : Array Expr := #[]
  if cond.isNone && (kind == "BLTU" || kind == "BGEU") then
    if let (some p, some q) := (a.lin.atom, b.lin.atom) then
      if p == q then
        -- the no-wrap bounds of the regions at that pointer
        let nw ← withMainContext do
          let mut out := #[]
          for R in st.regions do
            if R.ok != noRegionOk && R.baseLin.sameAtom a.lin then
              out := out.push (← mkAppM ``AsmVerif.RiscV.Sym.RegionOk.nowrap #[← R.okE])
            if out.size ≥ 4 then break
          pure out
        for t in [true, false] do
          if !cmpFacts.isEmpty then break
          let pf? ← withMainContext do
            let lt ← mkAppM ``LT.lt #[← mkAppM ``BitVec.toNat #[a.val], ← mkAppM ``BitVec.toNat #[b.val]]
            let goal := if t then lt else mkNot lt
            let tys ← nw.mapM fun h => inferType h
            let prop := tys.foldr (fun h g => mkForall `h .default h g) goal
            let some pf ← proveByOmega prop | return none
            -- as the `toNat` comparison the branch lemmas unfold `ult` to
            return some (mkAppN pf nw)
          if let some pf := pf? then cmpFacts := cmpFacts.push pf
  -- try the facts first: a branch may be decided by a hypothesis
  let decided ← match cond with
    | some t => pure (some t)
    | none => withMainContext do
      let pr := st.pureFacts ++ cmpFacts
      for t in [true, false] do
        let target := if t then tgt else pc4
        let prop := mkEqMS rhs (mkSetPC s (mkWordLit target))
        if let some _ ← proveBySimp prop (#[st.hpc] ++ st.regRules ++ pr) branchLemmas then
          return some t
      pure none
  match decided with
  | some taken =>
    let target := if taken then tgt else pc4
    let hrest ← withMainContext do
      let pr := st.pureFacts ++ cmpFacts
      let prop := mkEqMS rhs (mkSetPC s (mkWordLit target))
      match ← proveBySimp prop (#[st.hpc] ++ st.regRules ++ pr) branchLemmas with
      | some p => pure p
      | none =>
        let r ← simpWith prop (#[st.hpc] ++ st.regRules ++ pr) branchLemmas
        throwError "sym_exec: could not discharge the branch {kind} at pc {pc} (decided {taken}): {r.expr}"
    pcStep hstep eq hrest target
    return .cont
  | none =>
    -- split on the condition, stated over the register values
    let g ← getMainGoal
    let branches ← g.withContext do
      let c := rhs.getAppArgs[1]!
      let (c', _) ← rewriteTo c (st.regRules ++ #[st.hpc]) normLemmas
      let (P, _) ← goalParts g
      let g1 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow c' (mkSafe P s))
      let g2 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (mkNot c') (mkSafe P s))
      g.assign (← mkAppOptM ``AsmVerif.RiscV.Sym.Safe.cases #[some P, some s, some c', some g1, some g2])
      let (h1, g1') ← g1.mvarId!.intro (Name.mkSimple s!"hbr{st.k}")
      let (h2, g2') ← g2.mvarId!.intro (Name.mkSimple s!"hbr{st.k}")
      pure #[(g1', mkFVar h1, tgt), (g2', mkFVar h2, pc4)]
    return .split branches

/-- Finish a split branch: the pc step under the branch hypothesis. -/
def branchArm (f : Fetched) (target : Nat) : SymM Unit := do
  let st ← get
  let s := st.s
  let (hstep, eq, hrest) ← withMainContext do
    let hstep ← plainStep f
    let (eq, rhs) ← unfoldEq s f
    let pr := st.pureFacts
    let prop := mkEqMS rhs (mkSetPC s (mkWordLit target))
    match ← proveBySimp prop (#[st.hpc] ++ st.regRules ++ pr) branchLemmas with
    | some p => pure (hstep, eq, p)
    | none =>
      let r ← simpWith prop (#[st.hpc] ++ st.regRules ++ pr) branchLemmas
      throwError "sym_exec: branch arm to {target} did not discharge: {r.expr}"
  pcStep hstep eq hrest target

/-! ## The driver -/

def stepOnce (first : Bool) : SymM (Res × Option Fetched) := do
  let st ← get
  let some pc := st.pc | do
    logInfo m!"sym_exec: stopping at a symbolic pc {st.pcE}"
    return (.stop, none)
  if !first && st.stops.contains pc then
    logInfo m!"sym_exec: stopping at requested pc {pc}"
    return (.stop, none)
  -- the specifications at this pc, in order: the first whose preconditions hold (on the
  -- first step too: a run resumed at a loop head applies the loop's lemma there)
  if true then
    let cands := st.specs.filter (·.entry == pc)
    if !cands.isEmpty then
      let mut lastErr : Option Exception := none
      let mut undecided : Option Expr := none
      for sp in cands do
        let saved ← (saveState : TacticM Tactic.SavedState)
        let stSaved ← get
        try
          set { stSaved with undecided := none, multiSpec := cands.size > 1 }
          let closed ← applySpec sp
          return (if closed then .done else .cont, none)
        catch e =>
          let u := (← get).undecided
          (restoreState saved : TacticM Unit)
          set stSaved
          lastErr := some e
          if undecided.isNone then undecided := u
      -- a precondition no fact decides (`32 ≤ l.toNat` for an `Ok` against an `Err`
      -- specification): split on it, and apply the specifications again in each arm
      if let some c := undecided then
        let g ← getMainGoal
        let branches ← g.withContext do
          let (P, _) ← goalParts g
          let g1 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow c (mkSafe P st.s))
          let g2 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (mkNot c) (mkSafe P st.s))
          g.assign (← mkAppOptM ``AsmVerif.RiscV.Sym.Safe.cases #[some P, some st.s, some c, some g1, some g2])
          let (h1, g1') ← g1.mvarId!.intro (Name.mkSimple s!"hsp{st.k}")
          let (h2, g2') ← g2.mvarId!.intro (Name.mkSimple s!"hsp{st.k}")
          pure #[(g1', mkFVar h1), (g2', mkFVar h2)]
        logInfo m!"sym_exec: no specification at pc {pc} applies; splitting on{indentExpr c}"
        return (.splitHere branches, none)
      if let some e := lastErr then throw e
  if !covered st pc then
    logInfo m!"sym_exec: stopping at pc {pc}: no `CodeAt` hypothesis covers it"
    return (.stop, none)
  let f ← withMainContext (fetch st pc)
  let op ← withMainContext (classify f.ins)
  let s := st.s
  match op with
  | .alu rd =>
    let (hstep, eq, rawV, pcE) ← withMainContext do
      let hstep ← plainStep f
      let (eq, rhs) ← unfoldEq s f
      pure (hstep, eq, rhs.getAppArgs[0]!.getAppArgs[2]!, rhs.getAppArgs[1]!)
    regStep hstep rd rawV pcE eq
    return (.cont, none)
  | .fence =>
    let (hstep, eq) ← withMainContext do
      let hstep ← plainStep f
      let (eq, _) ← unfoldEq s f
      pure (hstep, eq)
    let hrest ← withMainContext do
      let (_, rhs) ← unfoldEq s f
      match ← proveBySimp (mkEqMS rhs (mkSetPC s (mkWordLit ((pc + 4) % two64)))) #[st.hpc] normLemmas with
      | some p => pure p
      | none => throwError "sym_exec: fence"
    pcStep hstep eq hrest ((pc + 4) % two64)
    return (.cont, none)
  | .jal rd _ | .jalr rd _ _ =>
    if let .jalr _ rs1 _ := op then let _ ← valueOf rs1
    let (hstep, eq, rawV, pcE) ← withMainContext do
      let hstep ← plainStep f
      let (eq, rhs) ← unfoldEq s f
      pure (hstep, eq, rhs.getAppArgs[0]!.getAppArgs[2]!, rhs.getAppArgs[1]!)
    regStep hstep rd rawV pcE eq
    return (.cont, none)
  | .branch rs1 rs2 off kind =>
    let r ← branchStep f rs1 rs2 off kind
    return (r, some f)
  | .load rd rs1 off width signed =>
    let ok ← loadStep f rd rs1 off width signed
    return (if ok then .cont else .stop, none)
  | .store rs1 rs2 off width =>
    let ok ← storeStep f rs1 rs2 off width
    return (if ok then .cont else .stop, none)
  | .ecall =>
    let ok ← ecallStep f
    return (if ok then .cont else .stop, none)
  | .ebreak => logInfo m!"sym_exec: stopping at EBREAK at pc {pc}"; return (.stop, none)
  | .other => logInfo m!"sym_exec: stopping at unsupported instruction at pc {pc}"; return (.stop, none)

/-- At a stop, state the facts about the current state as hypotheses the user
    can name: `hxᵢ` for every register, `hRᵢ` for every region, `hunch`, `hcw`. -/
def materialize : SymM Unit := do
  if (← getGoals).isEmpty then return
  let st ← get
  for i in [1:32] do
    if let some f := st.regs[i]! then
      if f.val == mkGetReg st.s i then continue
      try
        let _ ← addFact (regName i) (mkEqW (mkGetReg st.s i) f.val) f.proof
      catch ex =>
        trace[AsmVerif.sym] "materialize: register {i} fact {f.val} failed: {ex.toMessageData}"
  for ri in [0:st.regions.size] do
    let R := st.regions[ri]!
    if R.hyp.isFVar then continue
    let _ ← addFact (Name.mkSimple s!"hR{ri}") (← withMainContext (inferType R.hyp)) R.hyp
  if !st.hunch.isFVar then
    let _ ← addFact `hunch (← withMainContext (inferType st.hunch)) st.hunch
  if !st.hcw.isFVar then
    let _ ← addFact `hcw (← withMainContext (inferType st.hcw)) st.hcw
  -- the read-only image, so that a later run from this state has it: from the image at the
  -- last memory state (as `refresh` builds it), or the refreshed `hro` field
  if let some h := st.hroM then
    try
      let stateOf (e : Expr) : TacticM Expr := withMainContext do
        let ty ← instantiateMVars (← inferType e)
        return ty.appArg!.consumeMData
      let at_ ← stateOf h
      let pf? ← if at_ == st.s then pure (some h)
        else if at_ == st.sM then withMainContext do
          some <$> mkAppM ``AsmVerif.RiscV.Sym.RoImage.of_mem_eq #[h, st.hmem]
        else match st.hro with
          | some h' => do if (← stateOf h') == st.s then pure (some h') else pure none
          | none => pure none
      if let some pf := pf? then
        if !pf.isFVar then
          let _ ← addFact `hro (← withMainContext (inferType pf)) pf
    catch ex => trace[AsmVerif.sym] "materialize: read-only image fact failed: {ex.toMessageData}"
  for c in st.codes do
    if !c.hyp.isFVar then
      let _ ← addFact `hcode' (← withMainContext (inferType c.hyp)) c.hyp

partial def runPath (budget : IO.Ref Nat) (first : Bool) : SymM (Array MVarId) := do
  let mut first := first
  repeat
    let n ← budget.get
    if n == 0 then
      logInfo m!"sym_exec: step budget exhausted"
      materialize
      break
    budget.set (n - 1)
    let t0 ← IO.monoMsNow
    let (r, f?) ← stepOnce first
    let t1 ← IO.monoMsNow
    if ← isTracingEnabledFor `AsmVerif.sym.time then
      -- (no main goal once the path is closed or split)
      let ctx ← try withMainContext do return (← getLCtx).size catch _ => pure 0
      trace[AsmVerif.sym.time] "step {(← get).k} pc {(← get).pc}: {t1 - t0} ms, ctx {ctx}"
    first := false
    match r with
    | .cont => continue
    | .stop => materialize; break
    | .done => return #[]
    | .split bs =>
      let st ← get
      let mut out := #[]
      for (g, h, target) in bs do
        setGoals [g]
        -- the branch hypothesis, in the normal form the branch lemmas produce
        let h ← withMainContext do
          let ty ← inferType h
          let r ← simpWith ty #[] branchLemmas
          if r.expr == ty then pure h else mkEqMP (← r.getProof) h
        set { st with pureFacts := st.pureFacts.push h }
        -- an arm whose condition contradicts the facts (`omega`, with the branch facts as
        -- `Nat`): closed here, so no load on it picks a region by a vacuous bound
        let seed ← withMainContext do return (← (← inferType h).collectFVars.run {}).2.fvarIds
        if let some pf ← withMainContext (proveByOmega (mkConst ``False) (extras := true) (seed := seed)
            (clusterOnly := true)) then
          let g ← getMainGoal
          g.assign (← mkAppOptM ``False.elim #[some (← g.getType), some pf])
          logInfo m!"sym_exec: the arm to pc {target} at pc {st.pc} is infeasible, pruned"
          continue
        branchArm f?.get! target
        out := out ++ (← runPath budget false)
      return out
    | .splitHere bs =>
      let st ← get
      let mut out := #[]
      for (g, h) in bs do
        setGoals [g]
        set { st with pureFacts := st.pureFacts.push h }
        let seed ← withMainContext do return (← (← inferType h).collectFVars.run {}).2.fvarIds
        if let some pf ← withMainContext (proveByOmega (mkConst ``False) (extras := true) (seed := seed)
            (clusterOnly := true)) then
          let g ← getMainGoal
          g.assign (← mkAppOptM ``False.elim #[some (← g.getType), some pf])
          logInfo m!"sym_exec: an arm of the split at pc {st.pc} is infeasible, pruned"
          continue
        out := out ++ (← runPath budget false)
      return out
  return (← getGoals).toArray

end AsmVerif.RiscV.Sym.Meta

namespace AsmVerif.RiscV.Sym

open Lean Elab Tactic

/-- `sym_exec [spec₁, …] n`: execute the goal `Safe P s` forward for at most `n`
    steps (default 100000), applying the named specifications at their entry
    points and stopping at any pc listed after `stop`. -/
syntax (name := symExec) "sym_exec" (" [" ident,* "]")? (" stop" " [" num,* "]")? (num)? : tactic

/-- The entry pc of a specification's type: its first `s.pc = lit` hypothesis. -/
def Meta.specEntryOf (ty : Expr) (n : Name) : MetaM Nat := do
  Meta.forallTelescope ty fun xs _ => do
    for x in xs do
      let t ← inferType x
      if let some (_, lhs, rhs) := t.eq? then
        if lhs.isAppOf ``RiscvZkvm.Rv64.MachineState.pc then
          if let some v ← Meta.litValue? rhs then return v
    throwError "sym_exec: {n} has no `s.pc = <literal>` hypothesis"

def Meta.specEntry (n : Name) : MetaM Nat := do
  Meta.specEntryOf (← inferType (← mkConstWithFreshMVarLevels n)) n

elab_rules : tactic
  | `(tactic| sym_exec $[ [$specs,*] ]? $[ stop [$stops,*] ]? $[$n:num]?) => do
    let budget := match n with | some n => n.getNat | none => 100000
    let specInfos ← match specs with
      | some ss => ss.getElems.mapM fun id => withMainContext do
          -- a local hypothesis, or a constant
          if let some d := (← getLCtx).findFromUserName? id.getId then
            return ({ name := id.getId, entry := ← Meta.specEntryOf (← instantiateMVars d.type) id.getId,
                      term? := some d.toExpr } : Meta.SpecInfo)
          let nm ← realizeGlobalConstNoOverloadWithInfo id
          return ({ name := nm, entry := ← Meta.specEntry nm } : Meta.SpecInfo)
      | none => pure #[]
    let stopPcs := match stops with
      | some ss => ss.getElems.map (·.getNat)
      | none => #[]
    let g0 ← getMainGoal
    let st ← Meta.initState specInfos stopPcs
    let ref ← IO.mkRef budget
    let (goals, _) ← (Meta.runPath ref true).run st
    setGoals goals.toList
    if (← Lean.isTracingEnabledFor `AsmVerif.sym.size) then
      let pf ← instantiateMVars (mkMVar g0)
      let mut seen : Std.HashSet UInt64 := {}
      let mut stack := #[pf]
      let mut n : Nat := 0
      while h : stack.size > 0 do
        let e := stack.back
        stack := stack.pop
        if seen.contains e.hash then continue
        seen := seen.insert e.hash
        n := n + 1
        match e with
        | .app f a => stack := (stack.push f).push a
        | .lam _ t b _ | .forallE _ t b _ => stack := (stack.push t).push b
        | .letE _ t v b _ => stack := ((stack.push t).push v).push b
        | .mdata _ b | .proj _ _ b => stack := stack.push b
        | _ => pure ()
      logInfo m!"sym_exec: proof DAG size {n}"
    logInfo m!"sym_exec: executed {budget - (← ref.get)} steps, {goals.size} goal(s) left"

end AsmVerif.RiscV.Sym
