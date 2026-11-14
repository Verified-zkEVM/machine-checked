/-
  MachineChecked.Logical.Lift

  Lift 2: an Lprog program over the shared operations as a Pancake program.

  The registers are global variables. **Each function of the program is a Pancake function**,
  without parameters:

      fun 1 f_memcpy() {
        var 1 top = x2;            // the stack pointer at the call
        …
      }

  * A call is a call: `x1 = ret; f_g();`, then `if (x1 != ret) { wrong }`. A return is
    `return 0;` and a tail call `return f_g();`, each after `if (x2 != top) { wrong }`. The two
    tests are what Lprog asks of a return (the link register holds the value the call put
    there, and the stack pointer is back), so the Pancake program does not carry on where
    the Lprog program goes `wrong`.
  * An indirect call whose target is a constant is a call of the function at that address.
    Any other goes through a function that searches its candidates (`l_call0(a)`).
  * The body is **structured** where the control flow of the function is reducible
    (`Logical/Structure.lean`): `if`, `while`, `break` and `continue`. Pancake leaves only the
    innermost loop, so a jump out of several sets `lbr` and each loop on the way passes it on.
  * Otherwise, and for a function too long for the compiler (`big`), the body is a **loop over
    its blocks**: a counter `lpc` names the block to run next, and the blocks are dealt out to
    functions of a few each (`f_c0(top)`, …), which is what keeps a long function compilable.
  * Within a run of code the values of registers that are constants are known, so that
    `auipc` and the `jalr` after it are a call of a named function.
  * `Lext n` is what the execution environment says (`Env.ext`), given the statement that
    ends the program: `throw l_halt 0`, which `main` catches.
  * Where the Lprog program goes `wrong` (`Labort`, a jump or call outside its candidates,
    running off the end), the Pancake program does what the environment says (`Env.wrong`).

  `main` installs the program (`Env.init`) and calls its entry.

  Nothing is proved of it. It is checked by running: `scripts/decompile-check`.

  ## Main definitions

  * `Env`, `lift`
-/

import MachineChecked.Logical.Ops
import MachineChecked.Logical.Structure

namespace MachineChecked.Logical

open MachineChecked.Lprog
open Flapjack (Exp Prog Decl Shape Shift)
open Pancake (W)

/-- What lift 2 needs of the execution environment of a program. -/
structure Env where
  /-- Run once, before the program: the installation. It may name the registers, which are
      global variables. -/
  init : List (Prog W)
  /-- Entry `n` of the environment, as a statement, given the statement that ends the
      program; `none` if there is no such entry. -/
  ext : Nat → Prog W → Option (Prog W)
  /-- What to do where the Lprog program goes `wrong`. Any behaviour would do, `wrong` being
      undefined; it should be one that cannot be mistaken for the program's. -/
  wrong : Prog W
  /-- Registers `init` and `ext` name. -/
  regs : List String
  /-- Functions `init` calls. -/
  decls : List (Decl W) := []

namespace Lift

/-! ## What is known -/

variable {Reg : Type} [RegText Reg]

/-- An expression with the registers of known value replaced, and what can be computed
    computed. -/
def fold (known : List (String × BitVec 64)) : Expr Reg → Expr Reg
  | .reg r => match known.lookup (RegText.name r) with
    | some v => .imm v
    | none => .reg r
  | .imm v => .imm v
  | .un o e => match fold known e with
    | .imm v => .imm (o.eval v)
    | e' => .un o e'
  | .bin o a b =>
    -- zero on the right, or on the left, changes nothing
    let right := o matches .add | .sub | .or | .xor | .shl | .lshr | .ashr
    let left := o matches .add | .or | .xor
    match fold known a, fold known b with
    | .imm x, .imm y => .imm (o.eval x y)
    | a', .imm y => if y == 0 && right then a' else .bin o a' (.imm y)
    | .imm x, b' => if x == 0 && left then b' else .bin o (.imm x) b'
    | a', b' => .bin o a' b'

/-- An operation with the registers of known value replaced, and what is known after it. -/
def foldOp (known : List (String × BitVec 64)) : Op Reg → Op Reg × List (String × BitVec 64)
  | .set d e =>
    let e' := fold known e
    let rest := known.filter (·.1 != RegText.name d)
    (.set d e', match e' with
      | .imm v => (RegText.name d, v) :: rest
      | _ => rest)
  | .load d w s a => (.load d w s (fold known a), known.filter (·.1 != RegText.name d))
  | .store w a e => (.store w (fold known a) (fold known e), known)
  | .skip => (.skip, known)

/-- An operand with a register of known value replaced. -/
def foldOperand (known : List (String × BitVec 64)) : LOperand Reg → LOperand Reg
  | .reg r => match known.lookup (RegText.name r) with
    | some v => .imm (v.toNat : Int)
    | none => .reg r
  | .cmp o a b => .cmp o (foldOperand known a) (foldOperand known b)
  | o => o

/-! ## Blocks -/

/-- How a block ends. -/
inductive Term where
  | goto (l : Nat)
  /-- To `l` if `c` holds, to `other` if not. -/
  | branch (c : Exp W) (l other : Nat)
  /-- To the block paired with the value of `x`; `wrong` if there is none. -/
  | switch (x : Exp W) (cs : List (BitVec 64 × Nat))
  /-- The statements of the block end the function. -/
  | exit

/-- A block: its number, its statements and how it ends. A block that starts at a label has
    the label as its number. -/
structure Block where
  id : Nat
  code : List (Prog W)
  /-- After `code`, the statements that end the function, if the block does. -/
  last : List (Prog W) := []
  term : Term

def Block.succs (b : Block) : List Nat :=
  match b.term with
  | .goto l => [l]
  | .branch _ l o => [l, o]
  | .switch _ cs => cs.map (·.2)
  | .exit => []

/-- The names the lift gives its own variables: the block to run next, the address an
    indirect jump is looking for, the loop a jump is leaving for, the stack pointer at the
    call, and the exception that ends the program. -/
def lpc : String := "lpc"
def lia : String := "lia"
def lbr : String := "lbr"
def top : String := "top"
def halt : String := "l_halt"

/-- What lifting a function needs of the program. -/
structure Cx (Reg : Type) where
  env : Env
  link : Reg
  sp : Reg
  /-- The Pancake name of each function, and its address. -/
  names : Array String
  addrs : Array (BitVec 64)

/-- The labels something jumps to. -/
def targets (body : Lcmd (Op Reg) Reg) : List Nat :=
  body.flatMap fun
    | .Lgoto l => [l]
    | .Lcond _ l => [l]
    | .Ligoto _ cs => cs.map (·.2)
    | _ => []

/-- The function a call calls, as a Pancake call: the statements before it, the name and the
    arguments. `none` if it calls nothing it may. -/
def callee (cx : Cx Reg) (known : List (String × BitVec 64)) :
    Target Reg → M (Option (List (Prog W) × String × List (Exp W)))
  | .direct f => pure (cx.names[f]?.map fun n => ([], n, []))
  | .indirect e cands =>
    match fold known e with
    | .imm v => pure ((cands.find? fun f => cx.addrs[f]? == some v).bind fun f =>
        cx.names[f]?.map fun n => ([], n, []))
    | e' => do
      let (ps, x) ← expr e'
      let t ← fresh
      let j ← modifyGet fun s =>
        match s.tables.idxOf? cands with
        | some j => (j, s)
        | none => (s.tables.size, { s with tables := s.tables.push cands })
      pure (some (ps ++ [gset t x], s!"l_call{j}", [gvar t]))

/-- The body of a function as blocks, the entry first. Code after a jump and before the next
    label something jumps to is never run, and is dropped. -/
def blocks (cx : Cx Reg) (body : Lcmd (Op Reg) Reg) : ExceptT String M (List Block) := do
  let .Llabel _ entry :: _ := body | throw "a function does not start at a label"
  let ts := targets body
  let isLeader : Std.HashSet Nat := (Std.HashSet.ofList ts).insert entry
  let link := RegText.name cx.link
  let sp := RegText.name cx.sp
  let stop : Prog W := .raise halt (num 0)
  let wrong := cx.env.wrong
  let backAt : List (Prog W) := [when (.cmp .notEqual (gvar sp) (var top)) [wrong]]
  let mut out : Array Block := #[]
  -- numbers for the blocks that start at no label
  let mut next := body.foldl (fun m i => match i with | .Llabel _ l => max m (l + 1) | _ => m) 0
  -- the block being built, and the registers of known value
  let mut cur : Option Nat := none
  let mut acc : Array (Prog W) := #[]
  let mut known : List (String × BitVec 64) := []
  for i in body do
    modify fun s => { s with temps := 0 }
    match i, cur with
    | .Llabel _ l, _ =>
      if isLeader.contains l then
        if let some c := cur then out := out.push ⟨c, acc.toList, [], .goto l⟩
        cur := some l
        acc := #[]
        known := []
    | _, none => pure ()
    | i, some c =>
      -- how the block ends, if this instruction ends it
      let mut last : Option (List (Prog W) × Term) := none
      match i with
      | .Lopn o =>
        let (o', known') := foldOp known o
        known := known'
        acc := acc ++ (← op o')
      | .Lgoto l => last := some ([], .goto l)
      | .Lcond cnd l =>
        match cond (foldOperand known cnd) with
        | some e =>
          out := out.push ⟨c, acc.toList, [], .branch e l next⟩
          cur := some next
          acc := #[]
          next := next + 1
        | none => last := some ([wrong], .exit)
      | .Ligoto e cs =>
        match fold known e with
        | .imm v => match cs.find? (·.1 == v) with
          | some (_, l) => last := some ([], .goto l)
          | none => last := some ([wrong], .exit)
        | e' =>
          let (ps, x) ← expr e'
          last := some (ps ++ [gset lia x], .switch (gvar lia) cs)
      | .Lcall ret tgt =>
        match ← callee cx known tgt with
        | some (ps, f, args) =>
          acc := acc ++ ps ++ [gset link (.const ret), .call (some (none, none)) f args,
            when (.cmp .notEqual (gvar link) (.const ret)) [wrong]]
        | none => last := some ([wrong], .exit)
        known := []
      | .Ltail tgt =>
        match ← callee cx known tgt with
        | some (ps, f, args) => last := some (backAt ++ ps ++ [.call none f args], .exit)
        | none => last := some ([wrong], .exit)
      | .Lret => last := some (backAt ++ [.return (num 0)], .exit)
      | .Lext n =>
        match cx.env.ext n stop with
        | some p => acc := acc.push p
        | none => last := some ([wrong], .exit)
        known := []
      | .Labort => last := some ([wrong], .exit)
      | .Llabel .. => pure ()
      if let some (ps, t) := last then
        out := out.push ⟨c, acc.toList, ps, t⟩
        cur := none
  -- running off the end
  if let some c := cur then out := out.push ⟨c, acc.toList, [wrong], .exit⟩
  return out.toList

/-! ## A structured body -/

open Structure (S)

/-- A loop of the Pancake program that stands for a block or a loop of the structure. -/
structure Frame where
  label : Nat
  isLoop : Bool
  deriving BEq

/-- The value of `lbr` that names a frame. -/
def Frame.code (f : Frame) : Nat := 2 * f.label + (if f.isLoop then 2 else 1)

/-- `if c { t } else { e }`, without the branch that is empty, and with what follows a
    branch that does not come back after it. -/
def choice (c : Exp W) (t e : List (Prog W)) (tFalls eFalls : Bool) : List (Prog W) :=
  if t.isEmpty && e.isEmpty then []
  else if t.isEmpty then [when (negate c) e]
  else if e.isEmpty then [when c t]
  else if !tFalls then when c t :: e
  else if !eFalls then when (negate c) e :: t
  else [.ite c (seq t) (seq e)]

/-- `while 1 { body }`, or `while c { … }` where the body starts by leaving unless `c`. -/
def loop : List (Prog W) → Prog W
  | .ite c .break .skip :: rest => .while (negate c) (seq rest)
  | body => .while (num 1) (seq body)

/-- After a loop that jumps out of several pass through: where `lbr` names the frame we are
    in now, the jump is done; otherwise it goes on. The frames still to be reached. -/
def pass (ctx : List Frame) (pending : List Nat) : List (Prog W) × List Nat :=
  match ctx with
  | [] => ([], [])
  | f :: _ =>
    let rest := pending.filter (· != f.code)
    let here : List (Prog W) := [set lbr (num 0), if f.isLoop then .continue else .break]
    if !pending.contains f.code then
      (if rest.isEmpty then [] else [when (.cmp .notEqual (var lbr) (num 0)) [.break]], rest)
    else if rest.isEmpty then ([when (.cmp .notEqual (var lbr) (num 0)) here], [])
    else ([when (.cmp .equal (var lbr) (num f.code)) here,
           when (.cmp .notEqual (var lbr) (num 0)) [.break]], rest)

/-- A jump to a frame: `break` or `continue` for the innermost, and through `lbr` for one
    further out. -/
def jump (wrong : Prog W) (ctx : List Frame) (f : Frame) : List (Prog W) × List Nat :=
  match ctx.idxOf? f with
  | some 0 => ([if f.isLoop then .continue else .break], [])
  | some _ => ([set lbr (num f.code), .break], [f.code])
  | none => ([wrong], [])

/-- The statements of a structure, inside the frames `ctx` (innermost first), and the frames
    its jumps through `lbr` are for. -/
def emit (wrong : Prog W) (block : Nat → Option Block) : S → List Frame → List (Prog W) × List Nat
  | .nil, _ | .stop, _ => ([], [])
  | .seq a b, ctx =>
    let (p, c) := emit wrong block a ctx
    let (q, d) := emit wrong block b ctx
    (p ++ q, (c ++ d).eraseDups)
  | .node n, _ => (((block n).map fun b => b.code ++ b.last).getD [wrong], [])
  | .ite n t e, ctx =>
    let (p, c) := emit wrong block t ctx
    let (q, d) := emit wrong block e ctx
    match block n with
    | some { term := .branch cnd _ _, .. } => (choice cnd p q t.fallsThrough e.fallsThrough, (c ++ d).eraseDups)
    | _ => ([wrong], [])
  | .arm n k t e, ctx =>
    let (p, c) := emit wrong block t ctx
    let (q, d) := emit wrong block e ctx
    match block n with
    | some { term := .switch x cs, .. } => match cs[k]? with
      | some (a, _) =>
        (choice (.cmp .equal x (.const a)) p q t.fallsThrough e.fallsThrough, (c ++ d).eraseDups)
      | none => ([wrong], [])
    | _ => ([wrong], [])
  | .fail, _ => ([wrong], [])
  | .block l b, ctx =>
    let (p, c) := emit wrong block b (⟨l, false⟩ :: ctx)
    let (after, rest) := pass ctx c
    (.while (num 1) (seq (p ++ if b.fallsThrough then [.break] else [])) :: after, rest)
  | .loop l b, ctx =>
    let (p, c) := emit wrong block b (⟨l, true⟩ :: ctx)
    let (after, rest) := pass ctx c
    (loop p :: after, rest)
  | .exit l, ctx => jump wrong ctx ⟨l, false⟩
  | .again l, ctx => jump wrong ctx ⟨l, true⟩
  | .leave, _ => ([.break], [])

/-! ## A loop over the blocks -/

/-- `lpc = l; continue;` -/
def goto (l : Nat) : List (Prog W) := [gset lpc (num l), .continue]

/-- A search by halves among at most `2 ^ n` sorted keys. -/
def searchN (wrong : Prog W) (x : Exp W) (leaf : Nat × Prog W → Prog W) :
    Nat → List (Nat × Prog W) → Prog W
  | _, [] => wrong
  | _, [k] => leaf k
  | 0, _ => wrong
  | n + 1, ks =>
    match ks.drop (ks.length / 2) with
    | (m, _) :: _ =>
      .ite (.cmp .lower x (num m)) (searchN wrong x leaf n (ks.take (ks.length / 2)))
        (searchN wrong x leaf n (ks.drop (ks.length / 2)))
    | [] => wrong

/-- A search by halves among sorted keys: the statement for the key `x` holds. -/
def search (wrong : Prog W) (x : Exp W) (leaf : Nat × Prog W → Prog W) (ks : List (Nat × Prog W)) :
    Prog W :=
  searchN wrong x leaf ks.length ks

/-- A search for the key equal to `x`. -/
def find (wrong : Prog W) (x : Exp W) (ks : List (Nat × Prog W)) : Prog W :=
  search wrong x (fun (a, p) => .ite (.cmp .equal x (num a)) p wrong)
    (ks.toArray.qsort (·.1 < ·.1)).toList

/-- The most blocks a function of the loop holds. -/
def chunk : Nat := 8

/-- `bs` in runs of at most `n`. -/
def runs {α : Type} (n : Nat) (bs : List α) : List (List α) :=
  if bs.isEmpty ∨ n = 0 then [] else
    (List.range ((bs.length + n - 1) / n)).map fun i => (bs.drop (i * n)).take n

/-- The statements of a block in the loop, with the blocks only it reaches (those that
    start at no label, `inline`) after it. -/
def blockCode (block : Nat → Option Block) (inline : Nat → Bool) (table : Nat → Nat) :
    Nat → Block → List (Prog W)
  | 0, b => b.code ++ b.last
  | fuel + 1, b => b.code ++ b.last ++ match b.term with
    | .goto l => goto l
    | .branch c l o =>
      when c (goto l) :: match (if inline o then block o else none) with
        | some b' => blockCode block inline table fuel b'
        | none => goto o
    | .switch .. => goto (table b.id)
    | .exit => []

/-- The function of the blocks `bs`, sorted, numbered from `lo` to `hi`: it runs them until
    `lpc` names none of them, and then returns 1; a block that ends the function returns 0. -/
def chunkFn (wrong : Prog W) (name : String) (lo hi : Nat) (bs : List (Nat × Prog W)) : Decl W :=
  fn name [top] <| seq
    [.while (num 1) <| seq
      [when (.cmp .lower (gvar lpc) (num lo)) [.return (num 1)],
       when (.cmp .notLower (gvar lpc) (num (hi + 1))) [.return (num 1)],
       search wrong (gvar lpc) (fun (l, p) => .ite (.cmp .equal (gvar lpc) (num l)) p wrong) bs],
     .return (num 1)]

/-- A function as a loop over its blocks: the functions that hold the blocks, then the
    function itself, which calls the one `lpc` is in. -/
def looped (wrong : Prog W) (sp name : String) (bs : List Block) : List (Decl W) :=
  let block (n : Nat) := bs.find? (·.id == n)
  let entry := (bs.head?.map (·.id)).getD 0
  let preds := bs.flatMap (·.succs)
  -- a block only its predecessor's branch falls into
  let inline (n : Nat) : Bool := n != entry && (preds.filter (· == n)).length == 1 &&
    bs.any fun b => match b.term with
      | .branch _ _ o => o == n
      | _ => false
  let maxId := bs.foldl (fun m b => max m b.id) 0
  let switches := bs.filter fun b => b.term matches .switch ..
  let table (id : Nat) : Nat := maxId + 1 + (switches.findIdx? (·.id == id)).getD 0
  let own := (bs.filter fun b => !inline b.id).map fun b =>
    (b.id, seq (blockCode block inline table bs.length b))
  let tables := switches.filterMap fun b => match b.term with
    | .switch x cs => some (table b.id, find wrong x (cs.map fun (a, l) => (a.toNat, seq (goto l))))
    | _ => none
  let all := ((own ++ tables).toArray.qsort (·.1 < ·.1)).toList
  let chunks := (runs chunk all).zipIdx.filterMap fun (bs, j) =>
    match bs.head?, bs.getLast? with
    | some (lo, _), some (hi, _) => some (s!"{name}_c{j}", lo, hi, bs)
    | _, _ => none
  let r := "lr"
  (chunks.map fun (n, lo, hi, bs) => chunkFn wrong n lo hi bs) ++
  [fn name [] <| .dec top .one (gvar sp) <| .dec r .one (num 0) <| seq
    [gset lpc (num entry),
     .while (num 1) <| seq
       [search wrong (gvar lpc)
          (fun (_, p) => p)
          (chunks.map fun (n, lo, _, _) => (lo, .call (some (some (.local, r), none)) n [var top])),
        when (.cmp .equal (var r) (num 0)) [.return (num 0)]],
     .return (num 0)]]

/-! ## Functions -/

/-- Does the statement assign to the local `x`? -/
def assigns (x : String) : Prog W → Bool
  | .assign .local y _ => y == x
  | .dec _ _ _ p | .while _ p | .decCall _ _ _ _ p => assigns x p
  | .seq p q | .ite _ p q => assigns x p || assigns x q
  | _ => false

/-- A function with more instructions than this is a loop over its blocks even if it has a
    structure: Flapjack's time grows with the square of a function's length. -/
def big : Nat := 3000

/-- The most candidates of an indirect jump in a structured body. -/
def wide : Nat := 16

/-- The most statements in a row: a longer run is dealt out to functions of its own, for the
    same reason. -/
def long : Nat := 64

/-- The blocks with each long run of statements as calls of functions that hold it, and
    those functions. The statements of a run are operations and calls, which mean the same
    in any function: they name only globals. -/
def outline (name : String) (bs : List Block) : List Block × List (Decl W) := Id.run do
  let mut out : Array Block := #[]
  let mut fns : Array (Decl W) := #[]
  for b in bs do
    if b.code.length ≤ long then out := out.push b
    else
      let mut calls : Array (Prog W) := #[]
      for run in runs long b.code do
        let f := s!"{name}_s{fns.size}"
        fns := fns.push (fn f [] (seq (run ++ [.return (num 0)])))
        calls := calls.push (.call (some (none, none)) f [])
      out := out.push { b with code := calls.toList }
  return (out.toList, fns.toList)

/-- A function, lifted: structured if it can be. -/
def function (cx : Cx Reg) (name : String) (fd : Lfundef (Op Reg) Reg) :
    ExceptT String M (List (Decl W)) := do
  let (bs, runFns) := outline name (← blocks cx fd.body)
  let wrong := cx.env.wrong
  let sp := RegText.name cx.sp
  let index : Std.HashMap Nat Nat := Std.HashMap.ofList (bs.zipIdx.map fun (b, k) => (b.id, k))
  let arr := bs.toArray
  let succs := arr.map fun b => b.succs.map fun l => (index[l]?).getD arr.size
  let small := fd.body.length ≤ 2 * big && bs.all fun b => match b.term with
    | .switch _ cs => cs.length ≤ wide
    | _ => true
  match (if small then Structure.«structure» succs else none) with
  | some s =>
    let (ps, pending) := emit wrong (fun k => arr[k]?) s []
    if !pending.isEmpty then throw s!"{name}: a jump out of a loop goes nowhere"
    let usesLbr := ps.any (assigns lbr)
    let body := seq (ps ++ [.return (num 0)])
    return runFns ++ [fn name [] <| .dec top .one (gvar sp) <|
      if usesLbr then .dec lbr .one (num 0) body else body]
  | none => return runFns ++ looped wrong sp name bs

end Lift

open Lift in
/-- The Pancake name of each function: `f_` and its own name where that is a short
    identifier no other function has, `f` and its index otherwise. -/
def names {Op Reg : Type} (p : Lprog Op Reg) : Array String :=
  let ok (s : String) : Bool := !s.isEmpty && s.length ≤ 40 && s.all fun c => c.isAlphanum || c == '_'
  let all := p.map (·.name)
  (p.zipIdx.map fun (fd, i) =>
    if ok fd.name && (all.filter (· == fd.name)).length == 1 then s!"f_{fd.name}" else s!"f{i}").toArray

open Lift in
/-- **Lift 2.** A program, as a Pancake program whose `main` installs it in the environment
    `env` and calls its function `entry`. `regs` are its registers, `link` and `sp` the link
    register and the stack pointer of its instruction set. -/
def lift {Reg : Type} [RegText Reg] (env : Env) (regs : List Reg) (link sp : Reg) (entry : Nat)
    (p : Lprog (Op Reg) Reg) : Except String (List (Decl W)) := do
  let fnames := names p
  let cx : Cx Reg := { env, link, sp, names := fnames, addrs := (p.map (·.addr)).toArray }
  let some start := fnames[entry]? | throw "the program has no such entry"
  let all : ExceptT String M (List (List (Decl W))) :=
    p.zipIdx.mapM fun (fd, i) => function cx fnames[i]! fd
  let (r, st) := all.run.run {}
  let fns ← r
  -- the functions that search the candidates of the indirect calls
  let calls := st.tables.toList.zipIdx.map fun (cands, j) =>
    fn s!"l_call{j}" ["a"] <| seq
      [find env.wrong (var "a") (cands.filterMap fun f => do
          some ((← cx.addrs[f]?).toNat, .call none (← fnames[f]?) [])),
       .return (num 0)]
  let globals := (regs.map RegText.name ++ env.regs).eraseDups ++
    (List.range st.maxTemps).map temp ++ [lia, lpc]
  let r := "r"
  let main := fn "main" [] <| seq <|
    env.init ++
    [.dec r .one (num 0) <| seq
      [.call (some (some (.local, r), some (halt, r, .return (num 0)))) start [],
       .return (num 0)]]
  let called := st.called.flatMap fun f => needs f ++ [f]
  return [Decl.exnDecl halt .one] ++ globals.map (fun x => Decl.decl .one x (num 0)) ++
    (helpers.filter (called.contains ·.1) |>.map (·.2)) ++ env.decls ++ calls ++ fns.flatten ++ [main]

end MachineChecked.Logical
