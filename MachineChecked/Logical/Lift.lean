/-
  MachineChecked.Logical.Lift

  Lift 2, baseline: an Lprog program over the shared operations as a Pancake program.

  The baseline keeps the shape of the Lprog program and recovers no structure. The registers
  become global variables, with a counter `lpc` that names the block to run next. The blocks
  are dealt out, a few at a time, to functions, each a loop that runs its own blocks until
  `lpc` leaves them; `main` is the loop that calls the function `lpc` is in:

      var 1 x1 = 0; …                   // the registers, `lpc`
      fun 1 c0() {
        while 1 {
          if (lpc >=+ 9) { return 0; }
          if (lpc <+ 4) { … } else { … }   // a search for the block `lpc` names
        }
      }
      fun 1 main() {
        …                               // the installation (`Env.init`)
        lpc = 0;
        while 1 {
          if (lpc == 211) { return 0; }    // the program has ended
          if (lpc <+ 9) { c0(); } else { … }
        }
      }

  Small functions are for the compiler's sake: Flapjack's time grows much faster than a
  function does.

  * A block starts at a label something jumps to, and runs to the next such label.
  * `Lgoto` and `Lcond` set `lpc` and `continue`. `Ligoto` goes through a block that searches
    its candidates for the address.
  * An operation is an assignment, a load or a store. Pancake has `+ - * & | ^`, shifts by a
    constant and the comparisons; what it lacks (a shift by a register, the high halves of a
    product, division) is a call to a function written here in Pancake (`helpers`). Memory is
    Pancake's memory at the same addresses, so where the program's memory lives is up to the
    installation.
  * `Lext n` is what the execution environment says (`Env.ext`), given the statement that
    ends the program.
  * Where the Lprog program goes `wrong` (`Labort`, a jump outside its candidates, running
    off the end), the Pancake program loops for ever. Any behaviour would do, `wrong` being
    undefined; a loop is the one a test cannot mistake for a pass.

  It lifts a program of one function: `Lcall`, `Ltail` and `Lret` are not lifted yet.

  Nothing is proved of it. It is checked by running: `Tools/README.md` (`decompile`).

  ## Main definitions

  * `Env`, `lift`
-/

import MachineChecked.Lprog.Text
import MachineChecked.Logical.Pancake

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
  /-- Registers `init` and `ext` name. -/
  regs : List String

namespace Lift

/-! ## Pancake, briefly -/

def var (x : String) : Exp W := .var .local x
def num (n : Nat) : Exp W := .const (BitVec.ofNat 64 n)
def set (x : String) (e : Exp W) : Prog W := .assign .local x e
/-- A global: a register, or a variable of the lift's own. -/
def gvar (x : String) : Exp W := .var .global x
def gset (x : String) (e : Exp W) : Prog W := .assign .global x e
def add (a b : Exp W) : Exp W := .op .add [a, b]
def sub (a b : Exp W) : Exp W := .op .sub [a, b]
def band (a b : Exp W) : Exp W := .op .and [a, b]
def bor (a b : Exp W) : Exp W := .op .or [a, b]
def mul (a b : Exp W) : Exp W := .panOp .mul [a, b]
def shl (a : Exp W) (n : Nat) : Exp W := .shift .lsl a (num n)
def shr (a : Exp W) (n : Nat) : Exp W := .shift .lsr a (num n)
def sar (a : Exp W) (n : Nat) : Exp W := .shift .asr a (num n)

/-- Statements in sequence. -/
def seq : List (Prog W) → Prog W
  | [] => .skip
  | [p] => p
  | p :: ps => .seq p (seq ps)

/-- `if c { ps }`. -/
def when (c : Exp W) (ps : List (Prog W)) : Prog W := .ite c (seq ps) .skip

/-- The loop that never ends: where the Lprog program goes `wrong`. -/
def wrong : Prog W := .while (num 1) .skip

/-- A function of words. -/
def fn (name : String) (params : List String) (body : Prog W) : Decl W :=
  .function { name, inline := false, exported := false, params := params.map (·, .one), body,
              returnShape := .one }

/-! ## What Pancake lacks

Each is a Pancake function with the meaning of the Lprog operation (`BinOp.eval`). -/

/-- A shift by `n`, a bit of `n` at a time; `big` is the result when `n` is 64 or more. -/
def shiftFn (name : String) (o : Shift) (big : Exp W) : Decl W :=
  fn name ["a", "n"] <| seq <|
    [when (.cmp .notLower (var "n") (num 64)) [.return big]] ++
    ([1, 2, 4, 8, 16, 32].map fun k =>
      when (.cmp .notEqual (band (var "n") (num k)) (num 0)) [set "a" (.shift o (var "a") (num k))]) ++
    [.return (var "a")]

/-- The high half of the unsigned product, from the four products of the halves. -/
def mulhuFn : Decl W :=
  let m := num 0xffffffff
  fn "l_mulhu" ["a", "b"] <|
    .dec "al" .one (band (var "a") m) <| .dec "ah" .one (shr (var "a") 32) <|
    .dec "bl" .one (band (var "b") m) <| .dec "bh" .one (shr (var "b") 32) <|
    .dec "t" .one (mul (var "al") (var "bl")) <|
    .dec "u" .one (add (mul (var "ah") (var "bl")) (shr (var "t") 32)) <|
    .dec "v" .one (add (mul (var "al") (var "bh")) (band (var "u") m)) <|
    .return (add (add (mul (var "ah") (var "bh")) (shr (var "u") 32)) (shr (var "v") 32))

/-- The high half of a product with signed operands, from the unsigned one: a negative
    operand takes the other away. `both` is false for signed by unsigned. -/
def mulhFn (name : String) (both : Bool) : Decl W :=
  fn name ["a", "b"] <| .decCall "r" .one "l_mulhu" [var "a", var "b"] <| seq <|
    [when (.cmp .less (var "a") (num 0)) [set "r" (sub (var "r") (var "b"))]] ++
    (if both then [when (.cmp .less (var "b") (num 0)) [set "r" (sub (var "r") (var "a"))]] else []) ++
    [.return (var "r")]

/-- Unsigned division, a bit at a time: the quotient, or the remainder. Division by zero
    gives all ones, and the dividend as the remainder. -/
def divuFn (name : String) (quotient : Bool) : Decl W :=
  fn name ["a", "b"] <| seq
    [when (.cmp .equal (var "b") (num 0)) [.return (if quotient then .const (-1) else var "a")],
     .dec "q" .one (num 0) <| .dec "r" .one (num 0) <| .dec "i" .one (num 0) <|
     .dec "c" .one (num 0) <| seq
      [.while (.cmp .notEqual (var "i") (num 64)) <| seq
        [set "c" (shr (var "r") 63),
         set "r" (bor (shl (var "r") 1) (shr (var "a") 63)),
         set "a" (shl (var "a") 1),
         set "q" (shl (var "q") 1),
         when (bor (var "c") (.cmp .notLower (var "r") (var "b")))
           [set "r" (sub (var "r") (var "b")), set "q" (bor (var "q") (num 1))],
         set "i" (add (var "i") (num 1))],
       .return (var (if quotient then "q" else "r"))]]

/-- Signed division from unsigned, on the magnitudes. The quotient is negative when the
    signs differ, and the remainder has the sign of the dividend. -/
def divFn (name : String) (quotient : Bool) : Decl W :=
  let neg (x : String) := when (.cmp .less (var x) (num 0)) [set x (sub (num 0) (var x))]
  fn name ["a", "b"] <| seq
    [when (.cmp .equal (var "b") (num 0)) [.return (if quotient then .const (-1) else var "a")],
     .dec "s" .one
        (if quotient then .cmp .notEqual (.cmp .less (var "a") (num 0)) (.cmp .less (var "b") (num 0))
         else .cmp .less (var "a") (num 0)) <|
     seq [neg "a", neg "b",
       .decCall "r" .one (if quotient then "l_divu" else "l_remu") [var "a", var "b"] <|
       seq [when (var "s") [set "r" (sub (num 0) (var "r"))], .return (var "r")]]]

/-- The function for an operation Pancake lacks, by name, after the ones it calls. -/
def helpers : List (String × Decl W) :=
  [("l_shl", shiftFn "l_shl" .lsl (num 0)),
   ("l_lshr", shiftFn "l_lshr" .lsr (num 0)),
   ("l_ashr", shiftFn "l_ashr" .asr (sar (var "a") 63)),
   ("l_mulhu", mulhuFn),
   ("l_mulh", mulhFn "l_mulh" true),
   ("l_mulhsu", mulhFn "l_mulhsu" false),
   ("l_divu", divuFn "l_divu" true),
   ("l_remu", divuFn "l_remu" false),
   ("l_div", divFn "l_div" true),
   ("l_rem", divFn "l_rem" false)]

/-- What a function calls. -/
def needs : String → List String
  | "l_mulh" | "l_mulhsu" => ["l_mulhu"]
  | "l_div" => ["l_divu"]
  | "l_rem" => ["l_remu"]
  | _ => []

/-! ## Expressions and operations -/

/-- While lifting: the temporaries in use, the most that were, and the functions called. -/
structure St where
  temps : Nat := 0
  maxTemps : Nat := 0
  called : List String := []

abbrev M := StateM St

def temp (i : Nat) : String := s!"lt{i}"

/-- A fresh temporary. -/
def fresh : M String := modifyGet fun s =>
  (temp s.temps, { s with temps := s.temps + 1, maxTemps := max s.maxTemps (s.temps + 1) })

/-- `f(a, b)` into a fresh temporary. -/
def call2 (f : String) (a b : Exp W) : M (List (Prog W) × Exp W) := do
  let t ← fresh
  modify fun s => { s with called := if s.called.contains f then s.called else f :: s.called }
  return ([.call (some (some (.global, t), none)) f [a, b]], gvar t)

variable {Reg : Type} [RegText Reg]

/-- An expression: the statements that compute what Pancake cannot say in one, and the
    expression for the value. -/
def expr : Expr Reg → M (List (Prog W) × Exp W)
  | .reg r => pure ([], gvar (RegText.name r))
  | .imm v => pure ([], .const v)
  | .un op e => do
    let (ps, x) ← expr e
    let k (w : Width) := 64 - w.bits
    pure (ps, match op with
      | .sext .b8 | .zext .b8 => x
      | .sext w => sar (shl x (k w)) (k w)
      | .zext w => shr (shl x (k w)) (k w)
      | .not => .op .xor [x, .const (-1)]
      | .neg => sub (num 0) x)
  | .bin op a b => do
    let (pa, x) ← expr a
    let (pb, y) ← expr b
    let direct (e : Exp W) : M (List (Prog W) × Exp W) := pure (pa ++ pb, e)
    let viaCall (f : String) : M (List (Prog W) × Exp W) := do
      let (pc, e) ← call2 f x y
      pure (pa ++ pb ++ pc, e)
    let shiftBy (o : Shift) (f : String) (big : Exp W) : M (List (Prog W) × Exp W) :=
      match y with
      | .const n => direct (if n.toNat < 64 then .shift o x (num n.toNat) else big)
      | _ => viaCall f
    match op with
    | .add => direct (add x y)
    | .sub => direct (sub x y)
    | .mul => direct (mul x y)
    | .and => direct (band x y)
    | .or => direct (bor x y)
    | .xor => direct (.op .xor [x, y])
    | .slt => direct (.cmp .less x y)
    | .ult => direct (.cmp .lower x y)
    | .shl => shiftBy .lsl "l_shl" (num 0)
    | .lshr => shiftBy .lsr "l_lshr" (num 0)
    | .ashr => shiftBy .asr "l_ashr" (sar x 63)
    | .mulh => viaCall "l_mulh"
    | .mulhsu => viaCall "l_mulhsu"
    | .mulhu => viaCall "l_mulhu"
    | .div => viaCall "l_div"
    | .divu => viaCall "l_divu"
    | .rem => viaCall "l_rem"
    | .remu => viaCall "l_remu"

/-- An expression held in a variable, for a value used more than once. -/
def exprVar (e : Expr Reg) : M (List (Prog W) × Exp W) := do
  let (ps, x) ← expr e
  match x with
  | .var .. | .const _ => pure (ps, x)
  | _ => do
    let t ← fresh
    pure (ps ++ [gset t x], gvar t)

/-- The `n` bytes at `a`, little-endian, as a value. -/
def loadBytes (a : Exp W) : Nat → Exp W
  | 0 => num 0
  | n + 1 => (List.range n).foldl
      (fun acc i => bor acc (shl (.loadByte (add a (num (i + 1)))) (8 * (i + 1)))) (.loadByte a)

/-- An operation. A word and a byte are Pancake's own load and store; the widths between go
    by bytes. (Pancake has `ld32` and `st32`, but the Flapjack that the tests are compiled
    with rejects them at an address that names a local.) -/
def op : Op Reg → M (List (Prog W))
  | .skip => pure []
  | .set d e => do
    let (ps, x) ← expr e
    pure (ps ++ [gset (RegText.name d) x])
  | .load d w signed a => do
    let (ps, x) ← if w = .b2 ∨ w = .b4 then exprVar a else expr a
    let v : Exp W := match w with
      | .b8 => .load .one x
      | .b4 => loadBytes x 4
      | .b2 => loadBytes x 2
      | .b1 => .loadByte x
    let k := 64 - w.bits
    pure (ps ++ [gset (RegText.name d) (if signed ∧ w ≠ .b8 then sar (shl v k) k else v)])
  | .store w a e => do
    let wide := w = .b2 ∨ w = .b4
    let (pa, x) ← if wide then exprVar a else expr a
    let (pe, y) ← if wide then exprVar e else expr e
    pure (pa ++ pe ++ match w with
      | .b8 => [.store x y]
      | .b1 => [.storeByte x y]
      | _ => (List.range w.bytes).map fun i => .storeByte (add x (num i)) (shr y (8 * i)))

/-- A branch condition. -/
def cond : LOperand Reg → Option (Exp W)
  | .cmp o a b => do
    let val : LOperand Reg → Option (Exp W)
      | .reg r => some (gvar (RegText.name r))
      | .imm v => some (.const (BitVec.ofInt 64 v))
      | _ => none
    let c ← match o with
      | "eq" => some Flapjack.Cmp.equal
      | "ne" => some .notEqual
      | "lt" => some .less
      | "ge" => some .notLess
      | "ltu" => some .lower
      | "geu" => some .notLower
      | _ => none
    some (.cmp c (← val a) (← val b))
  | _ => none

/-! ## Blocks -/

/-- The block to run next, and the address an indirect jump is looking for. -/
def lpc : String := "lpc"
def lia : String := "lia"

/-- `lpc = l; continue;` -/
def goto (l : Nat) : List (Prog W) := [gset lpc (num l), .continue]

/-- A search by halves among at most `2 ^ n` sorted keys. -/
def searchN (x : Exp W) (leaf : Nat × Prog W → Prog W) : Nat → List (Nat × Prog W) → Prog W
  | _, [] => wrong
  | _, [k] => leaf k
  | 0, _ => wrong
  | n + 1, ks =>
    match ks.drop (ks.length / 2) with
    | (m, _) :: _ =>
      .ite (.cmp .lower x (num m)) (searchN x leaf n (ks.take (ks.length / 2)))
        (searchN x leaf n (ks.drop (ks.length / 2)))
    | [] => wrong

/-- A search by halves among sorted keys: the statement for the key `x` holds. -/
def search (x : Exp W) (leaf : Nat × Prog W → Prog W) (ks : List (Nat × Prog W)) : Prog W :=
  searchN x leaf ks.length ks

/-- The labels something jumps to. -/
def targets (body : Lcmd (Op Reg) Reg) : List Nat :=
  body.flatMap fun
    | .Lgoto l => [l]
    | .Lcond _ l => [l]
    | .Ligoto _ cs => cs.map (·.2)
    | _ => []

/-- The body of a function as blocks, each with the label it starts at, and the candidate
    lists of its indirect jumps: the block that searches list `j` is numbered `top + j`.
    Code after a jump and before the next label something jumps to is never run, and is
    dropped. -/
def blocks (env : Env) (stop : Prog W) (top : Nat) (leader : Nat → Bool) (body : Lcmd (Op Reg) Reg) :
    ExceptT String M (List (Nat × Prog W) × List (List (BitVec 64 × Nat))) := do
  let mut out : Array (Nat × Prog W) := #[]
  let mut tables : Array (List (BitVec 64 × Nat)) := #[]
  -- the block being built: its label and its statements so far
  let mut cur : Option Nat := none
  let mut acc : Array (Prog W) := #[]
  for i in body do
    modify fun s => { s with temps := 0 }
    match i, cur with
    | .Llabel _ l, _ =>
      if leader l then
        if let some c := cur then out := out.push (c, seq (acc.toList ++ goto l))
        cur := some l
        acc := #[]
    | _, none => pure ()
    | i, some c =>
      -- `ps` ends the block
      let mut last : Option (List (Prog W)) := none
      match i with
      | .Lopn o => acc := acc ++ (← op o)
      | .Lgoto l => last := some (goto l)
      | .Lcond cnd l =>
        match cond cnd with
        | some e => acc := acc.push (when e (goto l))
        | none => last := some [wrong]
      | .Ligoto e cs =>
        let (ps, x) ← expr e
        let j := (tables.idxOf? cs).getD tables.size
        if j = tables.size then tables := tables.push cs
        last := some (ps ++ [gset lia x] ++ goto (top + j))
      | .Lext n =>
        match env.ext n stop with
        | some p => acc := acc.push p
        | none => last := some [wrong]
      | .Labort => last := some [wrong]
      | _ => throw "calls and returns are not lifted yet: a program of one function only"
      if let some ps := last then
        out := out.push (c, seq (acc.toList ++ ps))
        cur := none
  -- running off the end
  if let some c := cur then out := out.push (c, seq (acc.toList ++ [wrong]))
  return (out.toList, tables.toList)

end Lift

namespace Lift

/-- The most blocks a function holds. -/
def chunk : Nat := 8

/-- `bs` in runs of at most `n`. -/
def runs {α : Type} (n : Nat) (bs : List α) : List (List α) :=
  if bs.isEmpty ∨ n = 0 then [] else
    (List.range ((bs.length + n - 1) / n)).map fun i => (bs.drop (i * n)).take n

/-- The function of the blocks `bs`, sorted, numbered from `lo` to `hi`: it runs them until
    `lpc` names none of them. -/
def chunkFn (name : String) (lo hi : Nat) (bs : List (Nat × Prog W)) : Decl W :=
  fn name [] <| seq
    [.while (num 1) <| seq
      [when (.cmp .lower (gvar lpc) (num lo)) [.return (num 0)],
       when (.cmp .notLower (gvar lpc) (num (hi + 1))) [.return (num 0)],
       search (gvar lpc) (·.2) bs],
     .return (num 0)]

end Lift

open Lift in
/-- **Lift 2, baseline.** A program of one function, as a Pancake program whose `main` runs
    that function in the environment `env`. -/
def lift {Reg : Type} [RegText Reg] (env : Env) (regs : List Reg) (p : Lprog (Op Reg) Reg) :
    Except String (List (Decl W)) := do
  let [fd] := p | throw "lift 2 takes a program of one function for now"
  let .Llabel _ entry :: _ := fd.body | throw "the function does not start at a label"
  let ts := targets fd.body
  let top := (fd.body.foldl (fun m i => match i with | .Llabel _ l => max m (l + 1) | _ => m) 0)
  let leader (l : Nat) : Bool := l == entry || ts.contains l
  -- ending the program: `lpc` past every block, and out of the function
  let stopAt (tables : Nat) := top + tables
  let stopVar := "lstop"
  let stop : Prog W := seq [gset lpc (gvar stopVar), .return (num 0)]
  let (r, st) := (blocks env stop top leader fd.body).run.run {}
  let (bs, tables) ← r
  -- the blocks that search the candidates of the indirect jumps
  let tableBlocks := tables.zipIdx.map fun (cs, j) =>
    let keys := (cs.map fun (a, l) => (a.toNat, seq (goto l))).toArray.qsort (·.1 < ·.1)
    (top + j, search (gvar lia)
      (fun (a, p) => .ite (.cmp .equal (gvar lia) (num a)) p wrong) keys.toList)
  let all := ((bs ++ tableBlocks).toArray.qsort (·.1 < ·.1)).toList
  let chunks := (runs chunk all).zipIdx.filterMap fun (bs, j) =>
    match bs.head?, bs.getLast? with
    | some (lo, _), some (hi, _) => some (s!"c{j}", lo, hi, bs)
    | _, _ => none
  let names := (regs.map RegText.name ++ env.regs).eraseDups
  let globals := names ++ (List.range st.maxTemps).map temp ++ [lia, lpc]
  let main := fn "main" [] <| seq <|
    env.init ++
    [gset lpc (num entry),
     .while (num 1) <| seq
       [when (.cmp .equal (gvar lpc) (gvar stopVar)) [.return (num 0)],
        search (gvar lpc) (·.2)
          (chunks.map fun (name, lo, _, _) => (lo, .call (some (none, none)) name []))],
     .return (num 0)]
  let called := st.called.flatMap fun f => needs f ++ [f]
  return globals.map (fun x => Decl.decl .one x (num 0)) ++
    [Decl.decl .one stopVar (num (stopAt tables.length))] ++
    (helpers.filter (called.contains ·.1) |>.map (·.2)) ++
    (chunks.map fun (name, lo, hi, bs) => chunkFn name lo hi bs) ++ [main]

end MachineChecked.Logical
