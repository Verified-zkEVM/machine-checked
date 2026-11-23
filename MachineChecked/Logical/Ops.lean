/-
  MachineChecked.Logical.Ops

  The shared operations of Lprog (`Lprog/Op.lean`) as Pancake statements.

  A register is a global variable of its name. An operation is an assignment, a load or a
  store. Pancake has `+ - * & | ^`, shifts by a constant and the comparisons; what it lacks (a
  shift by a register, the high halves of a product, division) is a call to a function
  written here in Pancake (`helpers`). Memory is Pancake's memory at the same addresses.

  ## Main definitions

  * `expr`, `op`, `cond`, `helpers`
-/

import Lprog.Text
import Pancake.Print

namespace MachineChecked.Logical

open Lprog
open Flapjack (Exp Prog Decl Shape Shift)
open Pancake (W)

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
  /-- The candidate lists of the indirect calls: list `j` is searched by the function
      `l_call{j}`. -/
  tables : Array (List Nat) := #[]
  /-- Where the program may go `wrong`, each place described. -/
  traps : Array String := #[]

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

/-- An operation. Pancake loads and stores a word, four bytes and a byte; two bytes go by
    bytes. A trap ends its block (`blocks`, in `Lift.lean`), so it is no statement of one. -/
def op : Op Reg → M (List (Prog W))
  | .skip => pure []
  -- unreachable from `blocks`, which ends the block at a trap
  | .trap => pure []
  | .set d e => do
    let (ps, x) ← expr e
    pure (ps ++ [gset (RegText.name d) x])
  | .load d w signed a => do
    let (ps, x) ← if w = .b2 then exprVar a else expr a
    let v : Exp W := match w with
      | .b8 => .load .one x
      | .b4 => .load32 x
      | .b2 => loadBytes x 2
      | .b1 => .loadByte x
    let k := 64 - w.bits
    pure (ps ++ [gset (RegText.name d) (if signed ∧ w ≠ .b8 then sar (shl v k) k else v)])
  | .store w a e => do
    let (pa, x) ← if w = .b2 then exprVar a else expr a
    let (pe, y) ← if w = .b2 then exprVar e else expr e
    pure (pa ++ pe ++ match w with
      | .b8 => [.store x y]
      | .b4 => [.store32 x y]
      | .b1 => [.storeByte x y]
      | .b2 => [.storeByte x y, .storeByte (add x (num 1)) (shr y 8)])

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

/-- The condition that holds when `c` does not. -/
def negate : Exp W → Exp W
  | .cmp .equal a b => .cmp .notEqual a b
  | .cmp .notEqual a b => .cmp .equal a b
  | .cmp .less a b => .cmp .notLess a b
  | .cmp .notLess a b => .cmp .less a b
  | .cmp .lower a b => .cmp .notLower a b
  | .cmp .notLower a b => .cmp .lower a b
  | c => .cmp .equal c (num 0)

end Lift

end MachineChecked.Logical
