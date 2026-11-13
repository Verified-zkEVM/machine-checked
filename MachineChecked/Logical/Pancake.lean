/-
  MachineChecked.Logical.Pancake

  Pancake programs as text.

  Pancake is the language of layer 1 here, and its syntax is Flapjack's
  (`Flapjack.Pancake.PanLang`): a program is a list of `Flapjack.Decl (BitVec 64)`. Flapjack
  has a parser and no printer, so this is the printer: `print` gives the source text Flapjack
  reads back. Expressions are printed with every bracket, so no precedence is relied on.

  It prints what lift 2 writes (`Logical/Lift.lean`) and the rest of the language without
  structures: words, the three loads and stores, the operators, calls, FFI calls and control
  flow. A program with structures, exceptions or shared-memory operations is not printed
  (`none`).

  Nothing is proved of it. `decompile` (`Tools/README.md`) is checked by compiling what it
  prints with Flapjack and running it.

  ## Main definitions

  * `Pancake.print`
-/

import Flapjack.Pancake.PanLang

namespace MachineChecked.Logical.Pancake

open Flapjack (Exp Prog Decl FunDecl Shape VarKind Shift)

/-- A word: the value type of Pancake at 64 bits. -/
abbrev W := BitVec 64

def shape : Shape → Option String
  | .one => some "1"
  | _ => none

def binOp : Flapjack.BinOp → String
  | .add => "+"
  | .sub => "-"
  | .and => "&"
  | .or => "|"
  | .xor => "^"

/-- A comparison; signed ones are `less`, unsigned `lower`. The bit tests have no syntax. -/
def cmp : Flapjack.Cmp → Option String
  | .equal => some "=="
  | .notEqual => some "!="
  | .less => some "<"
  | .notLess => some ">="
  | .lower => some "<+"
  | .notLower => some ">=+"
  | .test | .notTest => none

def shift : Shift → String
  | .lsl => "<<"
  | .lsr => ">>>"
  | .asr => ">>"
  | .ror => "#>>"

mutual

/-- An expression, in brackets unless it is a name or a number. -/
def exp : Exp W → Option String
  | .const v => some (toString v.toInt)
  | .var _ x => some x
  | .load s a => do some s!"(lds {← shape s} {← exp a})"
  | .load32 a => do some s!"(ld32 {← exp a})"
  | .loadByte a => do some s!"(ld8 {← exp a})"
  | .op o (a :: as) => do infixes (binOp o) (← exp a) as
  | .panOp .mul (a :: as) => do infixes "*" (← exp a) as
  | .cmp o a b => do some s!"({← exp a} {← cmp o} {← exp b})"
  | .shift o a (.const n) => do some s!"({← exp a} {shift o} {n.toNat})"
  | .baseAddr => some "@base"
  | .bytesInWord => some "@biw"
  | _ => none

/-- `acc o a₁ o a₂ …`, bracketed to the left. -/
def infixes (o : String) (acc : String) : List (Exp W) → Option String
  | [] => some acc
  | a :: as => do infixes o s!"({acc} {o} {← exp a})" as

end

def args (es : List (Exp W)) : Option String := do
  some (", ".intercalate (← es.mapM exp))

/-- A statement, each line indented by `ind`. A declaration's scope is the rest of its
    block, so its body is printed after it at the same depth. -/
def prog (ind : String) : Prog W → Option String
  | .skip => some s!"{ind}skip;\n"
  | .dec x s e body => do some (s!"{ind}var {← shape s} {x} = {← exp e};\n" ++ (← prog ind body))
  | .assign _ x e => do some s!"{ind}{x} = {← exp e};\n"
  | .store a v => do some s!"{ind}st {← exp a}, {← exp v};\n"
  | .store32 a v => do some s!"{ind}st32 {← exp a}, {← exp v};\n"
  | .storeByte a v => do some s!"{ind}st8 {← exp a}, {← exp v};\n"
  | .seq p q => do some ((← prog ind p) ++ (← prog ind q))
  | .ite c t .skip => do some s!"{ind}if {← exp c} \{\n{← prog (ind ++ "  ") t}{ind}}\n"
  | .ite c t e => do
    some s!"{ind}if {← exp c} \{\n{← prog (ind ++ "  ") t}{ind}} else \{\n{← prog (ind ++ "  ") e}{ind}}\n"
  | .while c body => do some s!"{ind}while {← exp c} \{\n{← prog (ind ++ "  ") body}{ind}}\n"
  | .break => some s!"{ind}break;\n"
  | .continue => some s!"{ind}continue;\n"
  | .call none f as => do some s!"{ind}return {f}({← args as});\n"
  | .call (some (none, none)) f as => do some s!"{ind}{f}({← args as});\n"
  | .call (some (some (_, x), none)) f as => do some s!"{ind}{x} = {f}({← args as});\n"
  | .decCall x s f as body => do
    some (s!"{ind}var {← shape s} {x} = {f}({← args as});\n" ++ (← prog ind body))
  | .extCall f a b c d => do some s!"{ind}@{f}({← exp a}, {← exp b}, {← exp c}, {← exp d});\n"
  | .return e => do some s!"{ind}return {← exp e};\n"
  | .tick => some s!"{ind}tick;\n"
  | _ => none

def decl : Decl W → Option String
  | .function fd => do
    let ps ← fd.params.mapM fun (x, s) => do some s!"{← shape s} {x}"
    some (s!"{if fd.inline then "inline " else ""}{if fd.exported then "export " else ""}" ++
      s!"fun {← shape fd.returnShape} {fd.name}({", ".intercalate ps}) \{\n{← prog "  " fd.body}}\n")
  | .decl s x e => do some s!"var {← shape s} {x} = {← exp e};\n"
  | _ => none

/-- **A Pancake program as source text**, or `none` if it uses what is not printed. -/
def print (ds : List (Decl W)) : Option String := do
  some ("\n".intercalate (← ds.mapM decl))

end MachineChecked.Logical.Pancake
