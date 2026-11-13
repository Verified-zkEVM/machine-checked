/-
  MachineChecked.Lprog.Text

  A text format for Lprog programs over the shared operations, with a printer and a parser
  that round-trip.

  A program is a list of tokens (`Tok`): symbols, numbers and register names. Every
  construct is a head symbol followed by its parts, and a list is its length followed by its
  elements, so no brackets are needed and the parser never looks ahead:

      lprog 1
      fn memcmp 0x201000 0 5
        label 0
          set %x5 add %x10 8
          if cmp eq %x5 %x0 0
          ret

  `print` gives the tokens of a program and `parse` reads them back: `parse_print`. An
  instruction set names its registers (`RegText`).

  As text (`toText`), tokens are separated by white space, a number is decimal or `0x`
  hexadecimal, a register is `%` and its name, and `#` starts a comment. `ofText` reads text
  back. That `ofText (toText p) = some p` is not proved: it holds when no symbol of the
  program (a function's name, a condition's comparison) is empty, has white space or `#` in
  it, or reads as a number or a register. A tool that writes text checks it on what it wrote.

  ## Main definitions

  * `Tok`, `RegText`, `print`, `parse`, `toText`, `ofText`

  ## Main results

  * `parse_print`: `parse (print p) = some p`
-/

import MachineChecked.Lprog.Op

namespace MachineChecked.Lprog

/-- A token. -/
inductive Tok where
  | sym (s : String)
  | num (n : Nat)
  /-- A register, by name. -/
  | reg (name : String)
  deriving DecidableEq, Repr

/-- Registers with names. -/
class RegText (Reg : Type) where
  name : Reg → String
  ofName : String → Option Reg
  ofName_name : ∀ r, ofName (name r) = some r

namespace Text

/-! ## Names -/

def widths : List Width := [.b1, .b2, .b4, .b8]

def widthName : Width → String
  | .b1 => "b1"
  | .b2 => "b2"
  | .b4 => "b4"
  | .b8 => "b8"

def widthOf (s : String) : Option Width := widths.find? (widthName · == s)

theorem widthOf_name (w : Width) : widthOf (widthName w) = some w := by
  cases w <;> simp [widthOf, widths, widthName]

def unOps : List UnOp :=
  [.sext .b1, .sext .b2, .sext .b4, .sext .b8, .zext .b1, .zext .b2, .zext .b4, .zext .b8, .not, .neg]

def unOpName : UnOp → String
  | .sext .b1 => "sext8"
  | .sext .b2 => "sext16"
  | .sext .b4 => "sext32"
  | .sext .b8 => "sext64"
  | .zext .b1 => "zext8"
  | .zext .b2 => "zext16"
  | .zext .b4 => "zext32"
  | .zext .b8 => "zext64"
  | .not => "not"
  | .neg => "neg"

def unOpOf (s : String) : Option UnOp := unOps.find? (unOpName · == s)

theorem unOpOf_name (op : UnOp) : unOpOf (unOpName op) = some op := by
  rcases op with w | w | _ | _ <;> (try cases w) <;> simp [unOpOf, unOps, unOpName]

def binOps : List BinOp :=
  [.add, .sub, .mul, .and, .or, .xor, .shl, .lshr, .ashr, .slt, .ult, .mulh, .mulhsu, .mulhu,
    .div, .divu, .rem, .remu]

def binOpName : BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .shl => "shl"
  | .lshr => "lshr"
  | .ashr => "ashr"
  | .slt => "slt"
  | .ult => "ult"
  | .mulh => "mulh"
  | .mulhsu => "mulhsu"
  | .mulhu => "mulhu"
  | .div => "div"
  | .divu => "divu"
  | .rem => "rem"
  | .remu => "remu"

def binOpOf (s : String) : Option BinOp := binOps.find? (binOpName · == s)

theorem binOpOf_name (op : BinOp) : binOpOf (binOpName op) = some op := by
  cases op <;> simp [binOpOf, binOps, binOpName]

/-- No binary operation has the name of a unary one. -/
theorem unOpOf_binOpName (op : BinOp) : unOpOf (binOpName op) = none := by
  cases op <;> simp [unOpOf, unOps, unOpName, binOpName]

/-! ## Lists -/

variable {α : Type}

/-- A list: its length, then its elements. -/
def printList (f : α → List Tok) (l : List α) : List Tok := .num l.length :: l.flatMap f

/-- `n` elements. -/
def parseN (p : List Tok → Option (α × List Tok)) : Nat → List Tok → Option (List α × List Tok)
  | 0, ts => some ([], ts)
  | n + 1, ts => match p ts with
    | some (a, ts) => match parseN p n ts with
      | some (as, ts) => some (a :: as, ts)
      | none => none
    | none => none

def parseList (p : List Tok → Option (α × List Tok)) : List Tok → Option (List α × List Tok)
  | .num n :: ts => parseN p n ts
  | _ => none

/-- A list is read back if each element is, given that it is no longer than `n` tokens. -/
theorem parseN_print {f : α → List Tok} {p : List Tok → Option (α × List Tok)} {n : Nat} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length ≤ n → ∀ ts, p (f a ++ ts) = some (a, ts)) →
      (l.flatMap f).length ≤ n → ∀ ts, parseN p l.length (l.flatMap f ++ ts) = some (l, ts)
  | [], _, _, ts => rfl
  | a :: l, h, hn, ts => by
    simp only [List.flatMap_cons, List.length_append] at hn
    simp [parseN, h a (by simp) (by omega),
      parseN_print l (fun b hb => h b (by simp [hb])) (by omega)]

theorem parseList_print {f : α → List Tok} {p : List Tok → Option (α × List Tok)} {n : Nat}
    (l : List α) (h : ∀ a ∈ l, (f a).length ≤ n → ∀ ts, p (f a ++ ts) = some (a, ts))
    (hn : (printList f l).length ≤ n) (ts : List Tok) :
    parseList p (printList f l ++ ts) = some (l, ts) := by
  simp only [printList, List.length_cons] at hn
  simp [parseList, printList, parseN_print l h (by omega)]

def printNat (n : Nat) : List Tok := [.num n]

def parseNat : List Tok → Option (Nat × List Tok)
  | .num n :: ts => some (n, ts)
  | _ => none

theorem parseNat_print (n : Nat) (ts : List Tok) : parseNat (printNat n ++ ts) = some (n, ts) := rfl

variable {Reg : Type} [RegText Reg]

/-! ## Expressions -/

def printExpr : Expr Reg → List Tok
  | .reg r => [.reg (RegText.name r)]
  | .imm v => [.num v.toNat]
  | .un op e => .sym (unOpName op) :: printExpr e
  | .bin op a b => .sym (binOpName op) :: (printExpr a ++ printExpr b)

/-- An expression of at most `n` tokens. The bound is what the recursion is on: a parser is
    given the number of tokens it reads from, once (`parse`). -/
def parseExprN : Nat → List Tok → Option (Expr Reg × List Tok)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .reg s :: ts => match RegText.ofName s with
    | some r => some (.reg r, ts)
    | none => none
  | _ + 1, .num v :: ts => some (.imm (BitVec.ofNat 64 v), ts)
  | n + 1, .sym s :: ts => match unOpOf s with
    | some op => match parseExprN n ts with
      | some (e, ts) => some (.un op e, ts)
      | none => none
    | none => match binOpOf s with
      | some op => match parseExprN n ts with
        | some (a, ts) => match parseExprN n ts with
          | some (b, ts) => some (.bin op a b, ts)
          | none => none
        | none => none
      | none => none

theorem parseExprN_print : ∀ (e : Expr Reg) (n : Nat) (ts : List Tok), (printExpr e).length ≤ n →
    parseExprN n (printExpr e ++ ts) = some (e, ts)
  | .reg r, n + 1, ts, _ => by simp [printExpr, parseExprN, RegText.ofName_name]
  | .imm v, n + 1, ts, _ => by simp [printExpr, parseExprN]
  | .un op e, n + 1, ts, h => by
    simp only [printExpr, List.length_cons] at h
    simp [printExpr, parseExprN, unOpOf_name, parseExprN_print e n ts (by omega)]
  | .bin op a b, n + 1, ts, h => by
    simp only [printExpr, List.length_cons, List.length_append] at h
    simp [printExpr, parseExprN, unOpOf_binOpName, binOpOf_name,
      parseExprN_print a n (printExpr b ++ ts) (by omega), parseExprN_print b n ts (by omega)]
  | .reg _, 0, _, h | .imm _, 0, _, h | .un .., 0, _, h | .bin .., 0, _, h => by
    simp [printExpr] at h

/-! ## Operands -/

def printInt : Int → List Tok
  | .ofNat n => [.num n]
  | .negSucc n => [.sym "-", .num (n + 1)]

def printOperand : LOperand Reg → List Tok
  | .reg r => [.reg (RegText.name r)]
  | .imm v => printInt v
  | .cmp op a b => .sym "cmp" :: .sym op :: (printOperand a ++ printOperand b)

/-- An operand of at most `n` tokens. -/
def parseOperandN : Nat → List Tok → Option (LOperand Reg × List Tok)
  | 0, _ => none
  | _ + 1, .reg s :: ts => match RegText.ofName s with
    | some r => some (.reg r, ts)
    | none => none
  | _ + 1, .num v :: ts => some (.imm (.ofNat v), ts)
  | n + 1, .sym s :: ts =>
    if s = "-" then match ts with
      | .num (v + 1) :: ts => some (.imm (.negSucc v), ts)
      | _ => none
    else if s = "cmp" then match ts with
      | .sym op :: ts => match parseOperandN n ts with
        | some (a, ts) => match parseOperandN n ts with
          | some (b, ts) => some (.cmp op a b, ts)
          | none => none
        | none => none
      | _ => none
    else none
  | _ + 1, [] => none

theorem parseOperandN_print : ∀ (c : LOperand Reg) (n : Nat) (ts : List Tok),
    (printOperand c).length ≤ n → parseOperandN n (printOperand c ++ ts) = some (c, ts)
  | .reg r, n + 1, ts, _ => by simp [printOperand, parseOperandN, RegText.ofName_name]
  | .imm (.ofNat v), n + 1, ts, _ => by simp [printOperand, printInt, parseOperandN]
  | .imm (.negSucc v), n + 1, ts, _ => by simp [printOperand, printInt, parseOperandN]
  | .cmp op a b, n + 1, ts, h => by
    simp only [printOperand, List.length_cons, List.length_append] at h
    simp [printOperand, parseOperandN,
      parseOperandN_print a n (printOperand b ++ ts) (by omega),
      parseOperandN_print b n ts (by omega)]
  | .reg _, 0, _, h | .cmp .., 0, _, h => by simp [printOperand] at h
  | .imm (.ofNat _), 0, _, h | .imm (.negSucc _), 0, _, h => by simp [printOperand, printInt] at h

/-! ## Targets -/

def printTarget : Target Reg → List Tok
  | .direct f => [.sym "fn", .num f]
  | .indirect e cands => .sym "via" :: (printExpr e ++ printList printNat cands)

def parseTarget (n : Nat) : List Tok → Option (Target Reg × List Tok)
  | .sym s :: ts =>
    if s = "fn" then match ts with
      | .num f :: ts => some (.direct f, ts)
      | _ => none
    else if s = "via" then match parseExprN n ts with
      | some (e, ts) => match parseList parseNat ts with
        | some (cands, ts) => some (.indirect e cands, ts)
        | none => none
      | none => none
    else none
  | _ => none

theorem parseTarget_print (t : Target Reg) (n : Nat) (ts : List Tok)
    (h : (printTarget t).length ≤ n) : parseTarget n (printTarget t ++ ts) = some (t, ts) := by
  cases t with
  | direct f => simp [printTarget, parseTarget]
  | indirect e cands =>
    simp only [printTarget, List.length_cons, List.length_append] at h
    simp [printTarget, parseTarget, fun ts => parseExprN_print e n ts (by omega),
      parseList_print (f := printNat) (n := n) cands (fun a _ _ ts => parseNat_print a ts) (by omega)]

/-! ## Instructions -/

/-- A candidate of an indirect jump: the value, then the label. -/
def printCand (c : BitVec 64 × LLabel) : List Tok := [.num c.1.toNat, .num c.2]

def parseCand : List Tok → Option ((BitVec 64 × LLabel) × List Tok)
  | .num v :: .num l :: ts => some ((BitVec.ofNat 64 v, l), ts)
  | _ => none

theorem parseCand_print (c : BitVec 64 × LLabel) (ts : List Tok) :
    parseCand (printCand c ++ ts) = some (c, ts) := by
  simp [printCand, parseCand]

def printOp : Op Reg → List Tok
  | .set d e => .sym "set" :: .reg (RegText.name d) :: printExpr e
  | .load d w s a =>
    .sym "load" :: .reg (RegText.name d) :: .sym (widthName w) :: .sym (if s then "s" else "u") ::
      printExpr a
  | .store w a e => .sym "store" :: .sym (widthName w) :: (printExpr a ++ printExpr e)
  | .skip => [.sym "skip"]

def printInstr : LinstrR (Op Reg) Reg → List Tok
  | .Lopn op => printOp op
  | .Llabel .internal l => [.sym "label", .num l]
  | .Llabel .external l => [.sym "elabel", .num l]
  | .Lgoto l => [.sym "goto", .num l]
  | .Lcond c l => .sym "if" :: (printOperand c ++ [.num l])
  | .Ligoto e cands => .sym "igoto" :: (printExpr e ++ printList printCand cands)
  | .Lcall ret t => .sym "call" :: .num ret.toNat :: printTarget t
  | .Ltail t => .sym "tail" :: printTarget t
  | .Lret => [.sym "ret"]
  | .Lext => [.sym "ext"]
  | .Labort => [.sym "abort"]

def parseSet (n : Nat) : List Tok → Option (LinstrR (Op Reg) Reg × List Tok)
  | .reg d :: ts => match RegText.ofName d, parseExprN n ts with
    | some d, some (e, ts) => some (.Lopn (.set d e), ts)
    | _, _ => none
  | _ => none

def parseLoad (n : Nat) : List Tok → Option (LinstrR (Op Reg) Reg × List Tok)
  | .reg d :: .sym w :: .sym s :: ts =>
    match RegText.ofName d, widthOf w, parseExprN n ts with
    | some d, some w, some (a, ts) =>
      if s = "s" then some (.Lopn (.load d w true a), ts)
      else if s = "u" then some (.Lopn (.load d w false a), ts)
      else none
    | _, _, _ => none
  | _ => none

def parseStore (n : Nat) : List Tok → Option (LinstrR (Op Reg) Reg × List Tok)
  | .sym w :: ts => match widthOf w, parseExprN n ts with
    | some w, some (a, ts) => match parseExprN n ts with
      | some (e, ts) => some (.Lopn (.store w a e), ts)
      | none => none
    | _, _ => none
  | _ => none

/-- An instruction of at most `n` tokens. -/
def parseInstr (n : Nat) : List Tok → Option (LinstrR (Op Reg) Reg × List Tok)
  | .sym s :: ts =>
    if s = "set" then parseSet n ts
    else if s = "load" then parseLoad n ts
    else if s = "store" then parseStore n ts
    else if s = "skip" then some (.Lopn .skip, ts)
    else if s = "label" then match ts with
      | .num l :: ts => some (.Llabel .internal l, ts)
      | _ => none
    else if s = "elabel" then match ts with
      | .num l :: ts => some (.Llabel .external l, ts)
      | _ => none
    else if s = "goto" then match ts with
      | .num l :: ts => some (.Lgoto l, ts)
      | _ => none
    else if s = "if" then match parseOperandN n ts with
      | some (c, .num l :: ts) => some (.Lcond c l, ts)
      | _ => none
    else if s = "igoto" then match parseExprN n ts with
      | some (e, ts) => match parseList parseCand ts with
        | some (cands, ts) => some (.Ligoto e cands, ts)
        | none => none
      | none => none
    else if s = "call" then match ts with
      | .num ret :: ts => match parseTarget n ts with
        | some (t, ts) => some (.Lcall (BitVec.ofNat 64 ret) t, ts)
        | none => none
      | _ => none
    else if s = "tail" then match parseTarget n ts with
      | some (t, ts) => some (.Ltail t, ts)
      | none => none
    else if s = "ret" then some (.Lret, ts)
    else if s = "ext" then some (.Lext, ts)
    else if s = "abort" then some (.Labort, ts)
    else none
  | _ => none

theorem parseInstr_print (i : LinstrR (Op Reg) Reg) (n : Nat) (ts : List Tok)
    (h : (printInstr i).length ≤ n) : parseInstr n (printInstr i ++ ts) = some (i, ts) := by
  cases i with
  | Lopn op =>
    cases op with
    | set d e =>
      simp only [printInstr, printOp, List.length_cons] at h
      simp [printInstr, printOp, parseInstr, parseSet, RegText.ofName_name,
        fun ts => parseExprN_print e n ts (by omega)]
    | load d w s a =>
      simp only [printInstr, printOp, List.length_cons] at h
      cases s <;>
        simp [printInstr, printOp, parseInstr, parseLoad, RegText.ofName_name, widthOf_name,
          fun ts => parseExprN_print a n ts (by omega)]
    | store w a e =>
      simp only [printInstr, printOp, List.length_cons, List.length_append] at h
      simp [printInstr, printOp, parseInstr, parseStore, widthOf_name,
        fun ts => parseExprN_print a n ts (by omega), fun ts => parseExprN_print e n ts (by omega)]
    | skip => simp [printInstr, printOp, parseInstr]
  | Llabel kind l => cases kind <;> simp [printInstr, parseInstr]
  | Lgoto l => simp [printInstr, parseInstr]
  | Lcond c l =>
    simp only [printInstr, List.length_cons, List.length_append] at h
    simp [printInstr, parseInstr, fun ts => parseOperandN_print c n ts (by omega)]
  | Ligoto e cands =>
    simp only [printInstr, List.length_cons, List.length_append] at h
    simp [printInstr, parseInstr, fun ts => parseExprN_print e n ts (by omega),
      parseList_print (f := printCand) (n := n) cands (fun a _ _ ts => parseCand_print a ts)
        (by omega)]
  | Lcall ret t =>
    simp only [printInstr, List.length_cons] at h
    simp [printInstr, parseInstr, fun ts => parseTarget_print t n ts (by omega)]
  | Ltail t =>
    simp only [printInstr, List.length_cons] at h
    simp [printInstr, parseInstr, fun ts => parseTarget_print t n ts (by omega)]
  | Lret => simp [printInstr, parseInstr]
  | Lext => simp [printInstr, parseInstr]
  | Labort => simp [printInstr, parseInstr]

/-! ## Functions and programs -/

def printFn (fd : Lfundef (Op Reg) Reg) : List Tok :=
  .sym "fn" :: .sym fd.name :: .num fd.addr.toNat :: .num fd.depth :: printList printInstr fd.body

/-- A function of at most `n` tokens. -/
def parseFn (n : Nat) : List Tok → Option (Lfundef (Op Reg) Reg × List Tok)
  | .sym s :: .sym name :: .num addr :: .num depth :: ts =>
    if s = "fn" then match parseList (parseInstr n) ts with
      | some (body, ts) => some (⟨name, BitVec.ofNat 64 addr, body, depth⟩, ts)
      | none => none
    else none
  | _ => none

theorem parseFn_print (fd : Lfundef (Op Reg) Reg) (n : Nat) (ts : List Tok)
    (h : (printFn fd).length ≤ n) : parseFn n (printFn fd ++ ts) = some (fd, ts) := by
  simp only [printFn, List.length_cons] at h
  simp [printFn, parseFn,
    parseList_print (n := n) fd.body (fun i _ hi ts => parseInstr_print i n ts hi) (by omega)]

end Text

variable {Reg : Type} [RegText Reg]

/-- The tokens of a program. -/
def print (p : Lprog (Op Reg) Reg) : List Tok := .sym "lprog" :: Text.printList Text.printFn p

/-- The program some tokens are, if they are one and nothing follows it. -/
def parse : List Tok → Option (Lprog (Op Reg) Reg)
  | .sym s :: ts =>
    if s = "lprog" then match Text.parseList (Text.parseFn ts.length) ts with
      | some (p, []) => some p
      | _ => none
    else none
  | _ => none

/-- **The parser reads what the printer writes.** -/
theorem parse_print (p : Lprog (Op Reg) Reg) : parse (print p) = some p := by
  have h := Text.parseList_print (f := Text.printFn) p
    (fun fd _ hn ts => Text.parseFn_print fd _ ts hn) (Nat.le_refl _) []
  rw [List.append_nil] at h
  simp [parse, print, h]

/-! ## Text -/

/-- A token as text: a number at least `4096` in hexadecimal, a register after `%`. -/
def Tok.text : Tok → String
  | .sym s => s
  | .num n => if n < 4096 then toString n else "0x" ++ String.ofList (Nat.toDigits 16 n)
  | .reg s => "%" ++ s

/-- Tokens on one line. -/
def Text.line (ts : List Tok) : String := " ".intercalate (ts.map Tok.text)

/-- **A program as text**: the tokens of `print`, a function to a paragraph and an instruction
    to a line. -/
def toText (p : Lprog (Op Reg) Reg) : String :=
  let instr (i : LinstrR (Op Reg) Reg) : String :=
    (match i with | .Llabel .. => "  " | _ => "    ") ++ Text.line (Text.printInstr i) ++ "\n"
  let fn (fd : Lfundef (Op Reg) Reg) : String :=
    "\n" ++ Text.line [.sym "fn", .sym fd.name, .num fd.addr.toNat, .num fd.depth, .num fd.body.length] ++
      "\n" ++ String.join (fd.body.map instr)
  Text.line [.sym "lprog", .num p.length] ++ "\n" ++ String.join (p.map fn)

/-- The token a word is: a register after `%`, a decimal or `0x` hexadecimal number, or a
    symbol. -/
def Text.word (cs : List Char) : Tok :=
  let digit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else none
  let number (base : Nat) (ds : List Char) : Option Nat :=
    if ds.isEmpty then none
    else ds.foldlM (fun v c => (digit c).bind fun d => if d < base then some (base * v + d) else none) 0
  match cs with
  | '%' :: cs => .reg (String.ofList cs)
  | _ =>
    match (match cs with | '0' :: 'x' :: hs => number 16 hs | _ => number 10 cs) with
    | some n => .num n
    | none => .sym (String.ofList cs)

/-- The tokens of a text: its words, without what follows a `#` on a line. -/
def lex (s : String) : List Tok := Id.run do
  let mut out : Array Tok := #[]
  let mut w : Array Char := #[]
  let mut comment := false
  for c in s.toList do
    if comment then
      if c = '\n' then comment := false
    else if c = '#' || c.isWhitespace then
      if !w.isEmpty then
        out := out.push (Text.word w.toList)
        w := #[]
      if c = '#' then comment := true
    else w := w.push c
  if !w.isEmpty then out := out.push (Text.word w.toList)
  return out.toList

/-- **The program a text is.** -/
def ofText (s : String) : Option (Lprog (Op Reg) Reg) := parse (lex s)

end MachineChecked.Lprog
