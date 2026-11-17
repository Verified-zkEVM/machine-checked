/-
  Tools.ToLean

  `decompile --to lean`: an ELF's `--proved` lift written as Lean modules, whose terms the
  kernel checks against the lift (`docs/design/Packages.md` §2; what stays trusted is in
  `Tools/README.md`, "As Lean").

  For an ELF the tool writes, under a namespace `NS`:

  * `NS/Words.lean`: each function's words (`w0`, `w1`, …), the list of them (`words`), the
    functions they decode to (`fns`), and `check_elf_words words "PATH"`, which reads the ELF
    when the module is built and adds `words_eq_elf : words = …` with the words it finds, for
    the kernel to check; a module whose words are not the ELF's does not build;
  * `NS/F<i>.lean`, one per function: its lift as a readable term (`f<i>`), and the theorem
    `f<i>_eq : (liftProg fns)[i]? = some f<i>`;
  * `NS.lean`, which imports them all.

  The theorem of a function is checked in parts: the kernel decides that the lift's name,
  address and stack bound (`f<i>_head`) and its body in parts of `chunk` instructions
  (`f<i>_parts`, by `chunks`) are the term's, by `decide +kernel`, and
  `getElem?_eq_of_chunks` gives the whole. A whole
  body at once would go deeper than the kernel allows by default on a function of thousands of
  instructions; in parts, nothing needs a limit raised.

  The terms are data for the kernel, not code to run: the modules are `noncomputable`, since
  the code generator does not take terms this large. Long lists are written as `List.flatten`
  of short ones, and a call's candidates that are every function as `List.range`, so that the
  elaborator does not go too deep.

  ## Main definitions

  * `functions`, `wordsOf`: the functions the `--proved` lift takes, and their words
  * `chunks`, `flatten_chunks`, `getElem?_eq_of_chunks`
  * `check_elf_words`
  * `emit`
-/

import Lean
import RiscvZkvm.Interpreter
import MachineChecked.RiscV.Lift.Lift
import Tools.Elf

namespace Tools.ToLean

open Lean Elab Command Meta
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open _root_.Lprog MachineChecked.RiscV.Lift Tools.Elf

/-! ## The functions of an ELF -/

/-- The functions of an image the `--proved` lift takes, and the names of those it does not,
    each with the reason. -/
def functions (img : Elf64Image) (syms : List Sym) : Array Fn × Array String := Id.run do
  let mut fs : Array Fn := #[]
  let mut skipped : Array String := #[]
  for sym in syms do
    if sym.addr % 4 != 0 || sym.size % 4 != 0 then
      skipped := skipped.push s!"{sym.name}: not word-aligned"
    else if !img.segments.any (fun s => s.executable && s.vaddr ≤ sym.addr &&
        sym.addr + sym.size ≤ s.vaddr + s.data.size) then
      skipped := skipped.push s!"{sym.name}: not in an executable segment"
    else match wordsAt img sym.addr (sym.size / 4) with
      | .error e => skipped := skipped.push s!"{sym.name}: {e}"
      | .ok ws => match ws.mapM decode with
        | some prog => fs := fs.push { name := sym.name, base := BitVec.ofNat 64 sym.addr, prog }
        | none => skipped := skipped.push s!"{sym.name}: a word does not decode"
  return (fs, skipped)

/-- The words of each function the `--proved` lift takes: its name, its address and its
    words, in the order `functions` gives. -/
def wordsOf (bytes : ByteArray) : Except String (List (String × Nat × List Nat)) := do
  let img ← parseElf64 bytes
  let (fs, _) := functions img (← symbols bytes)
  fs.toList.mapM fun f => do
    let ws ← wordsAt img f.base.toNat f.prog.length
    pure (f.name, f.base.toNat, ws.map (·.toNat))

/-! ## A function's theorem in parts -/

section
variable {α : Type}

/-- `l` in parts of `k`, at most `n` of them. -/
def chunksAux (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | n + 1, l => if l.isEmpty then [] else l.take k :: chunksAux k n (l.drop k)

/-- `l` in parts of `k`, the last perhaps shorter. -/
def chunks (k : Nat) (l : List α) : List (List α) := chunksAux k l.length l

theorem flatten_chunksAux {k : Nat} (hk : 0 < k) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (chunksAux k n l).flatten = l
  | 0, l, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; rfl
  | n + 1, l, h => by
    unfold chunksAux
    split
    · next he => simp [List.isEmpty_iff.mp he]
    · rw [List.flatten_cons, flatten_chunksAux hk n (l.drop k) (by simp; omega)]
      exact List.take_append_drop k l

theorem flatten_chunks {k : Nat} (hk : 0 < k) (l : List α) : (chunks k l).flatten = l :=
  flatten_chunksAux hk _ l (Nat.le_refl _)

end

/-- The parts of `chunk` instructions a function's theorem is checked in. -/
def chunk : Nat := 128

/-- **A function of a program, from its parts.** If the `i`th function of `p` has `f`'s name,
    address and stack bound, and its body in parts of `chunk` is `cs`, whose concatenation is
    `f`'s body, then it is `f`. The two facts are checked apart: the instances that decide
    them are found apart, and not together. -/
theorem getElem?_eq_of_chunks {Op Reg : Type} {p : Lprog Op Reg} {i : Nat} {f : Lfundef Op Reg}
    {cs : List (Lcmd Op Reg)}
    (hh : (p[i]?).map (fun g => (g.name, g.addr, g.depth)) = some (f.name, f.addr, f.depth))
    (hc : (p[i]?).map (fun g => chunks chunk g.body) = some cs)
    (hf : f.body = cs.flatten) : p[i]? = some f := by
  cases hp : p[i]? with
  | none => simp [hp] at hh
  | some g =>
    simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hh hc
    obtain ⟨hn, ha, hd⟩ := hh
    have hb : g.body = f.body := by
      rw [hf, ← hc, flatten_chunks (by decide)]
    cases g; cases f
    simp_all

/-! ## The check against the ELF -/

/-- `xs` in groups of 128. -/
def groups {β : Type} (xs : List β) : List (List β) :=
  (List.range ((xs.length + 127) / 128)).map fun k => (xs.drop (128 * k)).take 128

/-- A list of naturals as the emitter writes it: a literal of at most 128, or `List.flatten`
    of such literals (of literals). The check builds the same term, so that the kernel compares
    the words with the ELF's by unfolding constants, not by evaluating. -/
def natListExpr (xs : List Nat) : Expr :=
  let lit (ys : List Nat) : Expr := toExpr ys
  let ty := mkConst ``Nat
  let flat (e : Expr) : Expr := mkApp2 (mkConst ``List.flatten [0]) ty e
  let listOf (es : List Expr) (t : Expr) : Expr :=
    es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) t e acc) (mkApp (mkConst ``List.nil [0]) t)
  if xs.length ≤ 128 then lit xs
  else
    let parts := (groups xs).map lit
    let lty := mkApp (mkConst ``List [0]) ty
    if parts.length ≤ 128 then flat (listOf parts lty)
    else
      let llty := mkApp (mkConst ``List [0]) lty
      flat (mkApp2 (mkConst ``List.flatten [0]) lty (listOf ((groups parts).map (listOf · lty)) llty))

/-- The words of an ELF as the term the emitter writes for `words`. -/
def wordsExpr (ws : List (String × Nat × List Nat)) : Expr :=
  let natList := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  let inner := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) natList
  let outer := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) inner
  ws.foldr (fun (n, b, xs) acc =>
      mkApp3 (mkConst ``List.cons [0]) outer
        (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) inner (toExpr n)
          (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) natList (toExpr b) (natListExpr xs)))
        acc)
    (mkApp (mkConst ``List.nil [0]) outer)

/-- `check_elf_words words "PATH"` reads the ELF at `PATH` (from where the module is built)
    and adds `words_eq_elf : words = …`, with the words of each function the `--proved` lift
    takes, for the kernel to check. It fails if the ELF cannot be read or its words are not
    `words`. -/
syntax (name := checkElfWords) "check_elf_words " ident str : command

@[command_elab checkElfWords]
def elabCheckElfWords : CommandElab := fun stx => do
  let some path := stx[2].isStrLit? | throwUnsupportedSyntax
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let bytes ← match ← (IO.FS.readBinFile path).toBaseIO with
    | .ok b => pure b
    | .error e => throwError "check_elf_words: cannot read {path}: {e}"
  let ws ← match wordsOf bytes with
    | .ok ws => pure ws
    | .error e => throwError "check_elf_words: {path}: {e}"
  let ty := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String)
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkApp (mkConst ``List [0]) (mkConst ``Nat))))
  let thm := (declName.getPrefix).str (declName.getString! ++ "_eq_elf")
  liftCoreM <| addDecl <| .thmDecl {
    name := thm, levelParams := []
    type := mkApp3 (mkConst ``Eq [1]) ty (mkConst declName) (wordsExpr ws)
    value := mkApp2 (mkConst ``Eq.refl [1]) ty (mkConst declName) }

/-! ## The emitter -/

/-- A list as a literal of at most 128, or `List.flatten` of such literals (of literals). -/
def chunked (xs : List String) : String :=
  let lit (ys : List String) : String := "[" ++ ", ".intercalate ys ++ "]"
  if xs.length ≤ 128 then lit xs
  else
    let parts := (groups xs).map lit
    if parts.length ≤ 128 then "List.flatten " ++ lit parts
    else "List.flatten (List.flatten " ++ lit ((groups parts).map lit) ++ ")"

/-- `List.range n` in place of the literal `[0, 1, …, n-1]`: the candidates of an indirect
    call are every function, and a literal of hundreds of numbers inside an instruction is too
    much for the elaborator. `reprStr` wraps long lists across lines, so literals are compared
    with their whitespace taken out. -/
partial def ranges (n : Nat) (s : String) : String :=
  let flat := "[" ++ ",".intercalate ((List.range n).map toString) ++ "]"
  match s.splitOn "[0," with
  | [] | [_] => s
  | before :: after =>
    let tail := "[0," ++ "[0,".intercalate after
    let lit := String.ofList (tail.toList.takeWhile (· != ']')) ++ "]"
    if String.ofList (lit.toList.filter fun c => !c.isWhitespace) == flat then
      before ++ s!"(List.range {n})" ++ ranges n (String.ofList (tail.toList.drop lit.length))
    else
      before ++ "[0," ++ ranges n (String.ofList (tail.toList.drop 3))

/-- Shorter names for the constructors `reprStr` prints in full; the modules open their
    namespaces. -/
def short (s : String) : String :=
  [("Lprog.LinstrR.", "LinstrR."), ("Lprog.Op.", "Op."), ("Lprog.Expr.", "Expr."),
    ("Lprog.BinOp.", "BinOp."), ("Lprog.UnOp.", "UnOp."), ("Lprog.LOperand.", "LOperand."),
    ("Lprog.Target.", "Target."), ("Lprog.Width.", "Width."), ("Lprog.LabelKind.", "LabelKind."),
    ("RiscvZkvm.Rv64.Reg.", "Reg.")].foldl (fun s (a, b) => s.replace a b) s

/-- A symbol's name as it may appear inside a comment of a module written: its string literal
    (`reprStr`, which escapes quotes and control characters), with a space put between `-` and
    `/` wherever they meet, so that it neither opens nor closes a comment. A symbol name is any
    bytes of the ELF; one that closed the comment would put what follows into the module as
    Lean. -/
def commentSafe (s : String) : String :=
  ((reprStr s).replace "-/" "- /").replace "/-" "/ -"

/-- Is `ns` a namespace `--to lean` may write: an ASCII letter in upper case, then ASCII
    letters, digits and `_`? It is a directory, a module's root and a namespace at once, so it
    has no `.` (the module would not be where its import looks), no `/` (it would be written
    outside `OUTDIR`) and is no keyword (keywords are in lower case). -/
def validNs (ns : String) : Bool :=
  match ns.toList with
  | c :: cs => ('A' ≤ c && c ≤ 'Z') && cs.all fun c => c.isAlphanum && c.toNat < 128 || c == '_'
  | [] => false

/-- The header every module written shares. -/
def header (ns what : String) (imports : List String) : String :=
  s!"/-\n  {ns}.{what}\n\n  Written by `decompile --to lean`. Do not edit: the theorems below check it.\n-/\n\n" ++
    String.join (imports.map (s!"import {·}\n")) ++
    s!"\nnamespace {ns}\n\nopen RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean\n\n" ++
    "-- data for the kernel, not code to run: the code generator does not take terms this large\n" ++
    "noncomputable section\n\n"

def footer (ns : String) : String := s!"\nend\n\nend {ns}\n"

/-- The words module. -/
def wordsModule (ns elfPath : String) (ws : List (String × Nat × List Nat)) : String := Id.run do
  let mut s := header ns "Words" ["Tools.ToLean"]
  for h : k in [0 : ws.length] do
    let (_, _, xs) := ws[k]
    s := s ++ s!"def w{k} : List Nat :=\n    {chunked (xs.map toString)}\n"
  let entries := ws.zipIdx.map fun ((n, b, _), k) => s!"({repr n}, {b}, w{k})"
  s := s ++ "\ndef words : List (String × Nat × List Nat) := [\n  " ++ ",\n  ".intercalate entries ++ "]\n\n"
  s := s ++ s!"-- the words are the ELF's: `words_eq_elf`, checked when this module is built\n"
  s := s ++ s!"check_elf_words words {repr elfPath}\n\n"
  s := s ++ "/-- The functions the words decode to. -/\n"
  s := s ++ "def fns : List Fn := words.map fun (name, base, ws) =>\n  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }\n"
  return s ++ footer ns

/-- The module of the `i`th function, lifted to `fd`. -/
def functionModule (ns : String) (n i : Nat) (fd : Lfundef (Op Reg) Reg) : String := Id.run do
  let mut s := header ns s!"F{i}" [s!"{ns}.Words"]
  let parts := chunks chunk fd.body
  for h : j in [0 : parts.length] do
    s := s ++ s!"def f{i}_{j} : Lcmd (Op Reg) Reg :=\n  {chunked (parts[j].map fun x => ranges n (short (reprStr x)))}\n\n"
  let names := (List.range parts.length).map (s!"f{i}_{·}")
  s := s ++ s!"/-- The function {commentSafe fd.name}, lifted. -/\n"
  s := s ++ s!"def f{i} : Lfundef (Op Reg) Reg :=\n  \{ name := {repr fd.name}, addr := {fd.addr.toNat}, depth := {fd.depth},\n    body := List.flatten [{", ".intercalate names}] }\n\n"
  s := s ++ s!"theorem f{i}_head : (liftProg fns)[{i}]?.map (fun g => (g.name, g.addr, g.depth)) =\n" ++
    s!"    some (f{i}.name, f{i}.addr, f{i}.depth) := by\n  decide +kernel\n\n"
  s := s ++ s!"theorem f{i}_parts : (liftProg fns)[{i}]?.map (fun g => chunks chunk g.body) =\n" ++
    s!"    some [{", ".intercalate names}] := by\n  decide +kernel\n\n"
  s := s ++ s!"/-- **`f{i}` is the lift of the ELF's words.** -/\n"
  s := s ++ s!"theorem f{i}_eq : (liftProg fns)[{i}]? = some f{i} :=\n  getElem?_eq_of_chunks f{i}_head f{i}_parts rfl\n"
  return s ++ footer ns

/-- **Write the modules** for the ELF at `elfPath` (as the modules will name it, from where
    they are built) under `outDir`, in namespace `ns`. Gives the number of functions and of
    instructions, and the names of the functions left out, each with the reason. -/
def emit (elfPath outDir ns : String) : IO (Nat × Nat × Array String) := do
  let bytes ← IO.FS.readBinFile elfPath
  let img ← IO.ofExcept (parseElf64 bytes)
  let (fs, skipped) := functions img (← IO.ofExcept (symbols bytes))
  let ws ← IO.ofExcept (wordsOf bytes)
  unless validNs ns do
    throw <| IO.userError s!"the namespace {repr ns} is not an ASCII letter in upper case followed by ASCII letters, digits and `_`"
  let dir := System.FilePath.mk outDir / ns
  -- Files of an earlier run, of an ELF with more functions, would stay beside the new ones.
  if ← dir.pathExists then
    throw <| IO.userError s!"{dir} exists: remove it, or write to another OUTDIR or NAMESPACE"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "Words.lean") (wordsModule ns elfPath ws)
  let p := liftProg fs.toList
  for h : i in [0 : p.length] do
    IO.FS.writeFile (dir / s!"F{i}.lean") (functionModule ns fs.size i p[i])
  IO.FS.writeFile (System.FilePath.mk outDir / s!"{ns}.lean")
    (s!"/-\n  {ns}\n\n  Written by `decompile --to lean`: every module of it.\n-/\n\n" ++
      String.join ((List.range p.length).map (s!"import {ns}.F{·}\n")))
  return (fs.size, (fs.toList.map (·.prog.length)).sum, skipped)

end Tools.ToLean
