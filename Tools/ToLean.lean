/-
  Tools.ToLean

  `decompile --to lean`: an ELF's lift written as Lean modules, whose terms the kernel checks
  against the lift (`docs/design/Packages.md` §2; what stays trusted is in `Tools/README.md`,
  "As Lean"). The `--proved` route is described here; the lift of whole programs and Pancake
  (`--to lean [--pancake]`) under "The other routes" below.

  For an ELF the `--proved` route writes, under a namespace `NS`:

  * `NS/Words.lean`: each function's words (`w0`, `w1`, …), the list of them (`words`), the
    functions they decode to (`fns`), and `check_elf_words words "PATH"`, which reads the ELF
    when the module is built and adds `words_eq_elf : words = …` with the words it finds, for
    the kernel to check; a module whose words are not the ELF's does not build;
  * `NS/F<i>.lean`, one per function: its lift as a readable term (`f<i>`), and the theorem
    `f<i>_eq : (liftProg fns)[i]? = some f<i>`;
  * `NS.lean`, which imports them all.

  The theorem of a function is checked in parts: the kernel checks that the lift's name,
  address and stack bound (`f<i>_head`) and its body in parts of `chunk` instructions
  (`f<i>_parts`, by `chunks`) are the term's, by `kernel_eq` (`Eq.refl`, checked by evaluation
  in the kernel alone: faster than deciding the equation, which compares every field through
  `DecidableEq`), and `getElem?_eq_of_chunks` gives the whole. A whole
  body at once would go deeper than the kernel allows by default on a function of thousands of
  instructions; in parts, nothing needs a limit raised.

  The terms are data for the kernel, not code to run: the modules are `noncomputable`, since
  the code generator does not take terms this large. Long lists are written as `List.flatten`
  of short ones, and a call's candidates that are every function as `List.range`, so that the
  elaborator does not go too deep.

  ## Main definitions

  * `functions`, `wordsOf`: the functions the `--proved` lift takes, and their words
  * `chunks`, `flatten_chunks`, `getElem?_eq_of_chunks`
  * `check_elf_words`, `check_elf_input`: the checks of a written module against the ELF
  * `kernel_eq`: an equation proved by `Eq.refl`, for the kernel to check
  * `commentSafe`, `validNs`: what may go into a written module as text
  * `emit` (`--proved`), `emitRoute` (the other routes)
-/

import Lean
import RiscvZkvm.Interpreter
import MachineChecked.RiscV.Lift.Lift
import Tools.Elf
import Tools.Program

namespace Tools.ToLean

open Lean Elab Command Meta
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open _root_.Lprog MachineChecked.RiscV.Lift Tools.Elf

/-! ## The functions of an ELF -/

/-- Why a function's words do not decode, said of the first that does not: one of the 32-bit
    operations of RV64IM that riscv-zkvm's machine lacks (`Lift/Decode.lean`), which the
    `--proved` lift cannot take since its theorems are about that machine, or a word that is no
    instruction of RV64IM at all. -/
def undecoded (base : Nat) (ws : List (BitVec 32)) : String :=
  match (ws.zipIdx).find? (fun (w, _) => (decode w).isNone) with
  | none => "a word does not decode"
  | some (w, k) =>
    let addr := s!"0x{String.ofList (Nat.toDigits 16 (base + 4 * k))}"
    match wordOps w with
    | some (name, _) => s!"`{name}` at {addr}, a 32-bit operation riscv-zkvm's machine does not \
        run: the `--proved` lift does not take it (`--to lprog` without `--proved` does)"
    | none => s!"the word 0x{String.ofList (Nat.toDigits 16 w.toNat)} at {addr} is no instruction of RV64IM"

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
        | none => skipped := skipped.push s!"{sym.name}: {undecoded sym.addr ws}"
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

/-- Is `c` a component of a namespace `--to lean` may write: an ASCII letter in upper case, then
    ASCII letters, digits and `_`? It is a directory and a namespace at once, so it has no `/`
    (it would be written outside `OUTDIR`) and is no keyword (keywords are in lower case). -/
def validComponent (c : String) : Bool :=
  match c.toList with
  | c :: cs => ('A' ≤ c && c ≤ 'Z') && cs.all fun c => c.isAlphanum && c.toNat < 128 || c == '_'
  | [] => false

/-- Is `ns` a namespace `--to lean` may write: components separated by `.`, each
    `validComponent`. It is a module's path under `OUTDIR` as well (`nsPath`), so that the
    modules written can sit inside a library whose root is `OUTDIR`: `A.B` is written as
    `OUTDIR/A/B.lean` and `OUTDIR/A/B/`. -/
def validNs (ns : String) : Bool :=
  (ns.splitOn ".").all validComponent

/-- The path under `OUTDIR` of the namespace `ns`'s directory (and, with `.lean`, its module). -/
def nsPath (outDir ns : String) : System.FilePath :=
  (ns.splitOn ".").foldl (fun (d : System.FilePath) (c : String) => d / c) (System.FilePath.mk outDir)

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
  s := s ++ s!"kernel_eq f{i}_head : (liftProg fns)[{i}]?.map (fun g => (g.name, g.addr, g.depth)) =\n" ++
    s!"    some (f{i}.name, f{i}.addr, f{i}.depth)\n\n"
  s := s ++ s!"kernel_eq f{i}_parts : (liftProg fns)[{i}]?.map (fun g => chunks chunk g.body) =\n" ++
    s!"    some [{", ".intercalate names}]\n\n"
  s := s ++ s!"/-- **`f{i}` is the lift of the ELF's words.** -/\n"
  s := s ++ s!"theorem f{i}_eq : (liftProg fns)[{i}]? = some f{i} :=\n  getElem?_eq_of_chunks f{i}_head f{i}_parts rfl\n"
  return s ++ footer ns

/-- Run `act`, which writes under `dir`, a directory it made; if it fails, remove `dir` before
    passing the error on, so that a run that fails does not leave a directory the next run
    refuses to write over. -/
def removeOnError {α : Type} (dir : System.FilePath) (act : IO α) : IO α :=
  try act catch e => do
    try IO.FS.removeDirAll dir catch _ => pure ()
    throw e

/-- **Write the modules** for the ELF at `elfPath` (as the modules will name it, from where
    they are built) under `outDir`, in namespace `ns`. Gives the number of functions and of
    instructions, and the names of the functions left out, each with the reason. -/
def emit (elfPath outDir ns : String) : IO (Nat × Nat × Array String) := do
  let bytes ← IO.FS.readBinFile elfPath
  let img ← IO.ofExcept (parseElf64 bytes)
  let (fs, skipped) := functions img (← IO.ofExcept (symbols bytes))
  let ws ← IO.ofExcept (wordsOf bytes)
  unless validNs ns do
    throw <| IO.userError s!"the namespace {repr ns} is not a namespace of components separated by `.`, each an ASCII letter in upper case followed by ASCII letters, digits and `_`"
  let dir := nsPath outDir ns
  -- Files of an earlier run, of an ELF with more functions, would stay beside the new ones.
  if ← dir.pathExists then
    throw <| IO.userError s!"{dir} exists: remove it, or write to another OUTDIR or NAMESPACE"
  IO.FS.createDirAll dir
  removeOnError dir do
    IO.FS.writeFile (dir / "Words.lean") (wordsModule ns elfPath ws)
    let p := liftProg fs.toList
    for h : i in [0 : p.length] do
      IO.FS.writeFile (dir / s!"F{i}.lean") (functionModule ns fs.size i p[i])
    -- which function is which index: a proof names a function by its index (`f<i>_eq`,
    -- the frame `⟨i, 0, ret, top⟩`)
    let table := String.join ((fs.toList.zipIdx).map fun (f, i) =>
      s!"  * `F{i}`: {commentSafe f.name}, at 0x{String.ofList (Nat.toDigits 16 f.base.toNat)}\n")
    IO.FS.writeFile (dir.addExtension "lean")
      (s!"/-\n  {ns}\n\n  Written by `decompile --to lean`: every module of it. The functions, by \
        index (`f<i>`, `f<i>_eq`):\n\n{table}-/\n\n" ++
        String.join ((List.range p.length).map (s!"import {ns}.F{·}\n")))
    return (fs.size, (fs.toList.map (·.prog.length)).sum, skipped)

/-! ## The other routes: the lift of whole programs, and Pancake

`decompile --to lean ELF OUTDIR NS` writes the program `decompile --to lprog` lifts, for
RISC-V, AArch64 or x86-64, and `--to lean --pancake` the Pancake program `--to pancake` writes:

* `NS/Code.lean`: each function's bytes and the addresses a computed jump in it may reach
  (`code`), the entry and the memory, as `Tools.Program.inputOf` reads them from the ELF, and
  `check_elf_input`, which reads the ELF when the module is built and adds `code_eq_elf`,
  `entry_eq_elf` and `memory_eq_elf` for the kernel to check; `program` is the program the
  instruction set builds from them (`Tools.Program.riscvProgram`, …), the one the tool lifted;
* `NS/F<i>.lean`: the `i`th function of `program.lift` as a term, with its theorem, as for
  `--proved`;
* with `--pancake`, `NS/Pancake.lean` instead: the declarations of `program.toPancake` as
  terms of Flapjack's syntax, and `pancake_eq : program.toPancake = .ok (decls, notes)`, by
  `kernel_eq`: one theorem for the whole program, since lift 2 is of the whole program.
-/

/-- `kernel_eq name : a = b` adds the theorem `name : a = b`, proved by `Eq.refl a` for the
    kernel to check: definitional equality, decided by evaluation where it must be, with no
    instance of `Decidable` (Flapjack's syntax has none) and no check by the elaborator first,
    which would be slower than the kernel's. -/
syntax (name := kernelEq) "kernel_eq " ident " : " term : command

@[command_elab kernelEq]
def elabKernelEq : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  let (ty, lhs) ← liftTermElabM do
    -- an error in the statement fails the command, not a theorem stated with `sorry`
    let ty ← instantiateMVars (← Term.withoutErrToSorry (Term.elabType stx[3]))
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let some (_, lhs, _) := ty.eq? | throwError "kernel_eq: {ty} is not an equation"
    if ty.hasMVar then throwError "kernel_eq: {ty} has holes"
    pure (ty, lhs)
  let some (α, _, _) := ty.eq? | throwError "kernel_eq: not an equation"
  let u ← liftTermElabM do
    let s ← inferType α
    match (← whnf s) with
    | .sort u => pure u
    | _ => throwError "kernel_eq: not a type"
  liftCoreM <| addDecl <| .thmDecl {
    name, levelParams := []
    type := ty
    value := mkApp2 (mkConst ``Eq.refl [u]) α lhs }

/-- A list of `n` naturals' term, as `natListExpr`; for the flat memory. -/
def natTy : Expr := mkConst ``Nat
def listTy (t : Expr) : Expr := mkApp (mkConst ``List [0]) t
def prodTy (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [0, 0]) a b
def pairExpr (a b : Expr) (ea eb : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) a b ea eb

/-- The code of an input as the term the emitter writes for `code`: entries
    `(name, address, bytes, targets)`, the lists of naturals as `natListExpr` writes them. -/
def codeExpr (code : List Tools.Program.Entry) : Expr :=
  let inner3 := prodTy (listTy natTy) (listTy natTy)
  let inner2 := prodTy natTy inner3
  let entry := prodTy (mkConst ``String) inner2
  code.foldr (fun (n, a, bs, ts) acc =>
      mkApp3 (mkConst ``List.cons [0]) entry
        (pairExpr (mkConst ``String) inner2 (toExpr n)
          (pairExpr natTy inner3 (toExpr a)
            (pairExpr (listTy natTy) (listTy natTy) (natListExpr bs) (natListExpr ts))))
        acc)
    (mkApp (mkConst ``List.nil [0]) entry)

/-- The memory flat: each address followed by its word. -/
def flatMemory (m : List (Nat × Nat)) : List Nat := m.flatMap fun (a, w) => [a, w]

/-- The memory from its flat form. -/
def pairsOf : List Nat → List (Nat × Nat)
  | a :: w :: rest => (a, w) :: pairsOf rest
  | _ => []

/-- The builder of an instruction set's program (`Tools.Program`). -/
def builderOf : Tools.Program.Machine → Name
  | .riscv => ``Tools.Program.riscvProgram
  | .arm => ``Tools.Program.armProgram
  | .x86 => ``Tools.Program.x86Program

/-- `check_elf_input code entry memory "PATH"` reads the ELF at `PATH` (from where the module
    is built), reads its input as `decompile` does (`Tools.Program.inputOf`), and adds
    `code_eq_elf`, `entry_eq_elf` and `memory_eq_elf`, the three constants equal to what it
    finds (the memory flat, `flatMemory`), for the kernel to check. It then defines `program`,
    beside `code`, by the builder of the ELF's own instruction set (`builderOf`): which
    instruction set the program is of is the ELF's, not the written module's. -/
syntax (name := checkElfInput) "check_elf_input " ident ppSpace ident ppSpace ident ppSpace str : command

@[command_elab checkElfInput]
def elabCheckElfInput : CommandElab := fun stx => do
  let some path := stx[4].isStrLit? | throwUnsupportedSyntax
  let names ← [stx[1], stx[2], stx[3]].mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  let bytes ← match ← (IO.FS.readBinFile path).toBaseIO with
    | .ok b => pure b
    | .error e => throwError "check_elf_input: cannot read {path}: {e}"
  let i ← match Tools.Program.inputOf bytes with
    | .ok i => pure i
    | .error e => throwError "check_elf_input: {path}: {e}"
  let codeTy := listTy (prodTy (mkConst ``String) (prodTy natTy (prodTy (listTy natTy) (listTy natTy))))
  let facts : List (Name × Expr × Expr) :=
    [(names[0]!, codeTy, codeExpr i.code), (names[1]!, natTy, toExpr i.entry),
     (names[2]!, listTy natTy, natListExpr (flatMemory i.memory))]
  for (d, ty, e) in facts do
    liftCoreM <| addDecl <| .thmDecl {
      name := d.getPrefix.str (d.getString! ++ "_eq_elf"), levelParams := []
      type := mkApp3 (mkConst ``Eq [1]) ty (mkConst d) e
      value := mkApp2 (mkConst ``Eq.refl [1]) ty (mkConst d) }
  let prog := mkIdent (`_root_ ++ names[0]!.getPrefix.str "program")
  let cmd ← `(command| def $prog:ident := $(mkIdent (builderOf i.machine)) $(mkIdent names[0]!)
    $(mkIdent names[1]!) (Tools.ToLean.pairsOf $(mkIdent names[2]!)))
  elabCommand cmd

/-- What a written module of an instruction set opens, and the namespace of its registers,
    shortened in the terms. -/
def machineInfo : Tools.Program.Machine → String × String
  | .riscv => ("RiscvZkvm.Rv64", "RiscvZkvm.Rv64.Reg.")
  | .arm => ("Lprog.ARM", "Lprog.ARM.Reg.")
  | .x86 => ("Lprog.X86", "Lprog.X86.Reg.")

/-- The header of a module of the other routes. -/
def headerOf (m : Tools.Program.Machine) (ns what : String) (imports : List String) : String :=
  let (opens, _) := machineInfo m
  s!"/-\n  {ns}.{what}\n\n  Written by `decompile --to lean`. Do not edit: the theorems below check it.\n-/\n\n" ++
    String.join (imports.map (s!"import {·}\n")) ++
    s!"\nnamespace {ns}\n\nopen Lprog {opens} Tools.Program Tools.ToLean\n\n" ++
    "-- data for the kernel, not code to run: the code generator does not take terms this large\n" ++
    "noncomputable section\n\n"

/-- The code module: the input, its check against the ELF, and the program. -/
def codeModule (ns elfPath : String) (i : Tools.Program.Input) : String := Id.run do
  let mut s := headerOf i.machine ns "Code" ["Tools.ToLean"]
  for h : k in [0 : i.code.length] do
    let (_, _, bs, ts) := i.code[k]
    s := s ++ s!"def c{k} : List Nat :=\n    {chunked (bs.map toString)}\n"
    s := s ++ s!"def t{k} : List Nat := {chunked (ts.map toString)}\n"
  let entries := i.code.zipIdx.map fun ((n, a, _, _), k) => s!"({repr n}, {a}, c{k}, t{k})"
  s := s ++ "\ndef code : List (String × Nat × List Nat × List Nat) := [\n  " ++ ",\n  ".intercalate entries ++ "]\n\n"
  s := s ++ s!"def entry : Nat := {i.entry}\n\n"
  s := s ++ s!"def memory : List Nat :=\n    {chunked ((flatMemory i.memory).map toString)}\n\n"
  s := s ++ "-- the input is the ELF's: `code_eq_elf`, `entry_eq_elf`, `memory_eq_elf`, checked when this module\n"
  s := s ++ "-- is built; and `program`, the program the input makes by the builder of the ELF's instruction\n"
  s := s ++ "-- set, as `decompile` lifts it\n"
  s := s ++ s!"check_elf_input code entry memory {repr elfPath}\n"
  return s ++ footer ns

/-- The module of the `i`th function of `program.lift`, lifted to `fd`. Its parts are checked
    by `decide +kernel`, not `kernel_eq` as the `--proved` lift's are: the kernel's unfolding of
    `program.lift` (its tree maps) to compare it with a term can take far longer than
    evaluating the decision. -/
def liftModule {Reg : Type} [Repr Reg] (m : Tools.Program.Machine) (ns : String) (n i : Nat)
    (fd : Lfundef (Op Reg) Reg) : String := Id.run do
  let (_, regNs) := machineInfo m
  let short' (x : String) : String := (short x).replace regNs "Reg."
  let mut s := headerOf m ns s!"F{i}" [s!"{ns}.Code"]
  let parts := chunks chunk fd.body
  for h : j in [0 : parts.length] do
    s := s ++ s!"def f{i}_{j} : Lcmd (Op Reg) Reg :=\n  {chunked (parts[j].map fun x => ranges n (short' (reprStr x)))}\n\n"
  let names := (List.range parts.length).map (s!"f{i}_{·}")
  s := s ++ s!"/-- The function {commentSafe fd.name}, lifted. -/\n"
  s := s ++ s!"def f{i} : Lfundef (Op Reg) Reg :=\n  \{ name := {repr fd.name}, addr := {fd.addr.toNat}, depth := {fd.depth},\n    body := List.flatten [{", ".intercalate names}] }\n\n"
  s := s ++ s!"theorem f{i}_head : program.lift[{i}]?.map (fun g => (g.name, g.addr, g.depth)) =\n" ++
    s!"    some (f{i}.name, f{i}.addr, f{i}.depth) := by\n  decide +kernel\n\n"
  s := s ++ s!"theorem f{i}_parts : program.lift[{i}]?.map (fun g => chunks chunk g.body) =\n" ++
    s!"    some [{", ".intercalate names}] := by\n  decide +kernel\n\n"
  s := s ++ s!"/-- **`f{i}` is the lift of the ELF's code.** -/\n"
  s := s ++ s!"theorem f{i}_eq : program.lift[{i}]? = some f{i} :=\n  getElem?_eq_of_chunks f{i}_head f{i}_parts rfl\n"
  return s ++ footer ns

/-- The statements of a right-nested `seq` chain: `.seq a (.seq b c)` is `[a, b, c]`. -/
def seqChain : _root_.Flapjack.Prog Pancake.W → List (_root_.Flapjack.Prog Pancake.W)
  | .seq a b => a :: seqChain b
  | p => [p]

/-- A statement as Lean, as `reprStr` writes it but with each `seq` chain written as
    `MachineChecked.Logical.Lift.seq` of its statements, the function lift 2 builds it with,
    which unfolds to the same term: a chain of thousands of statements as nested `.seq` is too
    deep for the elaborator. -/
partial def progLean (p : _root_.Flapjack.Prog Pancake.W) : String :=
  let r {β : Type} [Repr β] (x : β) : String := "(" ++ reprStr x ++ ")"
  match p with
  | .seq .. =>
    "(MachineChecked.Logical.Lift.seq (" ++ chunked ((seqChain p).map progLean) ++ "))"
  | .dec n sh v b => s!"(Flapjack.Prog.dec {repr n} {r sh} {r v} {progLean b})"
  | .ite c t e => s!"(Flapjack.Prog.ite {r c} {progLean t} {progLean e})"
  | .while c b => s!"(Flapjack.Prog.while {r c} {progLean b})"
  | .decCall n sh f args b => s!"(Flapjack.Prog.decCall {repr n} {r sh} {repr f} {r args} {progLean b})"
  | .call (some (ret, some (e, v, h))) f args =>
    s!"(Flapjack.Prog.call (some ({r ret}, some ({repr e}, {repr v}, {progLean h}))) {repr f} {r args})"
  | p => r p

/-- A declaration as Lean, its body by `progLean`. -/
def declLean (d : _root_.Flapjack.Decl Pancake.W) : String :=
  match d with
  | .function fd =>
    s!"(Flapjack.Decl.function \{ name := {repr fd.name}, inline := {fd.inline}, exported := {fd.exported}, " ++
      s!"params := ({reprStr fd.params}), body := {progLean fd.body}, returnShape := ({reprStr fd.returnShape}) })"
  | d => "(" ++ reprStr d ++ ")"

/-- The Pancake module: the program's declarations, and the one theorem. -/
def pancakeModule (m : Tools.Program.Machine) (ns : String)
    (decls : List (_root_.Flapjack.Decl Pancake.W)) (notes : List String) : String := Id.run do
  let mut s := headerOf m ns "Pancake" [s!"{ns}.Code"]
  for h : k in [0 : decls.length] do
    s := s ++ s!"def d{k} : _root_.Flapjack.Decl Pancake.W :=\n  {declLean decls[k]}\n\n"
  s := s ++ s!"def decls : List (_root_.Flapjack.Decl Pancake.W) :=\n  {chunked ((List.range decls.length).map (s!"d{·}"))}\n\n"
  s := s ++ s!"def notes : List String :=\n  {chunked (notes.map reprStr)}\n\n"
  s := s ++ "-- the Pancake program is lift 2 of the ELF's code\n"
  s := s ++ "kernel_eq pancake_eq : program.toPancake = .ok (decls, notes)\n"
  return s ++ footer ns

/-- **Write the modules of the other routes** for the ELF at `elfPath` under `outDir`, in
    namespace `ns`: the Lprog program, or with `pancake` the Pancake program. Gives the number
    of functions and the names of those left out, each with the reason. -/
def emitRoute (elfPath outDir ns : String) (pancake : Bool) : IO (Nat × Array String) := do
  let bytes ← IO.FS.readBinFile elfPath
  let i ← IO.ofExcept (Tools.Program.inputOf bytes)
  unless validNs ns do
    throw <| IO.userError s!"the namespace {repr ns} is not a namespace of components separated by `.`, each an ASCII letter in upper case followed by ASCII letters, digits and `_`"
  let dir := nsPath outDir ns
  if ← dir.pathExists then
    throw <| IO.userError s!"{dir} exists: remove it, or write to another OUTDIR or NAMESPACE"
  IO.FS.createDirAll dir
  removeOnError dir do
    IO.FS.writeFile (dir / "Code.lean") (codeModule ns elfPath i)
    let mods ← if pancake then do
        let r : Except String _ := match i.machine with
          | .riscv => (Tools.Program.riscvProgram i.code i.entry i.memory).toPancake
          | .arm => (Tools.Program.armProgram i.code i.entry i.memory).toPancake
          | .x86 => (Tools.Program.x86Program i.code i.entry i.memory).toPancake
        let (decls, notes) ← IO.ofExcept r
        IO.FS.writeFile (dir / "Pancake.lean") (pancakeModule i.machine ns decls notes)
        pure ["Pancake"]
      else do
        let write {Reg : Type} [Repr Reg] (p : Lprog.Lprog (Op Reg) Reg) : IO (List String) := do
          for h : k in [0 : p.length] do
            IO.FS.writeFile (dir / s!"F{k}.lean") (liftModule i.machine ns i.code.length k p[k])
          pure ((List.range p.length).map (s!"F{·}"))
        match i.machine with
        | .riscv => write (Tools.Program.riscvProgram i.code i.entry i.memory).lift
        | .arm => write (Tools.Program.armProgram i.code i.entry i.memory).lift
        | .x86 => write (Tools.Program.x86Program i.code i.entry i.memory).lift
    IO.FS.writeFile (dir.addExtension "lean")
      (s!"/-\n  {ns}\n\n  Written by `decompile --to lean`: every module of it.\n-/\n\n" ++
        String.join (mods.map (s!"import {ns}.{·}\n")))
    return (i.code.length, i.skipped)

end Tools.ToLean
