/-
  Tools.ElfWords

  The words of the functions of an ELF that the `--proved` lift takes, and `check_elf_words`,
  the check of a written words module against the ELF (`Tools/ToLean.lean`, which writes the
  modules). It imports the lift and the ELF reader, not all of `Lean` as `Tools.ToLean` does,
  so that a written words module, and so every function's module, does not load the tool. The
  namespace is `Tools.ToLean`'s, of which this was part.

  ## Main definitions

  * `functions`, `wordsOf`: the functions the `--proved` lift takes (those whose words each
    decode, or are `unimp`, which it lifts as a trap), and their words
  * `check_elf_words`: the check of a written words module against the ELF
-/

import Lean.Elab.Command
import MachineChecked.RiscV.Lift.Lift
import MachineChecked.RiscV.Lift.Decode
import Tools.Elf

namespace Tools.ToLean

open Lean Elab Command Meta
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open _root_.Lprog MachineChecked.RiscV.Lift Tools.Elf

/-! ## The functions of an ELF -/

/-- `unimp` (`csrrw zero, cycle, zero`): the illegal instruction a compiler writes for a trap
    (Rust's `abort`, `unreachable!`). riscv-zkvm's decoder has no instruction for it, and the
    machine has no step there, as an illegal instruction does on hardware: the lift takes it as
    a trap. -/
def unimp : BitVec 32 := 0xc0001073#32

/-- A word the `--proved` lift takes: an instruction, or `unimp`. -/
def taken (w : BitVec 32) : Bool := (decode w).isSome || w == unimp

/-- Why a function's words are not taken, said of the first that is not: one of the 32-bit
    operations of RV64IM that riscv-zkvm's machine lacks (`Lift/Decode.lean`), which has no
    step there while hardware runs it, so that a trap there would be a false reading; or a word
    that is no instruction of RV64IM at all. -/
def undecoded (base : Nat) (ws : List (BitVec 32)) : String :=
  match (ws.zipIdx).find? (fun (w, _) => !taken w) with
  | none => "a word does not decode"
  | some (w, k) =>
    let addr := s!"0x{String.ofList (Nat.toDigits 16 (base + 4 * k))}"
    match wordOps w with
    | some (name, _) => s!"`{name}` at {addr}, a 32-bit operation riscv-zkvm's machine does not \
        run: the `--proved` lift does not take it (`--to lprog` without `--proved` does)"
    | none =>
      s!"the word 0x{String.ofList (Nat.toDigits 16 w.toNat)} at {addr} is no instruction of \
        RV64IM"

/-- The functions of an image the `--proved` lift takes, from its symbols of code
    (`symbols`), and the names of the symbols whose code it leaves out (`Symbols.lost` and the
    functions it does not take), each with the reason. -/
def functions (img : Elf64Image) (syms : Symbols) : Array Fn × Array String :=
    Id.run do
  let mut fs : Array Fn := #[]
  let mut skipped : Array String := syms.lost.toArray
  for sym in syms.fns do
    if sym.addr % 4 != 0 || sym.size % 4 != 0 then
      skipped := skipped.push s!"{sym.name}: not word-aligned"
    else if !img.segments.any (fun s => s.executable && s.vaddr ≤ sym.addr &&
        sym.addr + sym.size ≤ s.vaddr + s.data.size) then
      skipped := skipped.push s!"{sym.name}: not in an executable segment"
    else match wordsAt img sym.addr (sym.size / 4) with
      | .error e => skipped := skipped.push s!"{sym.name}: {e}"
      | .ok ws =>
        if ws.all taken then
          fs := fs.push
            { name := sym.name, base := BitVec.ofNat 64 sym.addr, prog := ws.map decode }
        else skipped := skipped.push s!"{sym.name}: {undecoded sym.addr ws}"
  return (fs, skipped)

/-- The words of each function the `--proved` lift takes: its name, its address and its
    words, in the order `functions` gives. -/
def wordsOf (bytes : ByteArray) : Except String (List (String × Nat × List Nat)) := do
  let img ← parseElf64 bytes
  let (fs, _) := functions img (← symbols bytes)
  fs.toList.mapM fun f => do
    let ws ← wordsAt img f.base.toNat f.prog.length
    pure (f.name, f.base.toNat, ws.map (·.toNat))

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
    es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) t e acc)
      (mkApp (mkConst ``List.nil [0]) t)
  if xs.length ≤ 128 then lit xs
  else
    let parts := (groups xs).map lit
    let lty := mkApp (mkConst ``List [0]) ty
    if parts.length ≤ 128 then flat (listOf parts lty)
    else
      let llty := mkApp (mkConst ``List [0]) lty
      flat (mkApp2 (mkConst ``List.flatten [0]) lty
        (listOf ((groups parts).map (listOf · lty)) llty))

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

end Tools.ToLean
