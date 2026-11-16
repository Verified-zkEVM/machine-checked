/-
  Tools.Decompile

  `decompile --to lprog ELF NM [OUT]`: a RISC-V binary as an Lprog program, in text
  (`docs/design/Decompiler.md`).

  The functions are the sized text symbols of `NM` (`llvm-nm -S --defined-only ELF`) whose
  words all decode, with riscv-zkvm's decoder. The program is `liftProg` of them, the lift
  that `RiscV/Lprog/Equiv.lean` proves equivalent to the machine; the text is `toText` of it
  (`Lprog/Text.lean`), and the tool reads its own text back and fails unless it gets the
  program it wrote.

  A function that is not word-aligned, lies outside the executable segments or has a word
  that does not decode is left out and named in a comment: a call to it is an `abort`.

  Untrusted, as every tool here: nothing proved is about this file. What it relies on is
  listed in `Tools/README.md`.
-/

import RiscvZkvm.Interpreter
import MachineChecked.RiscV.Lprog.Lift
import MachineChecked.RiscV.Flapjack.Pancake
import Tools.Elf
import Tools.Fjimg

namespace Tools.Decompile

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open MachineChecked.Lprog MachineChecked.RiscV.Lprog MachineChecked.RiscV.Flapjack
open Tools.Elf

/-- The functions of an image the lift takes, and the names of those it does not, each with
    the reason. -/
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

/-- The instructions of a program, and how many of them are `abort`. -/
def coverage (p : Lprog (Op Reg) Reg) : Nat × Nat :=
  p.foldl (fun (n, a) fd =>
    (n + (fd.body.filter fun i => !(i matches .Llabel ..)).length,
      a + (fd.body.filter fun i => i matches .Labort).length)) (0, 0)

def usage : String :=
  "usage: decompile --to lprog ELF NM [OUT]\n" ++
  "       decompile --to lprog|pancake IMAGE.fjimg [OUT]"

/-- Write `text` to `out?`, or print it. -/
def emit (out? : Option String) (summary text : String) : IO Unit :=
  match out? with
  | some o => do IO.FS.writeFile o text; IO.eprintln s!"decompile: {summary}"
  | none => IO.print text

/-- An Lprog program as text, checked to read back, under a header. -/
def lprogText (p : Lprog (Op Reg) Reg) (skipped : Array String) : Except String (String × String) := do
  let text := toText p
  if (ofText text : Option (Lprog (Op Reg) Reg)) != some p then
    throw "the text does not read back as the program (a symbol the format cannot hold?)"
  let (instrs, aborts) := coverage p
  let summary := s!"{p.length} functions, {instrs} instructions, {aborts} of them `abort` " ++
    s!"(not covered by the lift), {skipped.size} functions left out"
  let header := s!"# decompile --to lprog: {summary}\n" ++
    String.join (skipped.toList.map fun s => s!"# left out: {s}\n")
  return (summary, header ++ text)

/-- An ELF with its symbols, to Lprog. -/
def elfToLprog (elfPath nmPath : String) (out? : Option String) : IO UInt32 := do
  let img ← match parseElf64 (← IO.FS.readBinFile elfPath) with
    | .ok img => pure img
    | .error e => IO.eprintln s!"decompile: {e}"; return 1
  let (fs, skipped) := functions img (parseNm (← IO.FS.readFile nmPath))
  match lprogText (liftProg fs.toList) skipped with
  | .ok (summary, text) => emit out? summary text; return 0
  | .error e => IO.eprintln s!"decompile: {e}"; return 1

/-- A Flapjack image, to Lprog or on to Pancake. -/
def imageTo (target imgPath : String) (out? : Option String) : IO UInt32 := do
  let img ← match Tools.Fjimg.parse (← IO.FS.readFile imgPath) with
    | .ok img => pure img
    | .error e => IO.eprintln s!"decompile: {e}"; return 1
  let p := img.lift
  let (instrs, aborts) := coverage p
  let result : Except String (String × String) :=
    if target == "lprog" then lprogText p #[] else do
      let ds ← img.toPancake
      let some text := MachineChecked.Logical.Pancake.print ds
        | throw "the Pancake program has a construct the printer does not print"
      let summary := s!"{instrs} instructions, {aborts} of them `abort` (not covered by the lift)"
      return (summary, s!"// decompile --to pancake: {summary}\n" ++ text)
  match result with
  | .ok (summary, text) => emit out? summary text; return 0
  | .error e => IO.eprintln s!"decompile: {e}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "--to" :: target :: path :: rest =>
    if path.endsWith ".fjimg" then
      match target, rest with
      | "lprog", [] | "pancake", [] => imageTo target path none
      | "lprog", [o] | "pancake", [o] => imageTo target path (some o)
      | _, _ => IO.eprintln usage; return 2
    else
      match target, rest with
      | "lprog", [nm] => elfToLprog path nm none
      | "lprog", [nm, o] => elfToLprog path nm (some o)
      | _, _ => IO.eprintln usage; return 2
  | _ => IO.eprintln usage; return 2

end Tools.Decompile

def main (args : List String) : IO UInt32 := Tools.Decompile.main args
