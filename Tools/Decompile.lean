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
import Tools.Elf

namespace Tools.Decompile

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open MachineChecked.Lprog MachineChecked.RiscV.Lprog
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

def main (args : List String) : IO UInt32 := do
  let (elfPath, nmPath, out?) ← match args with
    | ["--to", "lprog", e, n] => pure (e, n, none)
    | ["--to", "lprog", e, n, o] => pure (e, n, some o)
    | _ => IO.eprintln "usage: decompile --to lprog ELF NM [OUT]"; return 2
  let img ← match parseElf64 (← IO.FS.readBinFile elfPath) with
    | .ok img => pure img
    | .error e => IO.eprintln s!"decompile: {e}"; return 1
  let (fs, skipped) := functions img (parseNm (← IO.FS.readFile nmPath))
  let p := liftProg fs.toList
  let text := toText p
  if (ofText text : Option (Lprog (Op Reg) Reg)) != some p then
    IO.eprintln "decompile: the text does not read back as the program (a symbol the format cannot hold?)"
    return 1
  let (instrs, aborts) := coverage p
  let summary := s!"{p.length} functions, {instrs} instructions, {aborts} of them `abort` " ++
    s!"(not covered by the lift), {skipped.size} functions left out"
  let header := s!"# decompile --to lprog: {summary}\n" ++
    String.join (skipped.toList.map fun s => s!"# left out: {s}\n")
  match out? with
  | some o => IO.FS.writeFile o (header ++ text); IO.eprintln s!"decompile: {summary}"
  | none => IO.print (header ++ text)
  return 0

end Tools.Decompile

def main (args : List String) : IO UInt32 := Tools.Decompile.main args
