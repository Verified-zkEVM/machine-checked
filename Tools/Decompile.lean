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
import MachineChecked.RiscV.Sp1.Pancake
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
  "usage: decompile --to lprog|pancake ELF [OUT]\n" ++
  "       decompile --to lprog --proved ELF [OUT]\n" ++
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

/-- An ELF, to Lprog by the lift the theorems are about (`liftProg`). -/
def elfProved (elfPath : String) (out? : Option String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile elfPath
  let r : Except String (String × String) := do
    let img ← parseElf64 bytes
    let (fs, skipped) := functions img (← symbols bytes)
    lprogText (liftProg fs.toList) skipped
  match r with
  | .ok (summary, text) => emit out? summary text; return 0
  | .error e => IO.eprintln s!"decompile: {e}"; return 1

/-- The words of an image that every loaded segment's file bytes make, at the addresses
    that are multiples of eight; the words that are zero are left out. -/
def memoryOf (img : Elf64Image) : List (Word × Word) := Id.run do
  let mut words : Std.HashMap Nat Nat := {}
  for seg in img.segments do
    for h : i in [0 : seg.data.size] do
      let a := seg.vaddr + i
      let b := seg.data[i].toNat
      if b != 0 then
        words := words.insert (a / 8 * 8) ((words.getD (a / 8 * 8) 0) ||| (b <<< (8 * (a % 8))))
  return (words.toArray.qsort (·.1 < ·.1)).toList.map fun (a, w) => (BitVec.ofNat 64 a, BitVec.ofNat 64 w)

/-- The addresses of code that the image holds as values: in its data, as a word of four
    or eight bytes where one would be aligned, and in its code, as the constant `auipc` or
    `lui` forms with the `addi` after it. -/
def codeAddrs (img : Elf64Image) (parts : Array Part) (isCode : Nat → Bool) : Std.HashSet Nat := Id.run do
  let mut out : Std.HashSet Nat := {}
  for seg in img.segments do
    if seg.executable then continue
    for i in [0 : seg.data.size] do
      let a := seg.vaddr + i
      for n in [4, 8] do
        if a % n == 0 && i + n ≤ seg.data.size then
          let v := (List.range n).foldl (fun v k => v ||| (seg.data[i + k]!.toNat <<< (8 * k))) 0
          if isCode v then out := out.insert v
  for p in parts do
    let prog := p.prog.toArray
    for k in [0 : prog.size] do
      let v? : Option Word := match prog[k]!, prog[k + 1]? with
        | .instr (.AUIPC rd imm), some (.instr (.ADDI rd' rs off)) =>
          if rd' = rd ∧ rs = rd then some (p.addrOf k + auipcOff imm + signExtend12 off) else none
        | .instr (.LUI rd imm), some (.instr (.ADDI rd' rs off))
        | .instr (.LUI rd imm), some (.instr (.ADDIW rd' rs off)) =>
          if rd' = rd ∧ rs = rd then
            some ((imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64 + signExtend12 off)
          else none
        | _, _ => none
      if let some v := v? then
        if isCode v.toNat then out := out.insert v.toNat
  return out

/-- An ELF as a guest: its functions are its sized text symbols, word-aligned and inside
    an executable segment, and the hints of the lift are the addresses of code it holds as
    values. The functions left out, each with the reason. -/
def guestOf (bytes : ByteArray) : Except String (MachineChecked.RiscV.Sp1.Guest × Array String) := do
  let img ← parseElf64 bytes
  let mut parts : Array (String × Part) := #[]
  let mut skipped : Array String := #[]
  for sym in ← symbols bytes do
    if sym.addr % 4 != 0 || sym.size % 4 != 0 then
      skipped := skipped.push s!"{sym.name}: not word-aligned"
    else if !img.segments.any (fun s => s.executable && s.vaddr ≤ sym.addr &&
        sym.addr + sym.size ≤ s.vaddr + s.data.size) then
      skipped := skipped.push s!"{sym.name}: not in an executable segment"
    else match wordsAt img sym.addr (sym.size / 4) with
      | .error e => skipped := skipped.push s!"{sym.name}: {e}"
      | .ok ws => parts := parts.push (sym.name, { base := BitVec.ofNat 64 sym.addr, prog := ws.map decodeWord })
  -- every instruction's address, with its function
  let mut owner : Std.HashMap Nat Nat := {}
  for h : f in [0 : parts.size] do
    let p := parts[f].2
    for k in [0 : p.prog.length] do
      owner := owner.insert (p.base.toNat + 4 * k) f
  let held := codeAddrs img (parts.map (·.2)) owner.contains
  let mut targets : Array (Array Nat) := Array.replicate parts.size #[]
  let mut taken : Array Nat := #[]
  for a in held.toArray.qsort (· < ·) do
    let some f := owner[a]? | continue
    if parts[f]!.2.base.toNat == a then taken := taken.push f
    else targets := targets.set! f (targets[f]!.push a)
  let fns := parts.toList.zipIdx.map fun ((name, part), f) =>
    ({ name, part, targets := targets[f]!.toList.map (BitVec.ofNat 64) } : Fun)
  return ({ whole := { fns, taken := taken.toList }, entry := BitVec.ofNat 64 img.entry,
            memory := memoryOf img }, skipped)

/-- Lines that say what a Pancake program is of: which function is which. -/
def legend (p : Lprog (Op Reg) Reg) : String :=
  String.join ((MachineChecked.Logical.names p).toList.zip p |>.map fun (n, fd) =>
    s!"// {n}: {fd.name} at 0x{hex fd.addr.toNat 8}\n")

/-- An ELF, to Lprog or on to Pancake, by the lift of whole programs (`liftWhole`). -/
def elfTo (target elfPath : String) (out? : Option String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile elfPath
  let r : Except String (String × String) := do
    let (g, skipped) ← guestOf bytes
    let p := g.lift
    if target == "lprog" then lprogText p skipped else
      let ds ← g.toPancake
      let some text := MachineChecked.Logical.Pancake.print ds
        | throw "the Pancake program has a construct the printer does not print"
      let (instrs, aborts) := coverage p
      let looped := (ds.filter fun d => match d with
        | .function fd => fd.name.endsWith "_c0"
        | _ => false).length
      let summary := s!"{p.length} functions ({looped} of them as a loop over their blocks), " ++
        s!"{instrs} instructions, {aborts} of them `abort` (not covered by the lift), " ++
        s!"{skipped.size} functions left out"
      return (summary, s!"// decompile --to pancake: {summary}\n" ++
        String.join (skipped.toList.map fun s => s!"// left out: {s}\n") ++ legend p ++ "\n" ++ text)
  match r with
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
  | ["--to", "lprog", "--proved", path] => elfProved path none
  | ["--to", "lprog", "--proved", path, o] => elfProved path (some o)
  | "--to" :: target :: path :: rest =>
    if target != "lprog" && target != "pancake" || rest.length > 1 then
      IO.eprintln usage; return 2
    else if path.endsWith ".fjimg" then imageTo target path rest.head?
    else elfTo target path rest.head?
  | _ => IO.eprintln usage; return 2

end Tools.Decompile

def main (args : List String) : IO UInt32 := Tools.Decompile.main args
