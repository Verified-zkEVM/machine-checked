/-
  Tools.Decompile

  `decompile --to lprog|pancake BINARY [OUT]`: a RISC-V binary as an Lprog program, in text,
  or as a Pancake program (`docs/design/Decompiler.md`).

  An ELF goes by the lift of whole programs (`RiscV/Lprog/Whole.lean`) and, to Pancake, by
  lift 2 in SP1's environment (`RiscV/Sp1/Pancake.lean`). Its functions are its text symbols,
  read from its own symbol table, and the hints of the lift are the addresses of code it
  holds as values. A Flapjack image goes by the lift of code without functions. Nothing on
  these routes is proved: they are checked by running (`scripts/decompile-check`).

  `--to lprog --proved` is `liftProg` of the ELF's functions, the lift that
  `RiscV/Lprog/Equiv.lean` proves equivalent to the machine. A function with a word that
  riscv-zkvm does not decode is left out there and named in a comment.

  Lprog text is `toText` (`Lprog/Text.lean`); the tool reads its own text back and fails
  unless it gets the program it wrote.

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

/-- How far after an `auipc` or `lui` the `addi` that completes an address is looked for. -/
def window : Nat := 24

/-- The addresses of code that the image holds as values: in its data, as a word of four
    or eight bytes where one would be aligned, and in its code, as the constant `auipc` or
    `lui` forms, alone or with an `addi` to its register soon after. More than there are:
    the lift only narrows its candidates with them. -/
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
      -- the `addi` need not come right after: any within `window` that adds to the register
      let (rd, base) : Reg × Option Word := match prog[k]! with
        | .instr (.AUIPC rd imm) => (rd, some (p.addrOf k + auipcOff imm))
        | .instr (.LUI rd imm) => (rd, some ((imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64))
        | _ => (.x0, none)
      let some base := base | continue
      if isCode base.toNat then out := out.insert base.toNat
      for j in [k + 1 : min prog.size (k + 1 + window)] do
        match prog[j]! with
        | .instr (.ADDI _ rs off) | .instr (.ADDIW _ rs off) =>
          let v := (base + signExtend12 off).toNat
          if rs = rd && isCode v then out := out.insert v
        | _ => pure ()
  return out

/-- Is this a file the lift of whole programs takes? A statically linked RV64 executable,
    little-endian, without compressed instructions. -/
def supported (bytes : ByteArray) : Except String Unit := do
  let u (o n : Nat) := Elf.readUIntLE bytes o n
  if bytes.size < 0x40 || (← u 0 4) != 0x464c457f then throw "not an ELF file"
  if (← u 4 1) != 2 then throw "not a 64-bit ELF (RV32 is not supported)"
  if (← u 5 1) != 1 then throw "not a little-endian ELF"
  if (← u 0x12 2) != 243 then throw "not a RISC-V ELF"
  if (← u 0x10 2) != 2 then
    throw "not a statically linked executable (a relocatable or position-independent file is not supported)"
  if (← u 0x30 4) &&& 1 != 0 then throw "the ELF uses compressed instructions (RVC), which are not supported"

/-- An ELF as a guest: its functions are its sized text symbols, word-aligned and inside
    an executable segment, and the hints of the lift are the addresses of code it holds as
    values. The functions left out, each with the reason. -/
def guestOf (bytes : ByteArray) : Except String (MachineChecked.RiscV.Sp1.Guest × Array String) := do
  supported bytes
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
  if parts.isEmpty then throw "the ELF has no function symbols (a stripped binary is not supported)"
  -- every instruction's address, with its function
  let mut owner : Std.HashMap Nat Nat := {}
  for h : f in [0 : parts.size] do
    let p := parts[f].2
    for k in [0 : p.prog.length] do
      owner := owner.insert (p.base.toNat + 4 * k) f
  let held := codeAddrs img (parts.map (·.2)) owner.contains
  let mut targets : Array (Array Nat) := Array.replicate parts.size #[]
  for a in held.toArray.qsort (· < ·) do
    let some f := owner[a]? | continue
    if parts[f]!.2.base.toNat != a then targets := targets.set! f (targets[f]!.push a)
  let fns := parts.toList.zipIdx.map fun ((name, part), f) =>
    ({ name, part, targets := targets[f]!.toList.map (BitVec.ofNat 64) } : Fun)
  return ({ whole := { fns }, entry := BitVec.ofNat 64 img.entry,
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
      let (ds, traps) ← g.toPancake
      let some text := MachineChecked.Logical.Pancake.print ds
        | throw "the Pancake program has a construct the printer does not print"
      let (instrs, all) := coverage p
      -- without the `abort` that ends each part of each function
      let aborts := all - (g.whole.fns.map fun f => (g.whole.parts f).length).sum
      let looped := (ds.filter fun d => match d with
        | .function fd => fd.name.endsWith "_c0"
        | _ => false).length
      let summary := s!"{p.length} functions ({looped} of them as a loop over their blocks), " ++
        s!"{instrs} instructions, {aborts} of them `abort` (not covered by the lift), " ++
        s!"{skipped.size} functions left out"
      return (summary, s!"// decompile --to pancake: {summary}\n" ++
        String.join (skipped.toList.map fun s => s!"// left out: {s}\n") ++ legend p ++
        String.join (traps.zipIdx.map fun (t, k) => s!"// trap {k}: {t}\n") ++ "\n" ++ text)
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
