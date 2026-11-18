/-
  Tools.Decompile

  `decompile --to lprog|pancake BINARY [OUT]` and `--to lean ELF OUTDIR NS`: a RISC-V, AArch64
  or x86-64 ELF (or, to Lprog and Pancake, a Flapjack image) as an Lprog program in text, as a
  Pancake program, or as Lean modules
  (`Tools/ToLean.lean`); and `--table`, `--kinds`, `--listing` for the `LIMITS.md` tables and
  x86-64's decoder (`docs/design/Decompiler.md`, usage in `Tools/README.md`).

  An ELF goes by the lift of whole programs of its instruction set (`RiscV/Lift/Whole.lean`,
  `ARM/Lift/Lift.lean`, `X86/Lift/Lift.lean`) and, to Pancake, by lift 2 in its environment
  (SP1's for RISC-V, `RiscV/Sp1/Pancake.lean`; a bare one, without an operating system, for
  AArch64 and x86-64, `ARM/Bare.lean`, `X86/Bare.lean`). Its functions are its text symbols,
  read from its own symbol table, and the hints of the lift are the addresses of code it
  holds as values. A Flapjack image goes by the lift of code without functions. Nothing on
  these routes is proved: they are checked by running (`scripts/decompile-check`).

  `--to lprog --proved` is `liftProg` of the ELF's functions, the lift that
  `RiscV/Lift/Equiv.lean` proves equivalent to the machine: under its conditions (the
  outermost return outside the code, a program that never goes `wrong`), which the tool does
  not check, and as to how a run ends, not the state it ends in. A function with a word that
  riscv-zkvm does not decode is left out there and named in a comment.

  Lprog text is `toText` (`Lprog/Text.lean`); the tool reads its own text back and fails
  unless it gets the program it wrote.

  Untrusted, as every tool here: nothing proved is about this file. What it relies on is
  listed in `Tools/README.md`.
-/

import RiscvZkvm.Interpreter
import MachineChecked.RiscV.Lift.Lift
import MachineChecked.RiscV.Flapjack.Pancake
import MachineChecked.RiscV.Sp1.Pancake
import MachineChecked.ARM.Bare
import MachineChecked.X86.Bare
import MachineChecked.X86.Lift.Table
import MachineChecked.ARM.Lift.Table
import MachineChecked.RiscV.Lift.Table
import Tools.Elf
import Tools.ToLean
import Tools.Program
import Tools.Fjimg

namespace Tools.Decompile

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open Lprog MachineChecked.RiscV.Lift MachineChecked.RiscV.Flapjack Lprog.RiscV
open Tools.Elf
open Tools.ToLean (functions)
open Tools.Program
open Lprog.Linked (At)


section
variable {Reg : Type} [RegText Reg] [DecidableEq Reg]

/-- The instructions of a program, and how many of them are `abort`. -/
def coverage (p : Lprog (Op Reg) Reg) : Nat × Nat :=
  p.foldl (fun (n, a) fd =>
    (n + (fd.body.filter fun i => !(i matches .Llabel ..)).length,
      a + (fd.body.filter fun i => i matches .Labort).length)) (0, 0)

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

/-- Lines that say what a Pancake program is of: which function is which. -/
def legend (p : Lprog (Op Reg) Reg) : String :=
  String.join ((MachineChecked.Logical.names p).toList.zip p |>.map fun (n, fd) =>
    s!"// {n}: {fd.name} at 0x{hex fd.addr.toNat 8}\n")

/-- A whole program as text: Lprog, or the Pancake program `pancake` with the places where
    it may give up. `ends` is the number of `abort`s that only end a part of a function. -/
def render (target : String) (p : Lprog (Op Reg) Reg) (ends : Nat) (skipped : Array String)
    (pancake : Except String (List (Flapjack.Decl Pancake.W) × List String)) :
    Except String (String × String) := do
  if target == "lprog" then lprogText p skipped else
    let (ds, traps) ← pancake
    let some text := Pancake.print ds
      | throw "the Pancake program has a construct the printer does not print"
    let (instrs, all) := coverage p
    let looped := (ds.filter fun d => match d with
      | .function fd => fd.name.endsWith "_c0"
      | _ => false).length
    let summary := s!"{p.length} functions ({looped} of them as a loop over their blocks), " ++
      s!"{instrs} instructions, {all - ends} of them `abort` (not covered by the lift), " ++
      s!"{skipped.size} functions left out"
    return (summary, s!"// decompile --to pancake: {summary}\n" ++
      String.join (skipped.toList.map fun s => s!"// left out: {s}\n") ++ legend p ++
      String.join (traps.zipIdx.map fun (t, k) => s!"// trap {k}: {t}\n") ++ "\n" ++ text)

end

def usage : String :=
  "usage: decompile --to lprog|pancake ELF [OUT]\n" ++
  "       decompile --to lprog --proved ELF [OUT]\n" ++
  "       decompile --to lean --proved ELF OUTDIR NAMESPACE\n" ++
  "       decompile --to lean [--pancake] ELF OUTDIR NAMESPACE\n" ++
  "       decompile --to lprog|pancake IMAGE.fjimg [OUT]\n" ++
  "       decompile --kinds riscv|aarch64|x86-64 INSTRUCTIONS\n" ++
  "       decompile --table riscv|aarch64|x86-64 [KINDS]\n" ++
  "       decompile --listing ELF"

/-- Write `text` to `out?`, or print it. -/
def emit (out? : Option String) (summary text : String) : IO Unit :=
  match out? with
  | some o => do IO.FS.writeFile o text; IO.eprintln s!"decompile: {summary}"
  | none => IO.print text

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

/-- `--to lean`: the `--proved` lift of the ELF at `elfPath` as Lean modules under `outDir`, in
    namespace `ns` (`Tools/ToLean.lean`). -/
def toLean (elfPath outDir ns : String) : IO UInt32 := do
  try
    let (n, k, skipped) ← Tools.ToLean.emit elfPath outDir ns
    IO.println s!"decompile: {n} functions, {k} instructions, {skipped.size} functions left out, as {(Tools.ToLean.nsPath outDir ns).addExtension "lean"} and {Tools.ToLean.nsPath outDir ns}/"
    for r in skipped do IO.println s!"  left out: {r}"
    return 0
  catch e => IO.eprintln s!"decompile: {e}"; return 1

/-- `--to lean` by the lift of whole programs: the program `--to lprog` gives as Lean modules
    under `outDir`, in namespace `ns`, or with `pancake` the one `--to pancake` gives
    (`Tools/ToLean.lean`). -/
def toLeanRoute (elfPath outDir ns : String) (pancake : Bool) : IO UInt32 := do
  try
    let (n, skipped) ← Tools.ToLean.emitRoute elfPath outDir ns pancake
    IO.println s!"decompile: {n} functions, {skipped.size} symbols left out, as {(Tools.ToLean.nsPath outDir ns).addExtension "lean"} and {Tools.ToLean.nsPath outDir ns}/"
    for r in skipped do IO.println s!"  left out: {r}"
    return 0
  catch e => IO.eprintln s!"decompile: {e}"; return 1

/-- An ELF, to Lprog or on to Pancake, by the lift of whole programs. -/
def elfTo (target elfPath : String) (out? : Option String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile elfPath
  let r : Except String (String × String) := do
    let i ← inputOf bytes
    match i.machine with
    | .x86 =>
      let g := x86Program i.code i.entry i.memory
      render target g.lift g.fns.length i.skipped g.toPancake
    | .riscv =>
      let g := riscvProgram i.code i.entry i.memory
      render target g.lift (g.fns.map fun f => (Whole.parts g.fns f).length).sum i.skipped g.toPancake
    | .arm =>
      let g := armProgram i.code i.entry i.memory
      render target g.lift g.fns.length i.skipped g.toPancake
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
      let some text := Pancake.print ds
        | throw "the Pancake program has a construct the printer does not print"
      let summary := s!"{instrs} instructions, {aborts} of them `abort` (not covered by the lift)"
      return (summary, s!"// decompile --to pancake: {summary}\n" ++ text)
  match result with
  | .ok (summary, text) => emit out? summary text; return 0
  | .error e => IO.eprintln s!"decompile: {e}"; return 1

/-- The instructions of an instruction set by kind (`RiscV/Lift/Table.lean`,
    `ARM/Lift/Table.lean`): the kinds with whether each is lifted, and the kind of an
    instruction given as its bytes. -/
def kindsOf (isa : String) : Except String (List (String × Bool) × (ByteArray → String)) :=
  let word (bs : ByteArray) : BitVec 32 :=
    BitVec.ofNat 32 ((List.range 4).foldl (fun v k => v ||| (bs[k]!.toNat <<< (8 * k))) 0)
  match isa with
  | "riscv" => .ok (Table.rows, fun bs => Table.kind (word bs))
  | "aarch64" => .ok (MachineChecked.ARM.Lift.Table.rows,
      fun bs => MachineChecked.ARM.Lift.Table.kind (Arm64.decode (word bs)))
  | "x86-64" => .ok (MachineChecked.X86.Lift.Table.rows,
      fun bs => MachineChecked.X86.Lift.Table.kind ((MachineChecked.X86.Lift.decode bs 0 0).map (·.1)))
  | _ => .error s!"no instruction set `{isa}` (riscv, aarch64, x86-64)"

/-- The lines of a file that are not empty. -/
def linesOf (path : String) : IO (List String) :=
  return ((← IO.FS.readFile path).splitOn "\n").map (·.trimAscii.toString) |>.filter (· != "")

/-- `--kinds`: the kinds of the instructions of a file, one instruction to a line as the
    bytes it is in memory, in hexadecimal. -/
def kinds (isa path : String) : IO UInt32 := do
  match kindsOf isa with
  | .error e => IO.eprintln s!"decompile: {e}"; return 1
  | .ok (_, kind) =>
    let mut seen : Std.HashSet String := {}
    for l in ← linesOf path do
      let some bytes := (List.range (l.length / 2)).mapM fun k =>
          (parseHex? ((l.drop (2 * k)).take 2).toString).map (·.toUInt8)
        | IO.eprintln s!"decompile: not bytes in hexadecimal: {l}"; return 1
      seen := seen.insert (kind (ByteArray.mk bytes.toArray))
    IO.print (String.join ((seen.toArray.qsort (· < ·)).toList.map (· ++ "\n")))
    return 0

/-- `--table`: the table of an instruction set, in Markdown. `run?` is a file of the kinds
    the check runs, as `--kinds` writes it. -/
def table (isa : String) (run? : Option String) : IO UInt32 := do
  match kindsOf isa with
  | .error e => IO.eprintln s!"decompile: {e}"; return 1
  | .ok (rows, _) =>
    let run ← match run? with
      | some path => linesOf path
      | none => pure []
    if let some k := run.find? fun k => !rows.any (·.1 == k) then
      IO.eprintln s!"decompile: the check runs a kind the table does not have: {k}"; return 1
    IO.println "| instruction | lifted | run by the check |\n| --- | --- | --- |"
    for (k, lifted) in rows.eraseDups do
      IO.println s!"| {k} | {if lifted then "yes" else "no: the program gives up there"} | {if run.contains k then "yes" else "no"} |"
    return 0

/-- `--listing`: the instructions of an x86-64 ELF as the decoder reads them, one to a line:
    its address, its length and its kind. For comparing the decoder with a disassembler. -/
def listing (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let r : Except String String := do
    if (← machineOf bytes) != 62 then throw "not an ELF for x86-64"
    let (_, parts, _) ← codeOf bytes 1 x86Code
    return String.join (parts.toList.flatMap fun (_, code) => code.toList.map fun i =>
      s!"{hex i.addr.toNat 8} {i.size} {MachineChecked.X86.Lift.Table.kind i.instr}\n")
  match r with
  | .ok text => IO.print text; return 0
  | .error e => IO.eprintln s!"decompile: {e}"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--listing", path] => listing path
  | ["--kinds", isa, path] => kinds isa path
  | ["--table", isa] => table isa none
  | ["--table", isa, run] => table isa (some run)
  | ["--to", "lprog", "--proved", path] => elfProved path none
  | ["--to", "lprog", "--proved", path, o] => elfProved path (some o)
  | ["--to", "lean", "--proved", path, out, ns] => toLean path out ns
  | ["--to", "lean", "--pancake", path, out, ns] => toLeanRoute path out ns true
  | ["--to", "lean", path, out, ns] => toLeanRoute path out ns false
  | "--to" :: target :: path :: rest =>
    if target != "lprog" && target != "pancake" || rest.length > 1 then
      IO.eprintln usage; return 2
    else if path.endsWith ".fjimg" then imageTo target path rest.head?
    else elfTo target path rest.head?
  | _ => IO.eprintln usage; return 2

end Tools.Decompile

def main (args : List String) : IO UInt32 := Tools.Decompile.main args
