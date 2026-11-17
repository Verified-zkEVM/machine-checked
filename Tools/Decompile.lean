/-
  Tools.Decompile

  `decompile --to lprog|pancake BINARY [OUT]`: a RISC-V binary as an Lprog program, in text,
  or as a Pancake program (`docs/design/Decompiler.md`).

  An ELF goes by the lift of whole programs (`RiscV/Lift/Whole.lean`) and, to Pancake, by
  lift 2 in SP1's environment (`RiscV/Sp1/Pancake.lean`). Its functions are its text symbols,
  read from its own symbol table, and the hints of the lift are the addresses of code it
  holds as values. A Flapjack image goes by the lift of code without functions. Nothing on
  these routes is proved: they are checked by running (`scripts/decompile-check`).

  `--to lprog --proved` is `liftProg` of the ELF's functions, the lift that
  `RiscV/Lift/Equiv.lean` proves equivalent to the machine. A function with a word that
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
import Tools.Fjimg

namespace Tools.Decompile

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open Lprog MachineChecked.RiscV.Lift MachineChecked.RiscV.Flapjack Lprog.RiscV
open Tools.Elf
open Lprog.Linked (At)

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
    (pancake : Except String (List (Flapjack.Decl MachineChecked.Logical.Pancake.W) × List String)) :
    Except String (String × String) := do
  if target == "lprog" then lprogText p skipped else
    let (ds, traps) ← pancake
    let some text := MachineChecked.Logical.Pancake.print ds
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

/-- The machine of an ELF the lift of whole programs takes: a statically linked 64-bit
    executable, little-endian, for RISC-V without compressed instructions (243), for
    AArch64 (183) or for x86-64 (62). -/
def machineOf (bytes : ByteArray) : Except String Nat := do
  let u (o n : Nat) := Elf.readUIntLE bytes o n
  if bytes.size < 0x40 || (← u 0 4) != 0x464c457f then throw "not an ELF file"
  if (← u 4 1) != 2 then throw "not a 64-bit ELF (a 32-bit program is not supported)"
  if (← u 5 1) != 1 then throw "not a little-endian ELF"
  let machine ← u 0x12 2
  if machine != 243 && machine != 183 && machine != 62 then
    throw "not an ELF for RISC-V, AArch64 or x86-64 (no other instruction set is supported)"
  if (← u 0x10 2) != 2 then
    throw "not a statically linked executable (a relocatable or position-independent file is not supported)"
  if machine == 243 && (← u 0x30 4) &&& 1 != 0 then
    throw "the ELF uses compressed instructions (RVC), which are not supported"
  return machine

/-- The code of an ELF: for each sized text symbol inside an executable segment, at an
    address that is a multiple of `align`, its bytes decoded by `decode` (which is given
    the address of the first). The symbols left out, each with the reason. -/
def codeOf {I : Type} (bytes : ByteArray) (align : Nat) (decode : ByteArray → Nat → Array (At I)) :
    Except String (Elf64Image × Array (String × Array (At I)) × Array String) := do
  -- riscv-zkvm's reader takes RISC-V only, and reads nothing that depends on the machine:
  -- `machineOf` has checked the machine, and the reader is given the field as it wants it
  let img ← parseElf64 ((bytes.set! 0x12 243).set! 0x13 0)
  let mut parts : Array (String × Array (At I)) := #[]
  let mut skipped : Array String := #[]
  for sym in ← symbols bytes do
    if sym.addr % align != 0 || sym.size % align != 0 then
      skipped := skipped.push s!"{sym.name}: not word-aligned"
    else match img.segments.find? (fun s => s.executable && s.vaddr ≤ sym.addr &&
        sym.addr + sym.size ≤ s.vaddr + s.data.size) with
      | none => skipped := skipped.push s!"{sym.name}: not in an executable segment"
      | some seg =>
        let code := decode (seg.data.extract (sym.addr - seg.vaddr) (sym.addr - seg.vaddr + sym.size)) sym.addr
        if !code.isEmpty then parts := parts.push (sym.name, code)
  if parts.isEmpty then throw "the ELF has no function symbols (a stripped binary is not supported)"
  return (img, parts, skipped)

/-- Code that is words of four bytes, each decoded by `decode`. -/
def words {I : Type} (decode : BitVec 32 → I) (bs : ByteArray) (addr : Nat) : Array (At I) :=
  (Array.range (bs.size / 4)).map fun k =>
    let w := (List.range 4).foldl (fun v j => v ||| (bs[4 * k + j]!.toNat <<< (8 * j))) 0
    { addr := BitVec.ofNat 64 (addr + 4 * k), size := 4, instr := decode (BitVec.ofNat 32 w) }

/-- The code of x86-64: one instruction after another from the start of a function. Bytes
    that are no instruction end it: what follows them cannot be told apart, and is one
    piece that is no instruction. -/
def x86Code (bs : ByteArray) (addr : Nat) : Array (At (Option MachineChecked.X86.Lift.Instr)) := Id.run do
  let mut out := #[]
  let mut pos := 0
  for _ in [0 : bs.size] do
    if pos ≥ bs.size then break
    let a := BitVec.ofNat 64 (addr + pos)
    match MachineChecked.X86.Lift.decode bs pos a with
    | some (i, n) =>
      out := out.push { addr := a, size := n, instr := some i }
      pos := pos + n
    | none =>
      out := out.push { addr := a, size := bs.size - pos, instr := none }
      pos := bs.size
  return out

/-- The functions of a program from its code and the addresses of code it holds as values
    (`held`, more than there are): those inside a function, other than its entry, are where
    its computed jumps may go. -/
def fnsOf {I : Type} (parts : Array (String × Array (At I))) (held : Array Nat) : List (Linked.Fun I) := Id.run do
  -- every instruction's address, with its function
  let mut owner : Std.HashMap Nat Nat := {}
  for h : f in [0 : parts.size] do
    for i in parts[f].2 do
      owner := owner.insert i.addr.toNat f
  let mut targets : Array (Array Nat) := Array.replicate parts.size #[]
  for a in (Std.HashSet.ofArray held).toArray.qsort (· < ·) do
    let some f := owner[a]? | continue
    if (parts[f]!.2[0]?.map (·.addr.toNat)) != some a then targets := targets.set! f (targets[f]!.push a)
  return parts.toList.zipIdx.map fun ((name, code), f) =>
    { name, code := code.toList, targets := targets[f]!.toList.map (BitVec.ofNat 64) }

/-- The words of four and of eight bytes in the data of an image, where one would be
    aligned. -/
def dataWords (img : Elf64Image) : Array Nat × Array Nat := Id.run do
  let mut w4 : Array Nat := #[]
  let mut w8 : Array Nat := #[]
  for seg in img.segments do
    if seg.executable then continue
    for i in [0 : seg.data.size] do
      let a := seg.vaddr + i
      let word (n : Nat) := (List.range n).foldl (fun v k => v ||| (seg.data[i + k]!.toNat <<< (8 * k))) 0
      if a % 4 == 0 && i + 4 ≤ seg.data.size then w4 := w4.push (word 4)
      if a % 8 == 0 && i + 8 ≤ seg.data.size then w8 := w8.push (word 8)
  return (w4, w8)

/-- How far after an `auipc` or `lui` the `addi` that completes an address is looked for. -/
def window : Nat := 24

/-- The addresses RISC-V code forms: the constant `auipc` or `lui` forms, alone or with an
    `addi` to its register soon after. -/
def formedRiscV (parts : Array (String × Array (At Decoded))) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for (_, prog) in parts do
    for k in [0 : prog.size] do
      let (rd, base) : Reg × Option Word := match prog[k]!.instr with
        | .instr (.AUIPC rd imm) => (rd, some (prog[k]!.addr + auipcOff imm))
        | .instr (.LUI rd imm) => (rd, some ((imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64))
        | _ => (.x0, none)
      let some base := base | continue
      out := out.push base.toNat
      for j in [k + 1 : min prog.size (k + 1 + window)] do
        match prog[j]!.instr with
        | .instr (.ADDI _ rs off) | .instr (.ADDIW _ rs off) =>
          if rs = rd then out := out.push (base + signExtend12 off).toNat
        | _ => pure ()
  return out

/-- Where the jump tables of AArch64 code may lead. A table there is of 32-bit offsets from
    an anchor that an `adr` just before the `br` forms, so: each anchor plus each word of
    four bytes in the data. -/
def tablesArm (parts : Array (String × Array (At (Option Arm64.Instr)))) (w4 : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for (_, prog) in parts do
    let some first := prog[0]? | continue
    let lo := first.addr.toNat
    let hi := lo + 4 * prog.size
    for k in [0 : prog.size] do
      let some (.br _) := prog[k]!.instr | continue
      for j in [k - min k 4 : k] do
        let some (.adr false _ off) := prog[j]!.instr | continue
        let anchor := prog[j]!.addr + off
        for w in w4 do
          let t := (anchor + (BitVec.ofNat 32 w).signExtend 64).toNat
          if lo < t && t < hi && t % 4 == 0 then out := out.push t
  return out

/-- The addresses x86-64 code forms, and where its jump tables of offsets may lead. An
    address is formed by `lea` or as a constant. A table of offsets is of 32-bit numbers
    counted from an address that a `lea` or an `add` before the `jmp` names, so: each such
    address plus each word of four bytes in the data. -/
def formedX86 (parts : Array (String × Array (At (Option MachineChecked.X86.Lift.Instr)))) (w4 : Array Nat) :
    Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for (_, prog) in parts do
    let some first := prog[0]? | continue
    let lo := first.addr.toNat
    let hi := prog.foldl (fun n i => n + i.size) lo
    -- the address an instruction names without a register
    let named (i : Option MachineChecked.X86.Lift.Instr) : Option Nat := match i with
      | some (.lea _ _ { base := none, index := none, disp }) => some disp.toNat
      | some (.mov _ _ (.imm v)) | some (.push (.imm v)) | some (.alu .add _ _ (.imm v)) => some v.toNat
      | some (.movx true .q .d _ (.mem { base := none, disp, .. })) => some disp.toNat
      | _ => none
    for k in [0 : prog.size] do
      if let some a := named prog[k]!.instr then out := out.push a
      let some (.jmpTo (.reg _)) := prog[k]!.instr | continue
      for j in [k - min k 8 : k] do
        let some anchor := named prog[j]!.instr | continue
        for w in w4 do
          let t := (BitVec.ofNat 64 anchor + (BitVec.ofNat 32 w).signExtend 64).toNat
          if lo < t && t < hi then out := out.push t
  return out

/-- An ELF, to Lprog or on to Pancake, by the lift of whole programs. -/
def elfTo (target elfPath : String) (out? : Option String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile elfPath
  let r : Except String (String × String) := do
    let machine ← machineOf bytes
    if machine == 62 then
      let (img, parts, skipped) ← codeOf bytes 1 x86Code
      let (w4, w8) := dataWords img
      let g : MachineChecked.X86.Guest :=
        { fns := fnsOf parts (w8 ++ formedX86 parts w4), entry := BitVec.ofNat 64 img.entry
          memory := memoryOf img }
      render target g.lift g.fns.length skipped g.toPancake
    else if machine == 243 then
      let (img, parts, skipped) ← codeOf bytes 4 (words decodeWord)
      let (w4, w8) := dataWords img
      let g : MachineChecked.RiscV.Sp1.Guest :=
        { fns := fnsOf parts (w4 ++ w8 ++ formedRiscV parts), entry := BitVec.ofNat 64 img.entry
          memory := memoryOf img }
      render target g.lift (g.fns.map fun f => (Whole.parts g.fns f).length).sum skipped g.toPancake
    else
      let (img, parts, skipped) ← codeOf bytes 4 (words Arm64.decode)
      let (w4, w8) := dataWords img
      let g : MachineChecked.ARM.Guest :=
        { fns := fnsOf parts (w8 ++ tablesArm parts w4), entry := BitVec.ofNat 64 img.entry
          memory := memoryOf img }
      render target g.lift g.fns.length skipped g.toPancake
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
  | "--to" :: target :: path :: rest =>
    if target != "lprog" && target != "pancake" || rest.length > 1 then
      IO.eprintln usage; return 2
    else if path.endsWith ".fjimg" then imageTo target path rest.head?
    else elfTo target path rest.head?
  | _ => IO.eprintln usage; return 2

end Tools.Decompile

def main (args : List String) : IO UInt32 := Tools.Decompile.main args
