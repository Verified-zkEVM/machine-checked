/-
  Tools.Elf

  ELF and symbol-table helpers shared by the build-time tools. Untrusted: boundaries from
  `llvm-nm` are hints, and words are read with riscv-zkvm's own ELF parser.
-/

import RiscvZkvm.Interpreter

namespace Tools.Elf

open RiscvZkvm.Rv64
open RiscvZkvm.Interpreter

/-- A sized function symbol. -/
structure Sym where
  addr : Nat
  size : Nat
  name : String

def hex (n : Nat) (width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (width - s.length) ++ s

/-- A lowercase hexadecimal numeral, without a prefix. -/
def parseHex? (s : String) : Option Nat :=
  if s.isEmpty then none else
  s.foldl (fun acc c => acc.bind fun v =>
    if c.isDigit then some (16 * v + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * v + (c.toNat - 'a'.toNat + 10))
    else none) (some 0)

/-- The symbols of code of an ELF, sorted out: the functions, the symbols whose code no
    function holds (`lost`), and the other names of code that a function holds (`names`: a
    second name of a function, a label inside one). Each of the last two with the reason. Only
    `lost` is code left out. -/
structure Symbols where
  fns : List Sym
  lost : List String := []
  names : List String := []

/-- The functions among text symbols, each given as address, size, whether it is global,
    and name: the sized ones, one per address, and the global ones without a size (`_start`,
    hand-written assembly), which extend to the next text symbol or, if none follows, to the
    end of their section, the least of `ends` after them. Every other symbol is given with
    the reason it is not a function (a second name for an address taken, a local label
    without a size, or a symbol without a size that nothing ends): among `names` if a function
    holds its address, so that its code is taken, and among `lost` if not. -/
def functionsOf (syms : List (Nat × Nat × Bool × String)) (ends : List Nat := []) :
    Symbols := Id.run do
  let mut taken : Std.HashMap Nat String := {}
  let mut out : Array Sym := #[]
  let mut rest : Array (Nat × String) := #[]
  let mut unsized : Array (Nat × String) := #[]
  let starts := syms.map (·.1)
  let alias (n : String) (addr : Nat) (f : String) : String :=
    s!"{n}: at 0x{hex addr 1}, the address of `{f}`, taken under that name"
  for (addr, size, global, n) in syms do
    if size > 0 then
      match taken[addr]? with
      | some f => rest := rest.push (addr, alias n addr f)
      | none =>
        taken := taken.insert addr n
        out := out.push { addr, size, name := n }
    else if global then unsized := unsized.push (addr, n)
    else rest := rest.push (addr, s!"{n}: a local label without a size")
  for (addr, n) in unsized do
    if let some f := taken[addr]? then
      rest := rest.push (addr, alias n addr f); continue
    let some next := ((starts ++ ends).filter (· > addr)).min?
      | rest := rest.push (addr, s!"{n}: no size, and no symbol or end of section after it")
    taken := taken.insert addr n
    out := out.push { addr, size := next - addr, name := n }
  let held (a : Nat) := out.any fun s => s.addr ≤ a && a < s.addr + s.size
  return { fns := out.toList.mergeSort (·.addr ≤ ·.addr)
           lost := (rest.filter (!held ·.1)).toList.map (·.2)
           names := (rest.filter (held ·.1)).toList.map (·.2) }

/-- Sized `t`/`T` symbols from `llvm-nm -S` output, one per address, local labels dropped. -/
def parseNm (txt : String) : List Sym :=
  Symbols.fns <| functionsOf <| (txt.splitOn "\n").filterMap fun line =>
    match line.splitOn " " |>.filter (· ≠ "") with
    | [a, s, k, n] =>
      if (k == "t" || k == "T") && !n.startsWith ".L" then
        match parseHex? a, parseHex? s with
        | some addr, some size => some (addr, size, k == "T", n)
        | _, _ => none
      else none
    | _ => none

/-- The functions of an ELF64 file, from its symbol table, by `functionsOf`, and the symbols
    of code that are not functions, each with the reason. A symbol of code is a function or an
    untyped label in a section that holds code, at an address inside that section: an untyped
    label without a size that a linker puts at or past the section's end (`__SDATA_BEGIN__`,
    `_end`) is not code, and any other symbol outside its section is lost. -/
def symbols (bs : ByteArray) : Except String Symbols := do
  let u (o n : Nat) := Elf.readUIntLE bs o n
  let shoff ← u 0x28 8
  let shentsize ← u 0x3A 2
  let shnum ← u 0x3C 2
  let sh (i : Nat) := shoff + i * shentsize
  let mut out : Array (Nat × Nat × Bool × String) := #[]
  let mut ends : Array Nat := #[]
  let mut outside : Array String := #[]
  for i in [0 : shnum] do
    if (← u (sh i + 4) 4) != 2 then continue
    let off ← u (sh i + 0x18) 8
    let size ← u (sh i + 0x20) 8
    let strs ← u (sh (← u (sh i + 0x28) 4) + 0x18) 8
    for j in [0 : size / 24] do
      let e := off + 24 * j
      let info ← u (e + 4) 1
      let shndx ← u (e + 6) 2
      -- a function or an untyped label, in a section that holds code
      if !(info % 16 == 0 || info % 16 == 2) || shndx == 0 || shndx ≥ shnum then continue
      if (← u (sh shndx + 8) 8) &&& 4 == 0 then continue
      let value ← u (e + 8) 8
      let start ← u (sh shndx + 0x10) 8
      let stop := start + (← u (sh shndx + 0x20) 8)
      let size ← u (e + 16) 8
      let inside := start ≤ value && value < stop
      if !inside && info % 16 == 0 && size == 0 then continue
      let mut name := ""
      for k in [0 : 4096] do
        let c ← u (strs + (← u e 4) + k) 1
        if c == 0 then break
        name := name.push (Char.ofNat c)
      if name.startsWith ".L" || name.startsWith "$" then continue
      if !inside then
        outside := outside.push s!"{name}: outside its section"; continue
      out := out.push (value, size, info / 16 != 0, name)
      ends := ends.push stop
  let s := functionsOf out.toList ends.toList
  return { s with lost := outside.toList ++ s.lost }

/-- The `n` little-endian 32-bit words at virtual address `addr`, from the segment holding them. -/
def wordsAt (img : Elf64Image) (addr n : Nat) : Except String (List (BitVec 32)) := do
  let some seg := img.segments.find? (fun s => s.vaddr ≤ addr && addr + 4 * n ≤ s.vaddr + s.data.size)
    | throw s!"no loaded segment holds [{addr}, {addr + 4 * n})"
  (List.range n).mapM fun i => do
    let off := addr - seg.vaddr + 4 * i
    let w ← Elf.readUIntLE seg.data off 4
    pure (BitVec.ofNat 32 w)

end Tools.Elf
