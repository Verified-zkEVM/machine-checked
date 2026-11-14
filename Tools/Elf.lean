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

/-- The functions among text symbols, each given as address, size, whether it is global,
    and name: the sized ones, one per address, and the global ones without a size (`_start`,
    hand-written assembly), which extend to the next text symbol. -/
def functionsOf (syms : List (Nat × Nat × Bool × String)) : List Sym := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Sym := #[]
  let mut unsized : Array (Nat × String) := #[]
  let mut starts : Array Nat := #[]
  for (addr, size, global, n) in syms do
    starts := starts.push addr
    if size > 0 && !seen.contains addr then
      seen := seen.insert addr
      out := out.push { addr, size, name := n }
    else if size == 0 && global then
      unsized := unsized.push (addr, n)
  for (addr, n) in unsized do
    if seen.contains addr then continue
    let nexts := starts.filter (· > addr)
    let some next := nexts.foldl (fun acc a => match acc with | none => some a | some b => some (min a b)) none
      | continue
    seen := seen.insert addr
    out := out.push { addr, size := next - addr, name := n }
  return out.toList.mergeSort (·.addr ≤ ·.addr)

/-- Sized `t`/`T` symbols from `llvm-nm -S` output, one per address, local labels dropped. -/
def parseNm (txt : String) : List Sym :=
  functionsOf <| (txt.splitOn "\n").filterMap fun line =>
    match line.splitOn " " |>.filter (· ≠ "") with
    | [a, s, k, n] =>
      if (k == "t" || k == "T") && !n.startsWith ".L" then
        match parseHex? a, parseHex? s with
        | some addr, some size => some (addr, size, k == "T", n)
        | _, _ => none
      else none
    | _ => none

/-- The functions of an ELF64 file, from its symbol table: what `parseNm` gives of
    `llvm-nm -S --defined-only`, without `llvm-nm`. -/
def symbols (bs : ByteArray) : Except String (List Sym) := do
  let u (o n : Nat) := Elf.readUIntLE bs o n
  let shoff ← u 0x28 8
  let shentsize ← u 0x3A 2
  let shnum ← u 0x3C 2
  let sh (i : Nat) := shoff + i * shentsize
  let mut out : Array (Nat × Nat × Bool × String) := #[]
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
      let mut name := ""
      for k in [0 : 4096] do
        let c ← u (strs + (← u e 4) + k) 1
        if c == 0 then break
        name := name.push (Char.ofNat c)
      if name.startsWith ".L" || name.startsWith "$" then continue
      out := out.push (← u (e + 8) 8, ← u (e + 16) 8, info / 16 != 0, name)
  return functionsOf out.toList

/-- The `n` little-endian 32-bit words at virtual address `addr`, from the segment holding them. -/
def wordsAt (img : Elf64Image) (addr n : Nat) : Except String (List (BitVec 32)) := do
  let some seg := img.segments.find? (fun s => s.vaddr ≤ addr && addr + 4 * n ≤ s.vaddr + s.data.size)
    | throw s!"no loaded segment holds [{addr}, {addr + 4 * n})"
  (List.range n).mapM fun i => do
    let off := addr - seg.vaddr + 4 * i
    let w ← Elf.readUIntLE seg.data off 4
    pure (BitVec.ofNat 32 w)

end Tools.Elf
