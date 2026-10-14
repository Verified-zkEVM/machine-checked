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

/-- Sized `t`/`T` symbols from `llvm-nm -S` output, one per address, local labels dropped. -/
def parseNm (txt : String) : List Sym := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Sym := #[]
  -- global text symbols without a size (`_start`, hand-written assembly): they extend to
  -- the next text symbol
  let mut unsized : Array (Nat × String) := #[]
  let mut starts : Array Nat := #[]
  for line in txt.splitOn "\n" do
    match line.splitOn " " |>.filter (· ≠ "") with
    | [a, s, k, n] =>
      if (k == "t" || k == "T") && !n.startsWith ".L" then
        match parseHex? a, parseHex? s with
        | some addr, some size =>
          starts := starts.push addr
          if size > 0 && !seen.contains addr then
            seen := seen.insert addr
            out := out.push { addr, size, name := n }
          else if size == 0 && k == "T" then
            unsized := unsized.push (addr, n)
        | _, _ => pure ()
    | _ => pure ()
  for (addr, n) in unsized do
    if seen.contains addr then continue
    let nexts := starts.filter (· > addr)
    let some next := nexts.foldl (fun acc a => match acc with | none => some a | some b => some (min a b)) none
      | continue
    seen := seen.insert addr
    out := out.push { addr, size := next - addr, name := n }
  return out.toList.mergeSort (·.addr ≤ ·.addr)

/-- The `n` little-endian 32-bit words at virtual address `addr`, from the segment holding them. -/
def wordsAt (img : Elf64Image) (addr n : Nat) : Except String (List (BitVec 32)) := do
  let some seg := img.segments.find? (fun s => s.vaddr ≤ addr && addr + 4 * n ≤ s.vaddr + s.data.size)
    | throw s!"no loaded segment holds [{addr}, {addr + 4 * n})"
  (List.range n).mapM fun i => do
    let off := addr - seg.vaddr + 4 * i
    let w ← Elf.readUIntLE seg.data off 4
    pure (BitVec.ofNat 32 w)

end Tools.Elf
