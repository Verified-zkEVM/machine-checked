/-
  Tools.Program

  An ELF as the input of the lift of whole programs: what `decompile` reads from it, as plain
  data (`Input`: each function's name, address, bytes and the addresses inside it a computed
  jump may reach; the entry; the memory), and the program each instruction set builds from that
  data (`riscvProgram`, `armProgram`, `x86Program`).

  The tool decompiles through these, and `decompile --to lean` writes the data into a module
  and the program as the builder applied to it, so that the program the kernel checks a term
  against is the one the tool lifted. Nothing here is proved.

  The program's structures are reducible by the kernel (`Std.TreeMap`, not `Std.HashMap`, in the
  lifts): a module written by `decompile --to lean` decides its terms by evaluating the lift.

  ## Main definitions

  * `Machine`, `Entry`, `Input`, `inputOf`
  * `riscvProgram`, `armProgram`, `x86Program`
-/

import RiscvZkvm.Interpreter
import MachineChecked.RiscV.Lift.Whole
import MachineChecked.RiscV.Sp1.Pancake
import MachineChecked.ARM.Bare
import MachineChecked.X86.Bare
import Tools.Elf
import Std.Data.HashMap
import Std.Data.HashSet

namespace Tools.Program

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter
open Lprog MachineChecked.RiscV.Lift Lprog.RiscV
open Tools.Elf
open Lprog.Linked (At)

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


/-! ## The input, as data -/

/-- The instruction sets the lift of whole programs takes. -/
inductive Machine where
  | riscv | arm | x86
  deriving DecidableEq, Repr

/-- One function: its name, its address, its bytes, and the addresses inside it, other than
    its entry, that a computed jump may reach (`Linked.Fun.targets`). -/
abbrev Entry := String × Nat × List Nat × List Nat

/-- **What `decompile` reads from an ELF**, as plain data. -/
structure Input where
  machine : Machine
  code : List Entry
  entry : Nat
  /-- The words the program loads, by address, as `memoryOf` gives them. -/
  memory : List (Nat × Nat)
  /-- The symbols left out, each with the reason. -/
  skipped : Array String

/-- The bytes of a list of naturals, each taken modulo 256. -/
def bytesOf (l : List Nat) : ByteArray := ⟨(l.map UInt8.ofNat).toArray⟩

/-- The code of an ELF as bytes: for each sized text symbol inside an executable segment, at
    an address that is a multiple of `align`, its name, address and bytes. The symbols left
    out, each with the reason. -/
def partsOf (bytes : ByteArray) (align : Nat) :
    Except String (Elf64Image × Array (String × Nat × ByteArray) × Array String) := do
  let img ← parseElf64 ((bytes.set! 0x12 243).set! 0x13 0)
  let mut parts : Array (String × Nat × ByteArray) := #[]
  let mut skipped : Array String := #[]
  for sym in ← symbols bytes do
    if sym.addr % align != 0 || sym.size % align != 0 then
      skipped := skipped.push s!"{sym.name}: not word-aligned"
    else match img.segments.find? (fun s => s.executable && s.vaddr ≤ sym.addr &&
        sym.addr + sym.size ≤ s.vaddr + s.data.size) with
      | none => skipped := skipped.push s!"{sym.name}: not in an executable segment"
      | some seg =>
        let bs := seg.data.extract (sym.addr - seg.vaddr) (sym.addr - seg.vaddr + sym.size)
        if bs.size > 0 then parts := parts.push (sym.name, sym.addr, bs)
  return (img, parts, skipped)

/-- A function of the program from its entry, by `decode`. -/
def funOf {I : Type} (decode : ByteArray → Nat → Array (At I)) : Entry → Linked.Fun I
  | (name, addr, bs, ts) =>
    { name, code := (decode (bytesOf bs) addr).toList, targets := ts.map (BitVec.ofNat 64) }

/-- The program of RISC-V code (an SP1 guest). -/
def riscvProgram (code : List Entry) (entry : Nat) (memory : List (Nat × Nat)) :
    MachineChecked.RiscV.Sp1.Guest :=
  { fns := code.map (funOf (words decodeWord)), entry := BitVec.ofNat 64 entry
    memory := memory.map fun (a, w) => (BitVec.ofNat 64 a, BitVec.ofNat 64 w) }

/-- The program of AArch64 code (a bare guest). -/
def armProgram (code : List Entry) (entry : Nat) (memory : List (Nat × Nat)) :
    MachineChecked.ARM.Guest :=
  { fns := code.map (funOf (words Arm64.decode)), entry := BitVec.ofNat 64 entry
    memory := memory.map fun (a, w) => (BitVec.ofNat 64 a, BitVec.ofNat 64 w) }

/-- The program of x86-64 code (a bare guest). -/
def x86Program (code : List Entry) (entry : Nat) (memory : List (Nat × Nat)) :
    MachineChecked.X86.Guest :=
  { fns := code.map (funOf x86Code), entry := BitVec.ofNat 64 entry
    memory := memory.map fun (a, w) => (BitVec.ofNat 64 a, BitVec.ofNat 64 w) }

/-- The entries of a program from its code as bytes, decoded by `decode`, and the addresses
    of code it holds as values (`held`, as `fnsOf` takes them). -/
def entriesOf {I : Type} (decode : ByteArray → Nat → Array (At I))
    (parts : Array (String × Nat × ByteArray)) (held : Array (String × Array (At I)) → Array Nat) :
    List Entry :=
  let decoded := parts.map fun (n, a, bs) => (n, decode bs a)
  let fns := fnsOf decoded (held decoded)
  (parts.toList.zip fns).map fun ((n, a, bs), f) =>
    (n, a, bs.toList.map (·.toNat), f.targets.map (·.toNat))

/-- **The input of an ELF**, as `decompile` reads it. -/
def inputOf (bytes : ByteArray) : Except String Input := do
  let machine ← machineOf bytes
  let align := if machine == 62 then 1 else 4
  let (img, parts, skipped) ← partsOf bytes align
  if parts.isEmpty then throw "the ELF has no function symbols (a stripped binary is not supported)"
  let (w4, w8) := dataWords img
  let (m, code) : Machine × List Entry :=
    if machine == 62 then (.x86, entriesOf x86Code parts fun ps => w8 ++ formedX86 ps w4)
    else if machine == 243 then (.riscv, entriesOf (words decodeWord) parts fun ps => w4 ++ w8 ++ formedRiscV ps)
    else (.arm, entriesOf (words Arm64.decode) parts fun ps => w8 ++ tablesArm ps w4)
  return { machine := m, code, entry := img.entry
           memory := (memoryOf img).map fun (a, w) => (a.toNat, w.toNat), skipped }

end Tools.Program
