/-
  Tools.Test.Elf

  Tests of the ELF reading the decompiler does on untrusted files, run when the module is
  built: riscv-zkvm's reader `parseElf64`, which gives the segments, and `Tools.Elf`, which
  gives the functions (`symbols`, `functionsOf`, `parseNm`) and the words of code (`wordsAt`).

  A small ELF64 executable is written byte by byte below, from the ELF specification: a
  header, one `PT_LOAD` segment of code with a `.bss` tail, and a symbol table with symbols of
  every kind the reader must keep or leave out. Then it is broken in each way a file can be:
  cut short, wrong magic, 32-bit, big-endian, relocatable, offsets and counts past the end.
  Every broken file must give an error, never a panic or a loop: a `#guard` that evaluates is
  the test.
-/

import Tools.Elf

namespace Tools.Test.Elf

open RiscvZkvm.Interpreter Tools.Elf

/-! ## A file, by hand -/

/-- `v` in `n` bytes, little-endian. -/
def le (n v : Nat) : List Nat := (List.range n).map fun i => (v >>> (8 * i)) % 256

/-- `bs` with `xs` written at `off`. -/
def put (bs : List Nat) (off : Nat) (xs : List Nat) : List Nat :=
  bs.take off ++ xs ++ bs.drop (off + xs.length)

def bytesOf (l : List Nat) : ByteArray := ⟨(l.map UInt8.ofNat).toArray⟩

/-- The ELF header: 64-bit, little-endian, an executable for RISC-V (243), entry 0x10000,
    one program header at 0x40, five section headers at 0x240, names in section 4. -/
def ehdr : List Nat :=
  [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    le 2 2 ++ le 2 243 ++ le 4 1 ++ le 8 0x10000 ++ le 8 0x40 ++ le 8 0x240 ++ le 4 0 ++
    le 2 64 ++ le 2 56 ++ le 2 1 ++ le 2 64 ++ le 2 5 ++ le 2 4

/-- A `PT_LOAD`, readable and executable: 16 bytes of the file at 0x100 at address 0x10000,
    32 bytes in memory. -/
def phdr : List Nat :=
  le 4 1 ++ le 4 5 ++ le 8 0x100 ++ le 8 0x10000 ++ le 8 0x10000 ++ le 8 16 ++ le 8 32 ++ le 8 0x1000

/-- The code: `li a0, 5`, `add a0, a0, a0`, `ret`, `nop`. -/
def code : List Nat := le 4 0x00500513 ++ le 4 0x00a50533 ++ le 4 0x00008067 ++ le 4 0x00000013

/-- A symbol: name offset, `st_info` (binding × 16 + type), section, value, size. -/
def sym (name info shndx value size : Nat) : List Nat :=
  le 4 name ++ [info, 0] ++ le 2 shndx ++ le 8 value ++ le 8 size

/-- The names, at the offsets the symbols give. -/
def strtab : List Nat := "\x00main\x00helper\x00_start\x00zz\x00.Lx\x00obj\x00ext\x00absf\x00dfun\x00".toUTF8.toList.map (·.toNat)

/-- Ten symbols, at 0x110. -/
def symtab : List Nat :=
  sym 0 0 0 0 0 ++                   -- the null symbol
  sym 1 0x12 1 0x10000 8 ++          -- main: global function in .text
  sym 6 0x02 1 0x10008 4 ++          -- helper: local function
  sym 13 0x10 1 0x1000c 0 ++         -- _start: global, untyped, no size
  sym 20 0x00 1 0x10010 0 ++         -- zz: local, untyped, no size, at the end of .text: no code
  sym 23 0x00 1 0x10004 4 ++         -- .Lx: a local label
  sym 27 0x11 1 0x10000 8 ++         -- obj: an object
  sym 31 0x12 0 0 0 ++               -- ext: undefined
  sym 35 0x12 0xfff1 0x10000 4 ++    -- absf: absolute
  sym 40 0x12 2 0x20000 4            -- dfun: in a section that is not code

/-- A section header: type, flags, address, offset, size, link, entry size. -/
def shdr (type flags addr off size link entsize : Nat) : List Nat :=
  le 4 0 ++ le 4 type ++ le 8 flags ++ le 8 addr ++ le 8 off ++ le 8 size ++ le 4 link ++ le 4 0 ++
    le 8 0 ++ le 8 entsize

/-- Null, `.text` (allocated, executable), `.data` (writable), `.symtab` (its names in 4),
    `.strtab`. -/
def shdrs : List Nat :=
  shdr 0 0 0 0 0 0 0 ++
  shdr 1 6 0x10000 0x100 16 0 0 ++
  shdr 1 3 0x20000 0x110 0 0 0 ++
  shdr 2 0 0 0x110 240 4 24 ++
  shdr 3 0 0 0x200 strtab.length 0 0

/-- The file, as a list of bytes. -/
def good : List Nat :=
  let z := List.replicate 0x380 0
  let z := put z 0 ehdr
  let z := put z 0x40 phdr
  let z := put z 0x100 code
  let z := put z 0x110 symtab
  let z := put z 0x200 strtab
  put z 0x240 shdrs

def elf : ByteArray := bytesOf good

/-- The file with `xs` written at `off`. -/
def bad (off : Nat) (xs : List Nat) : ByteArray := bytesOf (put good off xs)

/-- The first `n` bytes of the file. -/
def cut (n : Nat) : ByteArray := bytesOf (good.take n)

/-- The file with `zz` global and past `.text`, where a linker puts `_end`. -/
def labelPast : ByteArray :=
  bytesOf (put (put good (0x110 + 4 * 24 + 4) [0x10]) (0x110 + 4 * 24 + 8) (le 8 0x11000))

/-- The file with `zz` a global function past `.text`. -/
def funcPast : ByteArray :=
  bytesOf (put (put good (0x110 + 4 * 24 + 4) [0x12]) (0x110 + 4 * 24 + 8) (le 8 0x11000))

/-- The file with `zz` at 0x10000, so that `_start` is the last symbol of `.text`. -/
def startLast : ByteArray := bad (0x110 + 4 * 24 + 8) (le 8 0x10000)

def isErr {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

/-- The functions of a file, as address, size and name. -/
def syms (bs : ByteArray) : Option (List (Nat × Nat × String)) :=
  match symbols bs with
  | .ok r => some (r.fns.map fun s => (s.addr, s.size, s.name))
  | .error _ => none

/-- The symbols of code of a file whose code no function holds, with the reasons. -/
def lost (bs : ByteArray) : Option (List String) := (symbols bs).toOption.map (·.lost)

/-- The other names of code of a file that a function holds, with the reasons. -/
def names (bs : ByteArray) : Option (List String) := (symbols bs).toOption.map (·.names)

/-- The segments of a file, as address, file bytes, size in memory, writable, executable. -/
def segs (bs : ByteArray) : Option (List (Nat × List UInt8 × Nat × Bool × Bool)) :=
  match parseElf64 bs with
  | .ok img => some (img.segments.toList.map fun s => (s.vaddr, s.data.toList, s.memsz, s.writable, s.executable))
  | .error _ => none

/-! ## The file is read as its bytes say -/

-- the layout is as planned: 0x380 bytes, the parts where they belong
#guard good.length == 0x380 && ehdr.length == 64 && phdr.length == 56 && symtab.length == 240 &&
  shdrs.length == 320 && strtab.length == 45
-- the entry
#guard (parseElf64 elf).toOption.map (·.entry) == some 0x10000
-- one segment: the code's 16 bytes at 0x10000, 32 in memory, executable, not writable
#guard segs elf == some [(0x10000, (code.map UInt8.ofNat), 32, false, true)]
-- no `.tohost`
#guard (parseElf64 elf).toOption.map (·.tohost) == some none
-- a writable segment that is not executable (`p_flags` = RW)
#guard segs (bad 0x44 (le 4 6)) == some [(0x10000, (code.map UInt8.ofNat), 32, true, false)]
-- a segment that is not `PT_LOAD` (a `PT_NOTE`) is not loaded
#guard segs (bad 0x40 (le 4 4)) == some []
-- a segment with no bytes in the file: all `.bss`
#guard segs (bad 0x60 (le 8 0)) == some [(0x10000, [], 32, false, true)]

/-! ## Words of code -/

-- the four words at 0x10000, little-endian
#guard ((parseElf64 elf).toOption.map fun img => (wordsAt img 0x10000 4).toOption) ==
  some (some [0x00500513, 0x00a50533, 0x00008067, 0x00000013])
-- the last word
#guard ((parseElf64 elf).toOption.map fun img => (wordsAt img 0x1000c 1).toOption) ==
  some (some [0x00000013])
-- none
#guard ((parseElf64 elf).toOption.map fun img => (wordsAt img 0x10000 0).toOption) == some (some [])
-- past the file bytes of the segment (into `.bss`): an error
#guard ((parseElf64 elf).toOption.map fun img => isErr (wordsAt img 0x10010 1)) == some true
-- across the end of the segment: an error
#guard ((parseElf64 elf).toOption.map fun img => isErr (wordsAt img 0x1000c 2)) == some true
-- below the segment: an error
#guard ((parseElf64 elf).toOption.map fun img => isErr (wordsAt img 0xfffc 1)) == some true

/-! ## Symbols -/

-- the functions: main and helper as sized; _start, global with no size, up to the end of
-- .text; no label, object, undefined or absolute symbol, nor one outside code; zz, at the end
-- of .text, is no code, so it is not reported either
#guard syms elf == some [(0x10000, 8, "main"), (0x10008, 4, "helper"), (0x1000c, 4, "_start")]
#guard lost elf == some [] && names elf == some []
-- zz global and past .text, as a linker puts `_end`: still no code
#guard syms labelPast == syms elf && lost labelPast == some [] && names labelPast == some []
-- zz a function past .text: not taken, and lost
#guard syms funcPast == syms elf && lost funcPast == some ["zz: outside its section"]
-- zz at 0x10000: _start, global with no size, is the last symbol and extends to the end of
-- .text; zz, a local label without a size inside `main`, is a name, and no code is lost
#guard syms startLast == syms elf && lost startLast == some [] &&
  names startLast == some ["zz: a local label without a size"]
-- a symbol table with no symbols but the null one
#guard syms (bad (0x240 + 3 * 64 + 0x20) (le 8 24)) == some []
-- no section headers
#guard syms (bad 0x3c (le 2 0)) == some []
-- an entry size of 0 for section headers: every header is the null one
#guard syms (bad 0x3a (le 2 0)) == some []
-- a name with no NUL before the end of the file: an error (main's name is the last four
-- bytes, where the strings now start)
#guard syms (bytesOf (put (put (put good (0x240 + 4 * 64 + 0x18) (le 8 0x37c)) (0x110 + 24) (le 4 0))
  0x37c [0x61, 0x62, 0x63, 0x64])) == none

/-! ## Files cut short -/

-- empty
#guard isErr (parseElf64 (cut 0)) && syms (cut 0) == none
-- inside the ELF header
#guard isErr (parseElf64 (cut 16)) && isErr (parseElf64 (cut 63))
-- the header alone: the program header is past the end
#guard isErr (parseElf64 (cut 64))
-- inside the program header
#guard isErr (parseElf64 (cut 0x60))
-- inside the segment's bytes
#guard isErr (parseElf64 (cut 0x108))
-- inside the symbol table, the strings and the section headers: no symbols, but no crash
#guard syms (cut 0x120) == none && syms (cut 0x210) == none && syms (cut 0x300) == none

/-! ## Files that are not what the decompiler takes -/

-- wrong magic
#guard isErr (parseElf64 (bad 0 [0x7f, 0x45, 0x4c, 0x47]))
#guard isErr (parseElf64 (bad 0 [0, 0, 0, 0]))
-- ELFCLASS32
#guard isErr (parseElf64 (bad 4 [1]))
-- big-endian (ELFDATA2MSB)
#guard isErr (parseElf64 (bad 5 [2]))
-- relocatable (ET_REL), shared (ET_DYN), core
#guard isErr (parseElf64 (bad 0x10 (le 2 1))) && isErr (parseElf64 (bad 0x10 (le 2 3))) &&
  isErr (parseElf64 (bad 0x10 (le 2 4)))
-- for another machine (x86-64)
#guard isErr (parseElf64 (bad 0x12 (le 2 62)))
-- a size in memory less than in the file
#guard isErr (parseElf64 (bad 0x68 (le 8 8)))

/-! ## Offsets and counts past the end -/

-- the program headers' offset past the end, and at the greatest offset
#guard isErr (parseElf64 (bad 0x20 (le 8 0x10000))) && isErr (parseElf64 (bad 0x20 (le 8 (2 ^ 64 - 1))))
-- a segment's offset past the end
#guard isErr (parseElf64 (bad 0x48 (le 8 (2 ^ 64 - 1))))
-- a segment's size in the file past the end
#guard isErr (parseElf64 (bad 0x60 (le 8 (2 ^ 63))))
-- the greatest number of program headers, each read from the file: past the end
#guard isErr (parseElf64 (bad 0x38 (le 2 0xffff)))
-- the greatest number of program headers, all at one place (entry size 0): read, and ends
#guard (segs (bad 0x36 (le 2 0 ++ le 2 0xffff))).map List.length == some 0xffff
-- the section headers' offset past the end
#guard isErr (parseElf64 (bad 0x28 (le 8 0x10000))) && syms (bad 0x28 (le 8 0x10000)) == none
#guard syms (bad 0x28 (le 8 (2 ^ 64 - 1))) == none
-- the greatest number of section headers: past the end
#guard isErr (parseElf64 (bad 0x3c (le 2 0xffff))) && syms (bad 0x3c (le 2 0xffff)) == none
-- the names' section (`e_shstrndx`) out of range: not read
#guard (parseElf64 (bad 0x3e (le 2 0xffff))).toOption.map (·.entry) == some 0x10000
-- the symbol table's offset past the end
#guard syms (bad (0x240 + 3 * 64 + 0x18) (le 8 0x10000)) == none
-- the symbol table's size far past the end: read up to the end, then an error
#guard syms (bad (0x240 + 3 * 64 + 0x20) (le 8 (2 ^ 62))) == none
-- the symbol table's link to a section that does not exist
#guard syms (bad (0x240 + 3 * 64 + 0x28) (le 4 0xffffffff)) == none
-- the strings' offset past the end
#guard syms (bad (0x240 + 4 * 64 + 0x18) (le 8 (2 ^ 40))) == none
-- a symbol's name offset past the end
#guard syms (bad (0x110 + 24 + 0) (le 4 0xffffffff)) == none
-- a symbol's section out of range: left out
#guard syms (bad (0x110 + 24 + 6) (le 2 0xfff0)) == some [(0x10008, 4, "helper"), (0x1000c, 4, "_start")]

/-! ## Symbols from `llvm-nm -S` and the rules that make functions of them -/

-- sized text symbols, a global one without a size up to the next, a label left out, data left out
#guard (parseNm ("0000000000010000 0000000000000008 T main\n0000000000010008 0000000000000004 t helper\n" ++
    "000000000001000c 0000000000000000 T _start\n0000000000010010 0000000000000000 t zz\n" ++
    "0000000000010004 0000000000000004 t .Lx\n0000000000020000 0000000000000008 D obj\n")).map
    (fun s => (s.addr, s.size, s.name)) ==
  [(0x10000, 8, "main"), (0x10008, 4, "helper"), (0x1000c, 4, "_start")]
-- lines that are not four fields, or with numbers that are not lowercase hexadecimal
#guard (parseNm "garbage\n0000000000010000 T main\n0001000G 0008 T f\n00010000 0008 T g h\n\n").isEmpty
#guard (parseNm "0000ABCD 0008 T f\n").isEmpty
-- two symbols at one address: the first sized one; the other is a name, no code lost
#guard (functionsOf [(0x100, 8, true, "a"), (0x100, 16, true, "b")]).fns.map (·.name) == ["a"]
#guard (functionsOf [(0x100, 8, true, "a"), (0x100, 16, true, "b")]).names ==
  ["b: at 0x100, the address of `a`, taken under that name"]
#guard (functionsOf [(0x100, 8, true, "a"), (0x100, 16, true, "b")]).lost == []
-- a global symbol without a size at a sized one's address: a name
#guard (functionsOf [(0x100, 0, true, "a"), (0x100, 8, true, "b")]).names ==
  ["a: at 0x100, the address of `b`, taken under that name"]
-- a global symbol without a size and nothing after it: lost, or up to the end of its section
#guard (functionsOf [(0x100, 0, true, "a")]).fns.isEmpty
#guard (functionsOf [(0x100, 0, true, "a")]).lost ==
  ["a: no size, and no symbol or end of section after it"]
#guard (functionsOf [(0x100, 0, true, "a")] [0x140]).fns.map (fun s => (s.addr, s.size)) ==
  [(0x100, 0x40)]
-- a local symbol without a size where no function is: lost
#guard (functionsOf [(0x100, 0, false, "a"), (0x200, 4, false, "b")]).fns.map (·.name) == ["b"]
#guard (functionsOf [(0x100, 0, false, "a"), (0x200, 4, false, "b")]).lost ==
  ["a: a local label without a size"]
-- a local symbol without a size inside a function: a name, no code lost
#guard (functionsOf [(0x200, 8, false, "b"), (0x204, 0, false, "l")]).names ==
  ["l: a local label without a size"]
#guard (functionsOf [(0x200, 8, false, "b"), (0x204, 0, false, "l")]).lost == []
-- sorted by address
#guard (functionsOf [(0x300, 4, true, "c"), (0x100, 4, true, "a"), (0x200, 4, true, "b")]).fns.map
  (·.name) == ["a", "b", "c"]
-- hexadecimal numerals
#guard parseHex? "ff" == some 255 && parseHex? "0" == some 0 && parseHex? "" == none &&
  parseHex? "FF" == none && parseHex? "0x10" == none && parseHex? "-1" == none
#guard hex 255 4 == "00ff" && hex 0x12345 2 == "12345" && hex 0 1 == "0"

end Tools.Test.Elf
