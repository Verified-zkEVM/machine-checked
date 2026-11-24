/-
  Examples.Widths.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.KernelEq
import Tools.ElfWords

namespace Examples.Widths.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [395875, 12912179, 11862051, 1377555, 4274330851, 32871]
def w1 : List Nat :=
    [396899, 12912179, 378499, 13959203, 1377555, 1410451, 4274329827, 32871]
def w2 : List Nat :=
    [1427, 11863603, 411139, 1410451, 4261812963, 4294280467, 32871]
def w3 : List Nat :=
    [328963, 32871]
def w4 : List Nat :=
    [345347, 32871]
def w5 : List Nat :=
    [333059, 32871]
def w6 : List Nat :=
    [349443, 32871]
def w7 : List Nat :=
    [337155, 32871]
def w8 : List Nat :=
    [353539, 32871]
def w9 : List Nat :=
    [11862051, 11866403, 11870755, 11875363, 32871]
def w10 : List Nat :=
    [1394051, 345603, 2442883, 3491075, 8754579, 12969395, 17208979, 25498907, 10937651, 10872115, 32871]
def w11 : List Nat :=
    [374275, 341635, 12922915, 14004259, 32871]
def w12 : List Nat :=
    [111]

def words : List (String × Nat × List Nat) := [
  ("set_bytes", 4096, w0),
  ("copy_bytes", 4120, w1),
  ("str_len", 4152, w2),
  ("load_s8", 4180, w3),
  ("load_u8", 4188, w4),
  ("load_s16", 4196, w5),
  ("load_u16", 4204, w6),
  ("load_s32", 4212, w7),
  ("load_u32", 4220, w8),
  ("store_widths", 4228, w9),
  ("read_le32", 4248, w10),
  ("swap", 4292, w11),
  ("_start", 4312, w12)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/widths.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := (ws.map (BitVec.ofNat 32)).map decode }

end

end Examples.Widths.RiscV.Image
