/-
  Examples.Mem.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Mem.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [396899, 12912179, 378499, 13959203, 1377555, 1410451, 4274329827, 32871]
def w1 : List Nat :=
    [329363, 1049875, 33947747, 444163, 378755, 16194659, 4294313491, 1410451, 1476243, 4261811427, 32871, 1299, 32871]

def words : List (String × Nat × List Nat) := [
  ("copy_bytes", 65536, w0),
  ("equal_bytes", 65568, w1)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/mem.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := (ws.map (BitVec.ofNat 32)).map decode }

end

end Examples.Mem.RiscV.Image
