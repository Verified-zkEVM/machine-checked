/-
  Examples.Crc32.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Crc32.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [67505251, 4294264467, 12944947, 66871, 96797971, 378627, 1410451, 15124147, 16185107, 2561811, 15009587, 468739, 4642459, 15124147, 16185107, 2561811, 15009587, 468739, 4642459, 15124147, 4240806627, 4294362387, 32871]

def words : List (String × Nat × List Nat) := [
  ("crc32", 65536, w0)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/crc32.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := (ws.map (BitVec.ofNat 32)).map decode }

end

end Examples.Crc32.RiscV.Image
