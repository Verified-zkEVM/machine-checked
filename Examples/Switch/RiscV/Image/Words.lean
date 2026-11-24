/-
  Examples.Switch.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.KernelEq
import Tools.ElfWords

namespace Examples.Switch.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [8730003, 11535891, 46466355, 10814739, 4294280595, 10872115, 32871]
def w1 : List Nat :=
    [111]

def words : List (String × Nat × List Nat) := [
  ("classify", 4096, w0),
  ("_start", 4124, w1)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/switch.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := (ws.map (BitVec.ofNat 32)).map decode }

end

end Examples.Switch.RiscV.Image
