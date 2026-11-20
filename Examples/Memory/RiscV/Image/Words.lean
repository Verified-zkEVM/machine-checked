/-
  Examples.Memory.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Memory.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [374275, 341635, 12922915, 14004259, 32871]
def w1 : List Nat :=
    [33916003, 329235, 1299, 3511699, 11929011, 407171, 8783379, 10913075, 4273347299, 32871, 1299, 32871]
def w2 : List Nat :=
    [10871907, 361747, 32871]
def w3 : List Nat :=
    [4278255891, 1127459, 8466467, 394259, 151, 4265640167, 263571, 8466563, 78851, 16843027, 791, 4240638055]

def words : List (String × Nat × List Nat) := [
  ("swap", 65536, w0),
  ("sum_array", 65556, w1),
  ("max2", 65604, w2),
  ("max3", 65616, w3)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/memory.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Examples.Memory.RiscV.Image
