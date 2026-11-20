/-
  Examples.Limbs.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Limbs.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [1811, 33984099, 3577491, 13960883, 374659, 407555, 8783379, 15173427, 16201651, 17238067, 15218483, 17117219, 8717587, 15198003, 8750483, 4241824483, 460051, 32871]

def words : List (String × Nat × List Nat) := [
  ("add_limbs", 65536, w0)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/limbs.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Examples.Limbs.RiscV.Image
