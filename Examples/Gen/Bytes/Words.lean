/-
  Examples.Gen.Bytes.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Gen.Bytes

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [1427, 11863603, 411139, 1410451, 4261812963, 4294280467, 32871]
def w1 : List Nat :=
    [363107, 11863475, 12910627, 1377555, 4273282275, 32871]
def w2 : List Nat :=
    [1427, 330339, 1406483, 1398035, 12944819, 4261747427, 361747, 32871]

def words : List (String × Nat × List Nat) := [
  ("str_len", 65536, w0),
  ("fill", 65564, w1),
  ("count_ones", 65588, w2)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/bytes.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Examples.Gen.Bytes
