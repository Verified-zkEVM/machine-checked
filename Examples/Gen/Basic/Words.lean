/-
  Examples.Gen.Basic.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Gen.Basic

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [10847539, 12911923, 32871]
def w1 : List Nat :=
    [10871907, 361747, 32871]
def w2 : List Nat :=
    [33883747, 4294247827, 4293199379, 46499507, 46511667, 45450675, 11863347, 66459155, 1496723, 13035059, 1086653747, 32871]

def words : List (String × Nat × List Nat) := [
  ("add3", 65536, w0),
  ("max_u64", 65548, w1),
  ("sum_to", 65560, w2)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/basic.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Examples.Gen.Basic
