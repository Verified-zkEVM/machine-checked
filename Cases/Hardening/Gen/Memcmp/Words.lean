/-
  Cases.Hardening.Gen.Memcmp.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Cases.Hardening.Gen.Memcmp

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [33947747, 345731, 378627, 15113827, 1377555, 4294313491, 1410451, 4261811427, 1299, 32871, 1088849203, 32871]
def w1 : List Nat :=
    [111]

def words : List (String × Nat × List Nat) := [
  ("memcmp", 4096, w0),
  ("_start", 4144, w1)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Cases/Hardening/elf/memcmp.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Cases.Hardening.Gen.Memcmp
