/-
  Cases.Hardening.Gen.Calls.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Cases.Hardening.Gen.Calls

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [1377555, 32871]
def w1 : List Nat :=
    [4278255891, 1127459, 4280283375, 8466563, 16843027, 4267700335]
def w2 : List Nat :=
    [33882211, 329107, 1049875, 4294280723, 44401971, 394643, 4261812963, 32871, 1049875, 32871]
def w3 : List Nat :=
    [328467, 361747, 196711]
def w4 : List Nat :=
    [5559, 361875, 329235, 361747, 394643, 4263506031]
def w5 : List Nat :=
    [10847539, 14026291, 12911923, 32871]
def w6 : List Nat :=
    [4244701459, 34681891, 42020899, 9518115, 18954275, 20001827, 427027, 394387, 362771, 330131, 4238340335, 54068659, 43255347, 11929011, 10847539, 42020995, 33633283, 25244803, 16857347, 8468867, 50397459, 32871]
def w7 : List Nat :=
    [1377555, 4070568047]
def w8 : List Nat :=
    [111]
def w9 : List Nat :=
    [362083, 45434163, 32871, 4280283375]
def w10 : List Nat :=
    [111]

def words : List (String × Nat × List Nat) := [
  ("inc", 4096, w0),
  ("twice_inc", 4104, w1),
  ("fact", 4128, w2),
  ("apply", 4168, w3),
  ("apply_inc", 4180, w4),
  ("sum4", 4204, w5),
  ("keep", 4220, w6),
  ("tail_inc", 4308, w7),
  ("stop", 4316, w8),
  ("checked_div", 4320, w9),
  ("_start", 4336, w10)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Cases/Hardening/elf/calls.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Cases.Hardening.Gen.Calls
