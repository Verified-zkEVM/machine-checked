/-
  Cases.Hardening.Gen.Arith.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Cases.Hardening.Gen.Arith

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [362083, 45434163, 32871, 1299, 32871]
def w1 : List Nat :=
    [361571, 45442355, 32871]
def w2 : List Nat :=
    [362083, 45438259, 32871, 1299, 32871]
def w3 : List Nat :=
    [44414259, 32871]
def w4 : List Nat :=
    [44406067, 32871]
def w5 : List Nat :=
    [11867699, 1085277619, 11883827, 10904883, 32871]
def w6 : List Nat :=
    [1427, 330339, 4294247955, 10908979, 1410451, 4261747427, 361747, 32871]
def w7 : List Nat :=
    [1140151699, 11879731, 1085605171, 32871]
def w8 : List Nat :=
    [111]

def words : List (String × Nat × List Nat) := [
  ("sdiv", 4096, w0),
  ("srem", 4116, w1),
  ("udiv", 4128, w2),
  ("mulhi", 4148, w3),
  ("smulhi", 4156, w4),
  ("rotl", 4188, w5),
  ("popcount", 4208, w6),
  ("abs_branchless", 4240, w7),
  ("_start", 4276, w8)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Cases/Hardening/elf/arith.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Cases.Hardening.Gen.Arith
