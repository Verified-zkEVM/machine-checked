/-
  Examples.Branches.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Branches.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [10847539, 12911923, 32871]
def w1 : List Nat :=
    [10863715, 361747, 32871]
def w2 : List Nat :=
    [10871907, 361747, 32871]
def w3 : List Nat :=
    [329363, 12933219, 11885155, 361747, 32871, 394899, 4273294051, 427283, 32871]
def w4 : List Nat :=
    [33916003, 329235, 1299, 3511699, 11929011, 407171, 8783379, 10913075, 4273347299, 32871, 1299, 32871]
def w5 : List Nat :=
    [168101987, 1398163, 1431655991, 858994359, 252647223, 16844727, 11887923, 1431700883, 859211283, 4042720915, 269977363, 2447251, 16082227, 33920915, 16090547, 33953683, 16123443, 33986451, 16156339, 34019219, 16189235, 4544403, 16082227, 8738707, 16082227, 17127315, 16082227, 33904531, 16082227, 4294264083, 1398675, 12055987, 1085605171, 12940723, 2446611, 12940595, 10847539, 4543891, 11863347, 13989171, 48563507, 59069715, 67110291, 1084589363, 32871]
def w6 : List Nat :=
    [111]

def words : List (String × Nat × List Nat) := [
  ("add3", 4096, w0),
  ("max2", 4108, w1),
  ("umax2", 4120, w2),
  ("clamp", 4132, w3),
  ("sum", 4168, w4),
  ("count_down", 4216, w5),
  ("_start", 4396, w6)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/branches.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := (ws.map (BitVec.ofNat 32)).map decode }

end

end Examples.Branches.RiscV.Image
