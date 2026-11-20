/-
  Examples.RustBasic.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.RustBasic.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [111]
def w1 : List Nat :=
    [10847539, 12911923, 32871]
def w2 : List Nat :=
    [363107, 45446707, 361747, 394643, 4261812963, 32871]
def w3 : List Nat :=
    [10871907, 361747, 32871]
def w4 : List Nat :=
    [33916003, 329235, 1299, 3511699, 407171, 8783379, 4286940563, 10913075, 4261779683, 32871, 1299, 32871]

def words : List (String × Nat × List Nat) := [
  ("_RNvCs1njKG4L9aB3_7___rustc17rust_begin_unwind", 65536, w0),
  ("add3", 65540, w1),
  ("gcd", 65552, w2),
  ("max_u64", 65576, w3),
  ("sum_slice", 65588, w4)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/rustbasic.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }

end

end Examples.RustBasic.RiscV.Image
