/-
  Examples.Rec.RiscV.Image.Words

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Tools.ToLean

namespace Examples.Rec.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def w0 : List Nat :=
    [4261478675, 1129507, 8468515, 9516067, 18952227, 2098579, 328723, 1171, 11890275, 1050899, 4294182163, 4250923247, 4293133331, 9766067, 4270418147, 9700659, 25243779, 16856067, 8467587, 80131, 33620243, 32871]
def w1 : List Nat :=
    [111]

def words : List (String × Nat × List Nat) := [
  ("fib", 4096, w0),
  ("_start", 4184, w1)]

-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/rec.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := (ws.map (BitVec.ofNat 32)).map decode }

end

end Examples.Rec.RiscV.Image
