/-
  Writes the small ELF of `Tools/Test/Elf.lean` to the path given, for `check.sh`.
-/

import Tools.Test.Elf

def main (args : List String) : IO Unit :=
  match args with
  | [path] => IO.FS.writeBinFile path Tools.Test.Elf.elf
  | _ => throw <| IO.userError "usage: WriteElf PATH"
