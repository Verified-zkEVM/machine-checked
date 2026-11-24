/-
  Writes the small ELF of `Tools/Test/Elf.lean` to the path given, for `check.sh`; with
  `--start-last`, the same with `_start` the last symbol of `.text` (`startLast`), and with
  `--label-past`, with a global label past `.text` (`labelPast`), and with `--func-past`, with
  a global function past `.text` (`funcPast`).
-/

import Tools.Test.Elf

open Tools.Test.Elf in
def main (args : List String) : IO Unit :=
  match args with
  | [path] => IO.FS.writeBinFile path elf
  | ["--start-last", path] => IO.FS.writeBinFile path startLast
  | ["--label-past", path] => IO.FS.writeBinFile path labelPast
  | ["--func-past", path] => IO.FS.writeBinFile path funcPast
  | _ => throw <| IO.userError "usage: WriteElf [--start-last | --label-past | --func-past] PATH"
