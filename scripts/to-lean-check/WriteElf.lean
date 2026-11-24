/-
  Writes the small ELF of `Tools/Test/Elf.lean` to the path given, for `check.sh`; with
  `--start-last`, the same with `_start` the last symbol of `.text` (`startLast`), with
  `--label-past`, with a global label past `.text` (`labelPast`), with `--func-past`, with a
  global function past `.text` (`funcPast`), and with `--addw`, with `addw a0, a0, a0` for the
  last word of `_start`, a 32-bit operation the `--proved` lift leaves out.
-/

import Tools.Test.Elf

open Tools.Test.Elf in
def main (args : List String) : IO Unit :=
  match args with
  | [path] => IO.FS.writeBinFile path elf
  | ["--start-last", path] => IO.FS.writeBinFile path startLast
  | ["--label-past", path] => IO.FS.writeBinFile path labelPast
  | ["--func-past", path] => IO.FS.writeBinFile path funcPast
  | ["--addw", path] => IO.FS.writeBinFile path (bad 0x10c (le 4 0x00a5053b))
  | _ => throw <| IO.userError
      "usage: WriteElf [--start-last | --label-past | --func-past | --addw] PATH"
