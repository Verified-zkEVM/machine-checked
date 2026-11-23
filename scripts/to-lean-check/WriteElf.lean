/-
  Writes the small ELF of `Tools/Test/Elf.lean` to the path given, for `check.sh`; with
  `--start-last`, the same with `_start` the last symbol of `.text` (`startLast`), with
  `--label-past`, with a global label past `.text` (`labelPast`), with `--func-past`, with a
  global function past `.text` (`funcPast`), and with `--unimp`, with `unimp` for the `nop` of
  `_start`, which the `--proved` lift then leaves out.
-/

import Tools.Test.Elf

open Tools.Test.Elf in
def main (args : List String) : IO Unit :=
  match args with
  | [path] => IO.FS.writeBinFile path elf
  | ["--start-last", path] => IO.FS.writeBinFile path startLast
  | ["--label-past", path] => IO.FS.writeBinFile path labelPast
  | ["--func-past", path] => IO.FS.writeBinFile path funcPast
  | ["--unimp", path] => IO.FS.writeBinFile path (bad 0x10c (le 4 0xc0001073))
  | _ => throw <| IO.userError
      "usage: WriteElf [--start-last | --label-past | --func-past | --unimp] PATH"
