/-
  Tools.Fjimg

  The text form of a Flapjack image (`MachineChecked.RiscV.Flapjack.Image`), as flapjack-flip
  writes it: a header line, an `ffi NAME` line for each FFI name in index order, a `bitmaps`
  line of 16-digit words and a `code` line of 2-digit bytes, in lowercase hexadecimal.
-/

import MachineChecked.RiscV.Flapjack.Image
import Tools.Elf

namespace Tools.Fjimg

open MachineChecked.RiscV.Flapjack

def header : String := "flapjack-flip image v1"

/-- An image from its text. -/
def parse (text : String) : Except String Image := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  let some first := lines.head? | throw "empty image"
  unless first == header do throw s!"expected the header '{header}'"
  let mut img : Image := { ffiNames := [], bitmaps := [], code := [] }
  for line in lines.drop 1 do
    match (line.splitOn " ").filter (!·.isEmpty) with
    | ["ffi", name] => img := { img with ffiNames := img.ffiNames ++ [name] }
    | "bitmaps" :: ws =>
      let some vs := ws.mapM Tools.Elf.parseHex? | throw "malformed bitmaps line"
      img := { img with bitmaps := vs.map (BitVec.ofNat 64) }
    | "code" :: bs =>
      let some vs := bs.mapM Tools.Elf.parseHex? | throw "malformed code line"
      img := { img with code := vs.map (BitVec.ofNat 8) }
    | _ => throw s!"unexpected line '{line.take 40}'"
  if img.code.isEmpty then throw "the image has no code"
  return img

end Tools.Fjimg
