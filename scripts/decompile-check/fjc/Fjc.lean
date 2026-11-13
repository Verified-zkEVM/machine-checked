/-
  fjc SOURCE.pnk: compile Pancake source with Flapjack's verified RISC-V compiler
  (`RiscV.NativeSource.compile`) and print the image in flapjack-flip's text form.
  The computation of flapjack-flip's `FlapjackFlip.compile`, without running the result.
-/
import Flapjack.RiscV.NativeSource

open Flapjack

def hexOf (width n : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i => Nat.digitChar (n / 16 ^ i % 16))

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: fjc SOURCE.pnk"; return 2
  match RiscV.NativeSource.compile (← IO.FS.readFile path) with
  | .error e => IO.eprintln s!"fjc: {sourceRiscVImageErrorDescription e}"; return 1
  | .ok out =>
    match out.artifact with
    | none => IO.eprintln "fjc: native backend compilation failed"; return 1
    | some (bytes, bitmaps, config) =>
      let names := config.labConf.ffiNames.getD []
      if names.any (fun | .sharedMem _ => true | .extCall _ => false) then
        IO.eprintln "fjc: shared-memory operations are not supported"; return 1
      let ffi := (Compiler.Backend.Backend.ffinamesToStringList names).map
        Basis.Pure.MlString.toStringOfBytes
      IO.println "flapjack-flip image v1"
      for n in ffi do IO.println s!"ffi {n}"
      IO.println ("bitmaps " ++ " ".intercalate (bitmaps.map (hexOf 16 ·.toNat)))
      IO.println ("code " ++ " ".intercalate (bytes.map (hexOf 2 ·.toNat)))
      return 0
